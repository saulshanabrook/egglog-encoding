"""Finite, typed combinational circuits at the Churchroad/slotted boundary."""

from dataclasses import dataclass
from functools import cached_property


@dataclass(frozen=True)
class Expr:
    op: str
    width: int
    args: tuple["Expr", ...] = ()
    data: tuple = ()

    @cached_property
    def height(self):
        return 0 if not self.args else 1 + max(a.height for a in self.args)

    @cached_property
    def size(self):
        return 1 + sum(a.size for a in self.args)


def operation(op, args=(), data=()):
    """Validate widths before a circuit enters the untyped slotted carrier."""
    args, data = tuple(args), tuple(data)
    if op in {"Input", "BV"}:
        value, width = data
        if width <= 0:
            raise ValueError(f"{op}: width must be positive")
        if op == "BV":
            value = int(value) % (1 << width)
        return Expr(op, width, (), (value,))
    arities = {
        "And": 2,
        "Or": 2,
        "Xor": 2,
        "Add": 2,
        "Sub": 2,
        "Mul": 2,
        "Eq": 2,
        "Ne": 2,
        "Shr": 2,
        "Shl": 2,
        "Concat": 2,
        "Mux": 3,
        "Not": 1,
        "ReduceOr": 1,
        "ReduceAnd": 1,
        "ReduceXor": 1,
        "LogicNot": 1,
        "LogicAnd": 2,
        "LogicOr": 2,
        "Extract": 1,
        "ZeroExtend": 1,
        "SignExtend": 1,
    }
    if op not in arities:
        raise ValueError(f"unsupported combinational Churchroad operator {op!r}")
    if len(args) != arities[op]:
        raise ValueError(f"{op}: expected {arities[op]} children, got {len(args)}")
    parameters = {"Extract": 2, "ZeroExtend": 1, "SignExtend": 1}.get(op, 0)
    if len(data) != parameters:
        raise ValueError(f"{op}: expected {parameters} operator parameters, got {data}")
    width = args[0].width
    if op in {"And", "Or", "Xor", "Add", "Sub", "Mul", "Eq", "Ne"} and args[1].width != width:
        raise ValueError(f"{op}: unequal operand widths {width} and {args[1].width}")
    if op in {"Eq", "Ne", "ReduceOr", "ReduceAnd", "ReduceXor", "LogicNot", "LogicAnd", "LogicOr"}:
        width = 1
    elif op == "Concat":
        width += args[1].width
    elif op == "Mux":
        if width != 1 or args[1].width != args[2].width:
            raise ValueError("Mux: expected a one-bit selector and equal-width branches")
        width = args[1].width
    elif op == "Extract":
        high, low = data
        if not 0 <= low <= high < width:
            raise ValueError(f"Extract: invalid [{high}:{low}] of a {width}-bit value")
        width = high - low + 1
    elif op in {"ZeroExtend", "SignExtend"}:
        (new_width,) = data
        if new_width < width:
            raise ValueError(f"{op}: cannot extend {width} bits to {new_width}")
        width = new_width
    return Expr(op, width, args, data)


@dataclass
class Circuit:
    inputs: dict[str, Expr]
    outputs: dict[str, Expr]

    def nodes(self):
        seen, ordered = set(), []

        def visit(expr):
            if expr in seen:
                return
            seen.add(expr)
            for child in expr.args:
                visit(child)
            ordered.append(expr)

        for expr in self.outputs.values():
            visit(expr)
        return ordered


def evaluate(expr, inputs):
    """Independent bitvector evaluator for small exhaustive adapter tests."""
    op, width = expr.op, expr.width
    args = [evaluate(a, inputs) for a in expr.args]
    mask = (1 << width) - 1
    if op == "Input":
        value = inputs[expr.data[0]]
    elif op == "BV":
        value = expr.data[0]
    elif op in {"And", "Or", "Xor", "Add", "Sub", "Mul", "Eq", "Ne", "Shl", "Shr"}:
        a, b = args
        if op in {"Shl", "Shr"} and b >= width:
            value = 0
        else:
            value = {
                "And": lambda: a & b,
                "Or": lambda: a | b,
                "Xor": lambda: a ^ b,
                "Add": lambda: a + b,
                "Sub": lambda: a - b,
                "Mul": lambda: a * b,
                "Eq": lambda: a == b,
                "Ne": lambda: a != b,
                "Shl": lambda: a << b,
                "Shr": lambda: a >> b,
            }[op]()
    elif op == "Concat":
        value = (args[0] << expr.args[1].width) | args[1]
    elif op == "Mux":
        # Churchroad follows Yosys: selector, false branch, true branch.
        value = args[2] if args[0] else args[1]
    elif op == "Extract":
        value = args[0] >> expr.data[1]
    elif op == "SignExtend":
        value = args[0]
        if value & (1 << (expr.args[0].width - 1)):
            value -= 1 << expr.args[0].width
    elif op == "ZeroExtend":
        value = args[0]
    elif op == "Not":
        value = ~args[0]
    elif op in {"ReduceOr", "LogicNot", "ReduceAnd", "ReduceXor", "LogicAnd", "LogicOr"}:
        value = {
            "ReduceOr": lambda: bool(args[0]),
            "LogicNot": lambda: not args[0],
            "ReduceAnd": lambda: args[0] == (1 << expr.args[0].width) - 1,
            "ReduceXor": lambda: args[0].bit_count() % 2,
            "LogicAnd": lambda: bool(args[0] and args[1]),
            "LogicOr": lambda: bool(args[0] or args[1]),
        }[op]()
    else:
        raise ValueError(f"cannot evaluate {op}")
    return int(value) & mask
