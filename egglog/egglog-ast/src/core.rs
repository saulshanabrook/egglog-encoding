use std::{
    fmt::Display,
    hash::{Hash, Hasher},
    ops::AddAssign,
};

use crate::{
    generic_ast::{Change, GenericExpr, Literal},
    span::Span,
    util::ListDisplay,
};

/// A variable, literal, or global in lowered rule syntax.
#[derive(Debug, Clone)]
pub enum GenericAtomTerm<Leaf, Constant = Literal> {
    Var(Span, Leaf),
    Literal(Span, Constant),
    Global(Span, Leaf),
}

// Source annotations do not affect equality or hashing.
impl<Leaf: PartialEq, Constant: PartialEq> PartialEq for GenericAtomTerm<Leaf, Constant> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Var(_, lhs), Self::Var(_, rhs)) => lhs == rhs,
            (Self::Literal(_, lhs), Self::Literal(_, rhs)) => lhs == rhs,
            (Self::Global(_, lhs), Self::Global(_, rhs)) => lhs == rhs,
            _ => false,
        }
    }
}

impl<Leaf: Eq, Constant: Eq> Eq for GenericAtomTerm<Leaf, Constant> {}

impl<Leaf: Hash, Constant: Hash> Hash for GenericAtomTerm<Leaf, Constant> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::Var(_, value) | Self::Global(_, value) => value.hash(state),
            Self::Literal(_, value) => value.hash(state),
        }
    }
}

impl<Leaf, Constant> GenericAtomTerm<Leaf, Constant> {
    pub fn span(&self) -> &Span {
        match self {
            Self::Var(span, _) | Self::Literal(span, _) | Self::Global(span, _) => span,
        }
    }
}

impl<Leaf: Clone> GenericAtomTerm<Leaf> {
    pub fn to_expr<Head>(&self) -> GenericExpr<Head, Leaf> {
        match self {
            Self::Var(span, value) | Self::Global(span, value) => {
                GenericExpr::Var(span.clone(), value.clone())
            }
            Self::Literal(span, literal) => GenericExpr::Lit(span.clone(), literal.clone()),
        }
    }
}

impl<Constant: Display> Display for GenericAtomTerm<String, Constant> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Var(_, value) | Self::Global(_, value) => write!(f, "{value}"),
            Self::Literal(_, literal) => write!(f, "{literal}"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GenericAtom<Head, Leaf, Constant = Literal> {
    pub span: Span,
    pub head: Head,
    pub args: Vec<GenericAtomTerm<Leaf, Constant>>,
}

impl<Head: Display, Constant: Display> Display for GenericAtom<Head, String, Constant> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} {}) ", self.head, ListDisplay(&self.args, " "))
    }
}

impl<Head, Leaf, Constant> GenericAtom<Head, Leaf, Constant>
where
    Leaf: Clone,
{
    pub fn vars(&self) -> impl Iterator<Item = Leaf> + '_ {
        self.args.iter().filter_map(|term| match term {
            GenericAtomTerm::Var(_, value) => Some(value.clone()),
            GenericAtomTerm::Literal(..) | GenericAtomTerm::Global(..) => None,
        })
    }

    pub fn substitute_with(
        &mut self,
        substitute: &mut impl FnMut(&Leaf) -> Option<GenericAtomTerm<Leaf, Constant>>,
    ) where
        Constant: Clone,
    {
        for argument in &mut self.args {
            if let GenericAtomTerm::Var(_, variable) = argument
                && let Some(replacement) = substitute(variable)
            {
                *argument = replacement;
            }
        }
    }
}

impl<Head: Clone, Leaf: Clone> GenericAtom<Head, Leaf> {
    pub fn to_expr(&self) -> GenericExpr<Head, Leaf> {
        let input_count = self
            .args
            .len()
            .checked_sub(1)
            .expect("an atom must include an output argument");
        GenericExpr::Call(
            self.span.clone(),
            self.head.clone(),
            self.args[..input_count]
                .iter()
                .map(GenericAtomTerm::to_expr)
                .collect(),
        )
    }
}

#[derive(Debug, Clone)]
pub struct Query<Head, Leaf, Constant = Literal> {
    pub atoms: Vec<GenericAtom<Head, Leaf, Constant>>,
}

impl<Head, Leaf, Constant> Default for Query<Head, Leaf, Constant> {
    fn default() -> Self {
        Self { atoms: Vec::new() }
    }
}

impl<Head, Leaf: Clone, Constant> Query<Head, Leaf, Constant> {
    pub fn vars(&self) -> impl Iterator<Item = Leaf> + '_ {
        self.atoms.iter().flat_map(GenericAtom::vars)
    }
}

impl<Head, Leaf, Constant> AddAssign for Query<Head, Leaf, Constant> {
    fn add_assign(&mut self, rhs: Self) {
        self.atoms.extend(rhs.atoms);
    }
}

impl<Constant: Display> Display for Query<String, String, Constant> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for atom in &self.atoms {
            writeln!(f, "{atom}")?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum GenericCoreAction<Head, Leaf, Constant = Literal> {
    Let(Span, Leaf, Head, Vec<GenericAtomTerm<Leaf, Constant>>),
    LetAtomTerm(Span, Leaf, GenericAtomTerm<Leaf, Constant>),
    Set(
        Span,
        Head,
        Vec<GenericAtomTerm<Leaf, Constant>>,
        GenericAtomTerm<Leaf, Constant>,
    ),
    Change(Span, Change, Head, Vec<GenericAtomTerm<Leaf, Constant>>),
    Union(
        Span,
        GenericAtomTerm<Leaf, Constant>,
        GenericAtomTerm<Leaf, Constant>,
    ),
    Panic(Span, String),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct GenericCoreActions<Head, Leaf, Constant = Literal>(
    pub Vec<GenericCoreAction<Head, Leaf, Constant>>,
);

impl<Head, Leaf, Constant> Default for GenericCoreActions<Head, Leaf, Constant> {
    fn default() -> Self {
        Self(Vec::new())
    }
}

impl<Head, Leaf, Constant> GenericCoreActions<Head, Leaf, Constant> {
    pub fn new(actions: Vec<GenericCoreAction<Head, Leaf, Constant>>) -> Self {
        Self(actions)
    }

    pub fn free_vars(&self) -> Vec<Leaf>
    where
        Leaf: Clone + Eq,
    {
        fn insert_unique<T: Eq>(values: &mut Vec<T>, value: T) {
            if !values.contains(&value) {
                values.push(value);
            }
        }

        fn add_term<Leaf: Clone + Eq, Constant>(
            free: &mut Vec<Leaf>,
            term: &GenericAtomTerm<Leaf, Constant>,
        ) {
            if let GenericAtomTerm::Var(_, variable) = term {
                insert_unique(free, variable.clone());
            }
        }

        let mut free = Vec::new();

        for action in self.0.iter().rev() {
            match action {
                GenericCoreAction::Let(_, variable, _, arguments) => {
                    for argument in arguments {
                        add_term(&mut free, argument);
                    }
                    free.retain(|candidate| candidate != variable);
                }
                GenericCoreAction::LetAtomTerm(_, variable, term) => {
                    add_term(&mut free, term);
                    free.retain(|candidate| candidate != variable);
                }
                GenericCoreAction::Set(_, _, arguments, value) => {
                    for argument in arguments {
                        add_term(&mut free, argument);
                    }
                    add_term(&mut free, value);
                }
                GenericCoreAction::Change(_, _, _, arguments) => {
                    for argument in arguments {
                        add_term(&mut free, argument);
                    }
                }
                GenericCoreAction::Union(_, lhs, rhs) => {
                    add_term(&mut free, lhs);
                    add_term(&mut free, rhs);
                }
                GenericCoreAction::Panic(..) => {}
            }
        }
        free
    }
}

/// Lowered rule syntax with potentially distinct body and action call types.
#[derive(Debug, Clone)]
pub struct GenericCoreRule<BodyCall, ActionCall, Leaf, Constant = Literal> {
    pub span: Span,
    pub body: Query<BodyCall, Leaf, Constant>,
    pub head: GenericCoreActions<ActionCall, Leaf, Constant>,
}
