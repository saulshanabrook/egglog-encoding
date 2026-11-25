struct Params { left_rows: u32, right_rows: u32, keys: u32, output_rows: u32 }
@group(0) @binding(0) var<storage, read> lhs: array<u32>;
@group(0) @binding(1) var<storage, read> rhs: array<u32>;
@group(0) @binding(2) var<storage, read> keys: array<vec2<u32>>;
@group(0) @binding(3) var<storage, read_write> offsets: array<u32>;
@group(0) @binding(4) var<storage, read_write> pairs: array<vec2<u32>>;
@group(0) @binding(5) var<uniform> params: Params;

fn compare(l: u32, r: u32) -> i32 {
    for (var k = 0u; k < params.keys; k++) {
        let a = lhs[keys[k].x * params.left_rows + l];
        let b = rhs[keys[k].y * params.right_rows + r];
        if (a < b) { return -1; }
        if (a > b) { return 1; }
    }
    return 0;
}

fn bound(l: u32, upper: bool) -> u32 {
    var lo = 0u;
    var hi = params.right_rows;
    while (lo < hi) {
        let mid = lo + (hi - lo) / 2u;
        let order = compare(l, mid);
        if (order > 0 || (upper && order == 0)) { lo = mid + 1u; }
        else { hi = mid; }
    }
    return lo;
}

@compute @workgroup_size(64)
fn count(@builtin(global_invocation_id) id: vec3<u32>) {
    if (id.x >= params.left_rows) { return; }
    offsets[id.x] = bound(id.x, true) - bound(id.x, false);
}

@compute @workgroup_size(64)
fn emit(@builtin(global_invocation_id) id: vec3<u32>) {
    if (id.x >= params.output_rows) { return; }
    // Upper bound skips empty left rows and distributes skewed fanout across
    // output lanes instead of assigning all writes to one input lane.
    var lo = 0u;
    var hi = params.left_rows;
    while (lo < hi) {
        let mid = lo + (hi - lo) / 2u;
        if (offsets[mid] <= id.x) { lo = mid + 1u; }
        else { hi = mid; }
    }
    let l = lo - 1u;
    pairs[id.x] = vec2<u32>(l, bound(l, false) + id.x - offsets[l]);
}
