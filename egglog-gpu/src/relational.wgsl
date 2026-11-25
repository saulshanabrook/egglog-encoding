// Persistent row-major relations. Host control reads cardinalities, never join
// payloads. Every dispatch is a separate pass, providing a global barrier.
struct P { n: u32, m: u32, cols: u32, arg: u32 }
@group(0) @binding(0) var<storage, read> a: array<u32>;
@group(0) @binding(1) var<storage, read> b: array<u32>;
@group(0) @binding(2) var<storage, read> cfg: array<u32>;
@group(0) @binding(3) var<storage, read_write> aux: array<u32>;
@group(0) @binding(4) var<storage, read_write> out: array<u32>;
@group(0) @binding(5) var<uniform> p: P;
var<workgroup> tile: array<u32, 64>;

fn lane(id: vec3<u32>) -> u32 { return id.x + id.y * 4194240u; }
fn stride(cols: u32) -> u32 { return max(cols, 1u); }

@compute @workgroup_size(64)
fn scan_blocks(@builtin(global_invocation_id) gid: vec3<u32>, @builtin(local_invocation_index) local: u32) {
    let i = lane(gid);
    var x = 0u; if (i < p.n) { x = a[i]; }
    tile[local] = x;
    workgroupBarrier();
    for (var step = 1u; step < 64u; step *= 2u) {
        x = tile[local];
        if (local >= step) { x += min(tile[local-step], 0xffffffffu-x); }
        workgroupBarrier();
        tile[local] = x;
        workgroupBarrier();
    }
    if (i < p.n) { out[i] = x; }
    if (local == 63u && i/64u < (p.n+63u)/64u) { aux[i/64u] = x; }
}
@compute @workgroup_size(64)
fn scan_add(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = lane(gid); if (i >= p.n) { return; }
    var x = a[i]; if (i >= 64u) { x += min(b[i/64u-1u], 0xffffffffu-x); }
    out[i] = x;
}

fn compare_rows(l: u32, r: u32) -> i32 {
    if (l == 0xffffffffu) { return select(1, 0, r == l); }
    if (r == 0xffffffffu) { return -1; }
    for (var c = 0u; c < cfg[2]; c++) {
        let col = cfg[3u + c];
        let x = a[l * stride(p.cols) + col]; let y = a[r * stride(p.cols) + col];
        if (x < y) { return -1; } if (x > y) { return 1; }
    }
    if (l < r) { return -1; } if (l > r) { return 1; } return 0;
}
fn tile_exchange(local: u32, global: u32, j: u32, k: u32) {
    let other = local ^ j;
    if (other > local) {
        let x = tile[local]; let y = tile[other]; let order = compare_rows(x, y);
        if (((global & k) == 0u && order > 0) || ((global & k) != 0u && order < 0)) {
            tile[local] = y; tile[other] = x;
        }
    }
}
@compute @workgroup_size(64)
fn sort_tile_init(@builtin(global_invocation_id) gid: vec3<u32>, @builtin(local_invocation_index) local: u32) {
    let i = lane(gid);
    tile[local] = select(0xffffffffu, i, i < p.n);
    workgroupBarrier();
    for (var k = 2u; k <= 64u; k *= 2u) {
        for (var j = k/2u; j > 0u; j /= 2u) {
            tile_exchange(local, i, j, k);
            workgroupBarrier();
        }
    }
    if (i < p.m) { aux[i] = tile[local]; }
}
@compute @workgroup_size(64)
fn sort_tile_merge(@builtin(global_invocation_id) gid: vec3<u32>, @builtin(local_invocation_index) local: u32) {
    let i = lane(gid);
    var x = 0xffffffffu; if (i < p.m) { x = aux[i]; }
    tile[local] = x;
    workgroupBarrier();
    for (var j = 32u; j > 0u; j /= 2u) {
        tile_exchange(local, i, j, cfg[1]);
        workgroupBarrier();
    }
    if (i < p.m) { aux[i] = tile[local]; }
}
@compute @workgroup_size(64)
fn sort_step(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = lane(gid); let j = i ^ cfg[0]; if (i >= p.m || j <= i || j >= p.m) { return; }
    let x = aux[i]; let y = aux[j]; let order = compare_rows(x, y);
    if (((i & cfg[1]) == 0u && order > 0) || ((i & cfg[1]) != 0u && order < 0)) {
        aux[i] = y; aux[j] = x;
    }
}
@compute @workgroup_size(64)
fn unique_flags(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = lane(gid); if (i >= p.n) { return; }
    var distinct = i == 0u;
    if (i > 0u) {
        for (var k = 0u; k < cfg[0]; k++) {
            let c = cfg[k+1u];
            distinct = distinct || a[b[i] * stride(p.cols) + c] != a[b[i-1u] * stride(p.cols) + c];
        }
    }
    out[i] = select(0u, 1u, distinct);
}
@compute @workgroup_size(64)
fn gather_unique(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = lane(gid); if (i >= p.n) { return; }
    var prev = 0u; if (i > 0u) { prev = cfg[i - 1u]; }
    if (cfg[i] == prev) { return; }
    for (var c = 0u; c < p.cols; c++) { out[prev * stride(p.cols) + c] = a[b[i] * stride(p.cols) + c]; }
}
@compute @workgroup_size(64)
fn compact(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = lane(gid); if (i >= p.n) { return; }
    var prev = 0u; if (i > 0u) { prev = b[i - 1u]; }
    if (b[i] == prev) { return; }
    for (var c = 0u; c < p.cols; c++) { out[prev * stride(p.cols) + c] = a[i * stride(p.cols) + c]; }
}

// cfg: constraint count, projection count, occurrence mode/key/count, occurrence
// columns, constraint triples, projection columns (MAX means occurrence key).
@compute @workgroup_size(64)
fn select_project(@builtin(global_invocation_id) gid: vec3<u32>) {
    let slot = lane(gid); if (slot >= p.m) { return; }
    let mode = cfg[2]; let fanout = select(1u, cfg[4], mode == 2u);
    let row = slot / fanout; let occurrence = slot % fanout;
    var valid = b[row] != 0u;
    var key = cfg[3];
    if (mode == 2u) {
        key = a[row * stride(p.cols) + cfg[5u + occurrence]];
        for (var j = 0u; j < occurrence; j++) { valid = valid && key != a[row * stride(p.cols) + cfg[5u + j]]; }
    }
    if (mode == 3u) { key = a[row * stride(p.cols) + cfg[3]]; }
    if (mode == 1u || mode == 3u) {
        var found = false;
        for (var j = 0u; j < cfg[4]; j++) { found = found || key == a[row * stride(p.cols) + cfg[5u + j]]; }
        valid = valid && found;
    }
    let cons = 5u + cfg[4];
    for (var j = 0u; j < cfg[0]; j++) {
        let start = cons + j * 3u; let kind = cfg[start];
        let x = a[row * stride(p.cols) + cfg[start+1u]];
        var y = cfg[start+2u]; if (kind == 0u) { y = a[row * stride(p.cols) + y]; }
        switch kind {
            case 0u, 1u: { valid = valid && x == y; }
            case 2u: { valid = valid && x < y; }
            case 3u: { valid = valid && x <= y; }
            case 4u: { valid = valid && x > y; }
            default: { valid = valid && x >= y; }
        }
    }
    aux[slot] = select(0u, 1u, valid);
    if (!valid) { return; }
    for (var j = 0u; j < cfg[1]; j++) {
        let col = cfg[cons + cfg[0] * 3u + j];
        var val = key; if (col != 0xffffffffu) { val = a[row * stride(p.cols) + col]; }
        out[slot * stride(cfg[1]) + j] = val;
    }
}

// cfg: key count, extra count, (left col,right col)*, extra right columns,
// right row permutation. Prefix allocation and payload materialization stay GPU.
fn join_compare(l: u32, r: u32) -> i32 {
    for (var k = 0u; k < cfg[0]; k++) {
        let x = a[l * stride(p.cols) + cfg[2u + 2u*k]];
        let y = b[r * stride(p.arg) + cfg[3u + 2u*k]];
        if (x < y) { return -1; } if (x > y) { return 1; }
    }
    return 0;
}
fn join_bound(l: u32, upper: bool) -> u32 {
    let order_start = 2u + cfg[0] * 2u + cfg[1];
    var lo = 0u; var hi = p.m;
    while (lo < hi) {
        let mid = lo + (hi-lo)/2u; let cmp = join_compare(l, cfg[order_start+mid]);
        if (cmp > 0 || (upper && cmp == 0)) { lo = mid+1u; } else { hi = mid; }
    }
    return lo;
}
@compute @workgroup_size(64)
fn join_count(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = lane(gid); if (i >= p.n) { return; }
    out[i] = join_bound(i, true) - join_bound(i, false);
}
@compute @workgroup_size(64)
fn join_emit(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = lane(gid); let width = p.cols + cfg[1];
    if (i >= arrayLength(&out) / stride(width)) { return; }
    var lo = 0u; var hi = p.n;
    while (lo < hi) { let mid = lo+(hi-lo)/2u; if (aux[mid] <= i) { lo = mid+1u; } else { hi = mid; } }
    let l = lo; var prev = 0u; if (l > 0u) { prev = aux[l-1u]; }
    let r = cfg[2u + 2u*cfg[0] + cfg[1] + join_bound(l, false) + i-prev];
    for (var c = 0u; c < p.cols; c++) { out[i*stride(width)+c] = a[l*stride(p.cols)+c]; }
    for (var c = 0u; c < cfg[1]; c++) { out[i*stride(width)+p.cols+c] = b[r*stride(p.arg)+cfg[2u+2u*cfg[0]+c]]; }
}

// Project a batch of action rows: kind 0 = constant, 1 = binding column,
// 2 = reserved fresh-id base + lane, 3 = earlier output column.
@compute @workgroup_size(64)
fn action_project(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = lane(gid); if (i >= p.n) { return; }
    for (var c = 0u; c < p.m; c++) {
        let kind = cfg[2u*c]; let v = cfg[2u*c+1u]; var x = v;
        if (kind == 1u) { x = a[i*stride(p.cols)+v]; }
        if (kind == 2u) { x = v+i; }
        if (kind == 3u) { x = out[i*stride(p.m)+v]; }
        out[i*stride(p.m)+c] = x;
    }
}

@compute @workgroup_size(64)
fn bind_column(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = lane(gid); if (i >= p.n) { return; }
    for (var c = 0u; c < p.m; c++) {
        var x = 0u;
        if (c == cfg[1]) { x = b[i*stride(p.arg)+cfg[0]]; }
        else { x = a[i*stride(p.cols)+c]; }
        out[i*stride(p.m)+c] = x;
    }
}
fn entry(row: u32, offset: u32) -> u32 {
    let kind = cfg[offset]; let v = cfg[offset+1u];
    if (kind == 0u) { return v; } return a[row*stride(p.cols)+v];
}
// cfg: comparison mode (eq/ne/any-ne), pair count, entry pairs.
@compute @workgroup_size(64)
fn assert_flags(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = lane(gid); if (i >= p.n) { return; }
    var any_ne = false;
    for (var j = 0u; j < cfg[1]; j++) { any_ne = any_ne || entry(i, 2u+4u*j) != entry(i, 4u+4u*j); }
    out[i] = select(0u, 1u, select(any_ne, !any_ne, cfg[0] == 0u));
}
@compute @workgroup_size(64)
fn lookup_values(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = lane(gid); if (i >= p.n) { return; }
    let start = join_bound(i, false);
    var found = 0u; var val = 0u;
    if (start < p.m) {
        let row = cfg[3u+2u*cfg[0]+start];
        if (join_compare(i, row) == 0) { found = 1u; val = b[row*stride(p.arg)+cfg[2u+2u*cfg[0]]]; }
    }
    out[2u*i] = found; out[2u*i+1u] = val;
}

// One workgroup per probe. The minimum physical row matches the sorted
// lookup's tie breaking, even if the caller supplies duplicate keys.
@compute @workgroup_size(64)
fn lookup_small(@builtin(global_invocation_id) gid: vec3<u32>, @builtin(local_invocation_index) local: u32) {
    let key = lane(gid)/64u;
    var found = 0xffffffffu;
    for (var row = local; row < p.m; row += 64u) {
        var matches = true;
        for (var c = 0u; c < p.cols; c++) {
            matches = matches && a[key*stride(p.cols)+c] == b[row*stride(p.arg)+c];
        }
        if (matches) { found = row; break; }
    }
    tile[local] = found;
    workgroupBarrier();
    for (var step = 32u; step > 0u; step /= 2u) {
        if (local < step) { tile[local] = min(tile[local], tile[local+step]); }
        workgroupBarrier();
    }
    if (local == 0u) {
        found = tile[0];
        out[2u*key] = select(0u, 1u, found != 0xffffffffu);
        if (found != 0xffffffffu) { out[2u*key+1u] = b[found*stride(p.arg)+cfg[0]]; }
    }
}

@compute @workgroup_size(64)
fn resolve_lookup(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = lane(gid); if (i >= p.n) { return; }
    out[i] = select(entry(i, 0u), b[2u*i+1u], b[2u*i] == 1u);
}
