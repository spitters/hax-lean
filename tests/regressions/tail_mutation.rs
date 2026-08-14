// Reproducers for mutations the emitter can drop: one at the tail of an `if`-
// or `match`-statement branch (first section), one written through a `&mut`
// argument (second section).
//
// Each function below mutates a variable from a position that is the *last
// item* of an `if` branch — a nested `if`, a `match`, a loop, an `else if`
// chain — or from an arm of a `match` used as a statement. The mutated
// variable is read after the join, so `tThreadMut` restructures the join and
// `tReplaceTail` rewrites each branch or arm.
//
// Drive it through the emitter with:
//
//     cargo hax json --output hax_frontend_export.json
//     haxpipeT --hax hax_frontend_export.json --emit-certified --name TailMutation
//
// The expected Lean is sketched above each function (the surface details —
// binder types, ascriptions — follow whatever the renderer produces; what
// matters is that the mutation appears). The failure mode this guards against
// is an emitted branch that binds the intermediate `let`s and then returns the
// variable unchanged, with the mutation gone.

/// Nested `if` at the branch tail.
///
/// ```lean
/// let _mtup :=
///   if a then
///     if b then
///       let acc := (1 : Int)
///       acc
///     else
///       acc
///   else
///     acc
/// let acc := _mtup
/// acc
/// ```
pub fn nested_if(acc: u64, a: bool, b: bool) -> u64 {
    let mut acc = acc;
    if a {
        if b {
            acc = 1;
        }
    }
    acc
}

/// Loop at the branch tail.
///
/// ```lean
/// let _mtup :=
///   if a then
///     let acc := Hax.foldRange (0 : Int) (4 : Int) acc fun i acc =>
///       (Hax.array_update acc i (0 : Int) : Array (Int))
///     acc
///   else
///     acc
/// let acc := (_mtup : Array (Int))
/// acc
/// ```
pub fn loop_tail(acc: [u64; 4], a: bool) -> [u64; 4] {
    let mut acc = acc;
    if a {
        for i in 0..4 {
            acc[i] = 0;
        }
    }
    acc
}

/// Indexed compound assignment inside a nested `if` — the shape that appears in
/// `picnic-hax`'s `set_bit`. The `let mask` binding lives inside the outer
/// branch, so the nested `if` is that branch's tail.
///
/// ```lean
/// let _mtup :=
///   if Hax.lt i (64 : Int) then
///     let mask := Hax.shl_w 64 (1 : Int) (Hax.sub (63 : Int) i)
///     if Hax.bne val (0 : Int) then
///       let result :=
///         (Hax.array_update result (0 : Int)
///           (Hax.bitor_w 64 (Hax.index result (0 : Int)) mask) : Array (Int))
///       result
///     else
///       let result :=
///         (Hax.array_update result (0 : Int)
///           (Hax.bitand_w 64 (Hax.index result (0 : Int)) (Hax.bitnot_w 64 mask))
///          : Array (Int))
///       result
///   else
///     result
/// let result := (_mtup : Array (Int))
/// result
/// ```
pub fn set_bit(block: [u64; 2], i: usize, val: u64) -> [u64; 2] {
    let mut result = block;
    if i < 64 {
        let mask = 1u64 << (63 - i);
        if val != 0 {
            result[0] |= mask;
        } else {
            result[0] &= !mask;
        }
    }
    result
}

/// `else if` chain at the branch tail — the shape that appears in
/// `libcrux-specs-hax`'s edwards25519 point decompression.
///
/// ```lean
/// let _mtup :=
///   if p then
///     x
///   else
///     if q then
///       let x := Hax.add x (1 : Int)
///       x
///     else
///       x
/// let x := _mtup
/// x
/// ```
pub fn else_if_chain(x: u64, p: bool, q: bool) -> u64 {
    let mut x = x;
    if p {
        // x is already correct
    } else if q {
        x = x + 1;
    }
    x
}

// ---------------------------------------------------------------------------
// `&mut` write-back
//
// A function taking `&mut v` and yielding `()` writes through `v`. The
// extraction has no references, so the function returns `v` and each caller
// rebinds its own variable from the result. The failure mode this guards
// against is a call kept in statement position with its result dropped, which
// leaves the caller's variable at its pre-call value and makes the whole
// function constant in its inputs.

/// Writes through its single `&mut` parameter and yields `()`.
///
/// ```lean
/// def scale (v : Array (Int)) (k : Int) :=
///   let v := Hax.array_update v (0 : Int) (Hax.wrapping_mul_w 64 (Hax.index v (0 : Int)) k)
///   let v := Hax.array_update v (1 : Int) (Hax.wrapping_mul_w 64 (Hax.index v (1 : Int)) k)
///   v
/// ```
pub fn scale(v: &mut [u64; 2], k: u64) {
    v[0] = v[0].wrapping_mul(k);
    v[1] = v[1].wrapping_mul(k);
}

/// Calls a write-back function in statement position and reads the variable
/// afterwards.
///
/// ```lean
/// def scale_twice (v : Array (Int)) (k : Int) : Array (Int) :=
///   let out := v
///   let out := scale out k
///   let out := scale out k
///   out
/// ```
pub fn scale_twice(v: [u64; 2], k: u64) -> [u64; 2] {
    let mut out = v;
    scale(&mut out, k);
    scale(&mut out, k);
    out
}

/// Calls a write-back function inside a loop body, so the mutated variable
/// becomes the fold accumulator.
///
/// ```lean
/// def scale_rounds (v : Array (Int)) (k : Int) (n : Int) : Array (Int) :=
///   let out := v
///   let out := Hax.foldRange (0 : Int) n out fun _i out =>
///     scale out k
///   out
/// ```
pub fn scale_rounds(v: [u64; 2], k: u64, n: usize) -> [u64; 2] {
    let mut out = v;
    for _i in 0..n {
        scale(&mut out, k);
    }
    out
}

/// Two `&mut` parameters: no single parameter is the result, so the write-back
/// rewrite is declined and both mutations are still lost. Kept as the marker
/// for the remaining gap.
pub fn swap_first(a: &mut [u64; 2], b: &mut [u64; 2]) {
    let t = a[0];
    a[0] = b[0];
    b[0] = t;
}

/// A `&mut` borrow of an element rather than of a variable: the callee's result
/// is that element, so the write-back rewrite is declined here too.
pub fn bump(x: &mut u64) {
    *x = x.wrapping_add(1);
}

pub fn bump_first(v: [u64; 2]) -> [u64; 2] {
    let mut out = v;
    bump(&mut out[0]);
    out
}

// ---------------------------------------------------------------------------
// Statement after a conditional break in a loop body
//
// `encodeForFoldBody`'s `seq` case drops the tail whenever the head contains a
// surface control-flow node, and `hasSurfaceCF` reports an `ifThenElse` whose
// *one* branch breaks. Whether the shape below reaches that case, or whether an
// earlier pass has already inlined the tail into the non-breaking branch, is
// what this function measures: if `acc` comes back all zeros the tail was
// dropped.

pub fn break_then_write(n: usize, limit: usize) -> [u64; 4] {
    let mut acc = [0u64; 4];
    for i in 0..n {
        if i > limit {
            break;
        }
        acc[i % 4] = acc[i % 4] + 1;
    }
    acc
}
