// Reproducer: a mutation at the tail of an `if`- or `match`-statement branch.
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
