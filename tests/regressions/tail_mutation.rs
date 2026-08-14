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
// `&mut self` struct-field writes
//
// A write through a struct-field place has no mutable struct in the
// extraction; it lowers to an assignment of the root variable to a functional
// `struct_update` of the tuple encoding. The failure mode this guards against
// is the field write landing on the `_assign` sink (emitted as `let _ := …`),
// which leaves `self` at its input value and makes every method on the struct
// constant in its own writes.

pub struct Counter {
    h: [u32; 8],
    buf: [u8; 64],
    buf_len: usize,
}

/// Writes through its single `&mut` parameter — the shape `compress` takes in
/// a hash implementation.
///
/// ```lean
/// def mix (h : Array (Int)) (x : Int) :=
///   let h := Hax.array_update h (0 : Int) (Hax.wrapping_add_w 32 (Hax.index h (0 : Int)) x)
///   h
/// ```
pub fn mix(h: &mut [u32; 8], x: u32) {
    h[0] = h[0].wrapping_add(x);
}

impl Counter {
    /// Every statement writes through `self`: a field-element write, a plain
    /// field write, and a write-back call whose `&mut` argument is a field
    /// place. Each becomes an assignment of `self` to a `struct_update` of the
    /// tuple encoding, and the method itself becomes a write-back function
    /// returning `self`.
    ///
    /// ```lean
    /// def Counter_absorb (self : Counter_T) (b : Int) :=
    ///   let self := Hax.struct_update_snd self (Hax.struct_update_fst self.2
    ///     (Hax.array_update («.buf» self) («.buf_len» self) b))
    ///   let self := Hax.struct_update_snd self (Hax.struct_update_snd self.2
    ///     (Hax.add («.buf_len» self) (1 : Int)))
    ///   let self := Hax.struct_update_fst self (mix («.h» self) (Hax.castVal_w 32 b))
    ///   self
    /// ```
    pub fn absorb(&mut self, b: u8) {
        self.buf[self.buf_len] = b;
        self.buf_len = self.buf_len + 1;
        mix(&mut self.h, b as u32);
    }
}

// ---------------------------------------------------------------------------
// Fold-body tails that carry mutations
//
// The fold-body encoders replace a pure-value tail by `cfContinue acc`. A
// `match` at the tail distributes the encoding into its arms, and a nested
// loop at the tail is kept ahead of the continue; the failure mode this
// guards against is either being *replaced* by the continue, dropping the
// mutation (or the whole inner loop).

/// `match` at the fold-body tail: the arm's write must survive.
pub fn match_tail(n: usize, sel: bool) -> u64 {
    let mut acc = 0u64;
    for _i in 0..n {
        match sel {
            true => acc = acc + 2,
            false => acc = acc + 1,
        }
    }
    acc
}

/// Nested loop at the fold-body tail: the inner loop must survive.
pub fn loop_at_tail(n: usize) -> [u64; 4] {
    let mut acc = [0u64; 4];
    for _i in 0..n {
        for j in 0..4 {
            acc[j] = acc[j] + 1;
        }
    }
    acc
}

// ---------------------------------------------------------------------------
// Statement after a conditional break in a loop body
//
// `distributeStmtCF` pushes the statements that follow a conditional break
// into the non-breaking branch before the fold-body encoding, so the write
// below survives on the non-breaking iterations.
//
// ```lean
// Hax.whileFold … fun acc =>
//   if Hax.gt i limit then
//     Hax.cfBreak acc
//   else
//     let acc := Hax.array_update acc …
//     Hax.cfContinue acc
// ```

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
