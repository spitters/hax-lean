/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.TExpr
public import HaxLean.DenoteTotal

/-!
# Byte arrays as little-endian words

A call through a trait bound on byte-encoded arguments (`[u8; 32]`, one word per byte) is
answered by a linked leaf whose parameters are arrays of four `u64` words. This module
defines the conversion between the two layouts and a generated callee that performs it.

## Main definitions

* `ByteWords.packLE` — 32 bytes, each masked to its low 8 bits, as 4 little-endian words.
* `ByteWords.unpackLE` — 4 words as 32 bytes.
* `ByteWords.ArgConv`, `ByteWords.ResConv` — the conversion of an argument (bytes to words, or
  none) and of the result (words to bytes, or a word to the flag `r ≠ 0`).
* `ByteWords.traitWrapperTExpr` — the callee: it packs the arguments with `index`,
  `BitAnd#64`, `Shl#64`, `BitOr#64`, `repeat` and `array_update` at literal positions, calls
  the leaf, and unpacks the result with `index`, `Shr#64`, `BitAnd#64`, or tests it with `Ne`.

## Main results

* `ByteWords.denote'_wrapper` — under `denote'`, at a builtin table that agrees with
  `hax64Builtins` on the heads of the callee, the callee returns the converted result of the
  leaf applied to the converted arguments.
-/

@[expose] public section

namespace Hax

namespace ByteWords

/-! ## The conversion on words -/

/-- Byte `k` of `bs` masked to its low 8 bits, `0` past the end. -/
def maskedByte (bs : List Nat) (k : Nat) : Nat := bs.getD k 0 &&& 255

/-- The little-endian word of the `n` masked bytes of `bs` from position `base`. -/
def packedWord (bs : List Nat) (base : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => packedWord bs base n ||| (maskedByte bs (base + n) <<< (8 * n))

/-- The 4 little-endian `u64` words of the 32 masked bytes of `bs`. -/
def packLE (bs : List Nat) : List Nat := (List.range 4).map fun j => packedWord bs (8 * j) 8

/-- Byte `k` of the little-endian word array `ws`. -/
def wordByteLE (ws : List Nat) (k : Nat) : Nat := (ws.getD (k / 8) 0 >>> (8 * (k % 8))) &&& 255

/-- The 32 little-endian bytes of the 4 words `ws`. -/
def unpackLE (ws : List Nat) : List Nat := (List.range 32).map (wordByteLE ws)

/-- The array value of a list of words. -/
def wordsVal (ns : List Nat) : Value := .array (ns.map fun (n : Nat) => .int n)

/-- The conversion of a wrapper argument: `bytes` packs a byte array into words, `keep`
    passes the value unchanged. -/
inductive ArgConv where
  | bytes
  | keep
  deriving DecidableEq, Repr

/-- The conversion of the leaf's result: `bytes` unpacks a word array into bytes, `flag`
    reads a word as the Boolean `r ≠ 0`. -/
inductive ResConv where
  | bytes
  | flag
  deriving DecidableEq, Repr

/-- The value the leaf receives for an argument value. -/
def ArgConv.apply : ArgConv → Value → Value
  | .bytes, .array vs => wordsVal (packLE (vs.map hax64WordNat))
  | .bytes, v => v
  | .keep, v => v

/-- The argument values the wrapper converts: 32 words below `2^64` for `bytes`, a value
    that is not a control-flow value for `keep`. -/
def ArgConv.Admits : ArgConv → Value → Prop
  | .bytes, v => ∃ bs, v = wordsVal bs ∧ bs.length = 32 ∧ ∀ b ∈ bs, b < 2 ^ 64
  | .keep, v => v.isControlFlow = false

/-- The value the wrapper returns for a result value of the leaf. -/
def ResConv.apply : ResConv → Value → Value
  | .bytes, .array vs => wordsVal (unpackLE (vs.map hax64WordNat))
  | .flag, .int r => .bool (r != 0)
  | _, v => v

/-- The leaf results the wrapper converts: 4 words below `2^64` for `bytes`, an integer for
    `flag`. -/
def ResConv.Admits : ResConv → Value → Prop
  | .bytes, v => ∃ ws, v = wordsVal ws ∧ ws.length = 4 ∧ ∀ w ∈ ws, w < 2 ^ 64
  | .flag, v => ∃ r : Int, v = .int r

/-! ## The callee -/

/-- The type of a `u64` word. -/
abbrev u64Ty : ImpType := .uint .w64

/-- The integer literal `n` at type `u64`. -/
def litE (n : Nat) : TExpr := .mk (.lit (.int n)) u64Ty

/-- The masked byte `p[k] & 255` of the byte array `p`. -/
def byteE (p : String) (k : Nat) : TExpr :=
  .mk (.app "BitAnd#64"
    [.mk (.app "index" [.mk (.var p) (.array (.uint .w8) 32), litE k]) (.uint .w8), litE 255])
    u64Ty

/-- The little-endian word of the `n` masked bytes of `p` from position `base`. -/
def wordE (p : String) (base : Nat) : Nat → TExpr
  | 0 => litE 0
  | n + 1 => .mk (.app "BitOr#64"
      [wordE p base n, .mk (.app "Shl#64" [byteE p (base + n), litE (8 * n)]) u64Ty]) u64Ty

/-- The word array whose first `j` words are those of `packLE` on `p`, the rest `0`. -/
def packE (p : String) : Nat → TExpr
  | 0 => .mk (.app "repeat" [litE 0, litE 4]) (.array u64Ty 4)
  | j + 1 => .mk (.app "array_update" [packE p j, litE j, wordE p (8 * j) 8]) (.array u64Ty 4)

/-- Byte `k` of the word array `r`: `(r[k / 8] >> 8 (k % 8)) & 255`. -/
def byteOfWordE (r : String) (k : Nat) : TExpr :=
  .mk (.app "BitAnd#64"
    [.mk (.app "Shr#64"
      [.mk (.app "index" [.mk (.var r) (.array u64Ty 4), litE (k / 8)]) u64Ty,
       litE (8 * (k % 8))]) u64Ty, litE 255]) u64Ty

/-- The byte array whose first `k` bytes are those of `unpackLE` on `r`, the rest `0`. -/
def unpackE (r : String) : Nat → TExpr
  | 0 => .mk (.app "repeat" [litE 0, litE 32]) (.array (.uint .w8) 32)
  | k + 1 =>
    .mk (.app "array_update" [unpackE r k, litE k, byteOfWordE r k]) (.array (.uint .w8) 32)

/-- The leaf argument for the wrapper parameter `p` under the conversion `c`. -/
def argE : String × ArgConv → TExpr
  | (p, .bytes) => packE p 4
  | (p, .keep) => .mk (.var p) .unknown

/-- The variable the wrapper binds the leaf's result to. -/
def resVar : String := "_trait_link_r"

/-- The wrapper's result from the leaf's result under the conversion `c`. -/
def resE : ResConv → TExpr
  | .bytes => unpackE resVar 32
  | .flag => .mk (.app "Ne" [.mk (.var resVar) u64Ty, litE 0]) .bool

/-- The wrapper callee of the leaf head `leaf`: the parameters `params` converted by their
    `ArgConv`, the call of `leaf`, and the result converted by `res`. -/
def traitWrapperTExpr (leaf : String) (params : List (String × ArgConv)) (res : ResConv) :
    TExpr :=
  .mk (.letBind resVar (.mk (.app leaf (params.map argE)) .unknown) (resE res)) .unknown

/-- The builtin heads the wrapper calls besides the leaf. -/
def wrapperHeads : List String :=
  ["index", "BitAnd#64", "Shl#64", "BitOr#64", "Shr#64", "repeat", "array_update", "Ne"]

/-- A builtin table agrees with `hax64Builtins` on the heads of `wrapperHeads`. -/
def WrapperOps (bi : Builtins) : Prop := ∀ f ∈ wrapperHeads, bi f = hax64Builtins f

theorem wrapperOps_hax64Builtins : WrapperOps hax64Builtins := fun _ _ => rfl

/-! ## Bounds -/

theorem maskedByte_lt (bs : List Nat) (k : Nat) : maskedByte bs k < 2 ^ 8 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem packedWord_lt (bs : List Nat) (base : Nat) (n : Nat) : packedWord bs base n < 2 ^ (8 * n) := by
  induction n with
  | zero => simp [packedWord]
  | succ n ih =>
    rw [packedWord]
    have hm := maskedByte_lt bs (base + n)
    have h1 : packedWord bs base n < 2 ^ (8 * (n + 1)) :=
      Nat.lt_of_lt_of_le ih (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : maskedByte bs (base + n) <<< (8 * n) < 2 ^ (8 * (n + 1)) := by
      rw [Nat.shiftLeft_eq, show 8 * (n + 1) = 8 + 8 * n by omega, Nat.pow_add]
      exact Nat.mul_lt_mul_of_pos_right hm (Nat.two_pow_pos _)
    exact Nat.or_lt_two_pow h1 h2

theorem wordByteLE_lt (ws : List Nat) (k : Nat) : wordByteLE ws k < 2 ^ 8 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-! ## Partially filled arrays -/

/-- The first `j` values of `f` followed by zeros, `n` entries in all. -/
theorem fill_length (f : Nat → Nat) {n j : Nat} (hj : j ≤ n) :
    ((List.range j).map f ++ List.replicate (n - j) 0).length = n := by
  simp only [List.length_append, List.length_map, List.length_range, List.length_replicate,
    Nat.add_sub_cancel' hj]

/-- Setting entry `j` of the partial fill to `f j` extends it by one value. -/
theorem fill_set (f : Nat → Nat) {n j : Nat} (hj : j < n) :
    ((List.range j).map f ++ List.replicate (n - j) 0).set j (f j) =
      (List.range (j + 1)).map f ++ List.replicate (n - (j + 1)) 0 := by
  obtain ⟨m, hm⟩ : ∃ m, n - j = m + 1 := ⟨n - j - 1, by omega⟩
  rw [hm, show n - (j + 1) = m by omega, List.replicate_succ,
    List.set_append_right _ _ (by simp), List.range_succ]
  simp

/-! ## The builtins of the callee on words -/

theorem hax64Builtins_index_nat (vs : List Value) (i : Nat) :
    hax64Builtins "index" [.array vs, .int i] = widthArrayOps "index" [.array vs, .int i] :=
  hax64Builtins_of_none rfl

theorem hax64Builtins_index_wordsVal {ns : List Nat} {i : Nat} (h : i < ns.length) :
    hax64Builtins "index" [wordsVal ns, .int i] = some (.int (ns[i] : Nat)) := by
  rw [wordsVal, hax64Builtins_index_nat]
  simp [widthArrayOps, h]

theorem hax64Builtins_repeat_nat (v : Value) (n : Nat) :
    hax64Builtins "repeat" [v, .int n] = some (.array (List.replicate n v)) := by
  rw [hax64Builtins_of_none rfl]
  rfl

theorem hax64Builtins_arrayUpdate_nat (vs : List Value) (i : Nat) (v : Value) :
    hax64Builtins "array_update" [.array vs, .int i, v] =
      if i < vs.length then some (.array (vs.set i v)) else none := by
  rw [hax64Builtins_of_none rfl]
  simp [widthArrayOps]

theorem hax64Builtins_bitAnd_nat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    hax64Builtins "BitAnd#64" [.int a, .int b] = some (.int (a &&& b : Nat)) := by
  unfold hax64Builtins
  rw [hax64WordOps_bitAnd, u64BinOp_natCast ha hb, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rfl

/-- The unfolding of `hax64WordOps` at the head `BitOr#64` on two integers. -/
theorem hax64WordOps_bitOr_int (a b : Int) : hax64WordOps "BitOr#64" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x % 2 ^ 64) ||| (y % 2 ^ 64)) := rfl

theorem hax64Builtins_bitOr_nat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    hax64Builtins "BitOr#64" [.int a, .int b] = some (.int (a ||| b : Nat)) := by
  unfold hax64Builtins
  rw [hax64WordOps_bitOr_int, u64BinOp_natCast ha hb, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rfl

theorem hax64Builtins_shl_nat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 64) :
    hax64Builtins "Shl#64" [.int a, .int b] = some (.int ((a <<< b) % 2 ^ 64 : Nat)) := by
  unfold hax64Builtins
  rw [hax64WordOps_shl, u64BinOp_natCast ha (Nat.lt_trans hb (by decide)), Nat.mod_eq_of_lt ha,
    if_pos hb]
  rfl

theorem hax64Builtins_shr_nat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 64) :
    hax64Builtins "Shr#64" [.int a, .int b] = some (.int (a >>> b : Nat)) := by
  unfold hax64Builtins
  rw [hax64WordOps_shr, u64BinOp_natCast ha (Nat.lt_trans hb (by decide)), Nat.mod_eq_of_lt ha,
    if_pos hb]
  rfl

/-! ## Evaluation of the pieces -/

section Eval

variable {bi : Builtins} {fuel : Nat} {env : Env}

theorem denote'_litE (n : Nat) : denote' bi fuel (litE n).erase env = (.val (.int n), env) :=
  denote'_lit_run bi fuel _ env

/-- A call of two arguments that evaluate to values without changing the environment. -/
theorem denote'_app_two {f : String} {e₁ e₂ : ImpExpr} {v₁ v₂ w : Value}
    (h₁ : denote' bi fuel e₁ env = (.val v₁, env)) (c₁ : v₁.isControlFlow = false)
    (h₂ : denote' bi fuel e₂ env = (.val v₂, env)) (c₂ : v₂.isControlFlow = false)
    (hf : bi f [v₁, v₂] = some w) :
    denote' bi fuel (.app f [e₁, e₂]) env = (.val w, env) :=
  Total.denote'_app_of_args (Total.denoteArgs'_cons_of_val h₁ c₁
    (Total.denoteArgs'_cons_of_val h₂ c₂ (Total.denoteArgs'_nil_run bi fuel env))) hf

/-- A call of three arguments that evaluate to values without changing the environment. -/
theorem denote'_app_three {f : String} {e₁ e₂ e₃ : ImpExpr} {v₁ v₂ v₃ w : Value}
    (h₁ : denote' bi fuel e₁ env = (.val v₁, env)) (c₁ : v₁.isControlFlow = false)
    (h₂ : denote' bi fuel e₂ env = (.val v₂, env)) (c₂ : v₂.isControlFlow = false)
    (h₃ : denote' bi fuel e₃ env = (.val v₃, env)) (c₃ : v₃.isControlFlow = false)
    (hf : bi f [v₁, v₂, v₃] = some w) :
    denote' bi fuel (.app f [e₁, e₂, e₃]) env = (.val w, env) :=
  Total.denote'_app_of_args (Total.denoteArgs'_cons_of_val h₁ c₁
    (Total.denoteArgs'_cons_of_val h₂ c₂ (Total.denoteArgs'_cons_of_val h₃ c₃
      (Total.denoteArgs'_nil_run bi fuel env)))) hf

variable (hbi : WrapperOps bi)
include hbi

theorem denote'_byteE {p : String} {bs : List Nat} (hp : env p = some (wordsVal bs))
    (hb : ∀ b ∈ bs, b < 2 ^ 64) {k : Nat} (hk : k < bs.length) :
    denote' bi fuel (byteE p k).erase env = (.val (.int (maskedByte bs k)), env) := by
  have hbk : bs[k] < 2 ^ 64 := hb _ (List.getElem_mem hk)
  refine denote'_app_two (v₁ := .int (bs[k] : Nat))
    (denote'_app_two (v₁ := wordsVal bs) ?_ rfl (denote'_litE k) rfl ?_) rfl
    (denote'_litE 255) rfl ?_
  · rw [TExpr.erase, denote'_var_run, hp]
  · rw [hbi "index" (by simp [wrapperHeads]), hax64Builtins_index_wordsVal hk]
  · rw [hbi "BitAnd#64" (by simp [wrapperHeads]), hax64Builtins_bitAnd_nat hbk (by decide)]
    simp [maskedByte, hk]

theorem denote'_wordE {p : String} {bs : List Nat} (hp : env p = some (wordsVal bs))
    (hb : ∀ b ∈ bs, b < 2 ^ 64) {base n : Nat} (hn : n ≤ 8) (hk : base + n ≤ bs.length) :
    denote' bi fuel (wordE p base n).erase env = (.val (.int (packedWord bs base n)), env) := by
  induction n with
  | zero => exact denote'_litE 0
  | succ n ih =>
    have hm := maskedByte_lt bs (base + n)
    have hw := packedWord_lt bs base n
    have h8 : 2 ^ (8 * n) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
    have hs : maskedByte bs (base + n) <<< (8 * n) < 2 ^ 64 := by
      rw [Nat.shiftLeft_eq]
      calc maskedByte bs (base + n) * 2 ^ (8 * n) < 2 ^ 8 * 2 ^ (8 * n) :=
            Nat.mul_lt_mul_of_pos_right hm (Nat.two_pow_pos _)
        _ = 2 ^ (8 * (n + 1)) := by rw [← Nat.pow_add]; congr 1; omega
        _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
    refine denote'_app_two (ih (by omega) (by omega)) rfl
      (v₂ := .int ((maskedByte bs (base + n) <<< (8 * n) : Nat)))
      (denote'_app_two (denote'_byteE hbi hp hb (by omega)) rfl (denote'_litE (8 * n)) rfl ?_)
      rfl ?_
    · rw [hbi "Shl#64" (by simp [wrapperHeads]),
        hax64Builtins_shl_nat (Nat.lt_trans hm (by decide)) (by omega), Nat.mod_eq_of_lt hs]
    · rw [hbi "BitOr#64" (by simp [wrapperHeads]),
        hax64Builtins_bitOr_nat (Nat.lt_of_lt_of_le hw h8) hs]
      rfl

theorem denote'_packE {p : String} {bs : List Nat} (hp : env p = some (wordsVal bs))
    (hb : ∀ b ∈ bs, b < 2 ^ 64) (hl : bs.length = 32) {j : Nat} (hj : j ≤ 4) :
    denote' bi fuel (packE p j).erase env =
      (.val (wordsVal (((List.range j).map fun i => packedWord bs (8 * i) 8) ++
        List.replicate (4 - j) 0)), env) := by
  induction j with
  | zero =>
    refine denote'_app_two (denote'_litE 0) rfl (denote'_litE 4) rfl ?_
    rw [hbi "repeat" (by simp [wrapperHeads]), hax64Builtins_repeat_nat]
    simp [wordsVal]
  | succ j ih =>
    refine denote'_app_three (ih (by omega)) rfl (denote'_litE j) rfl
      (denote'_wordE hbi hp hb (by omega) (by omega)) rfl ?_
    rw [hbi "array_update" (by simp [wrapperHeads]), wordsVal, wordsVal,
      hax64Builtins_arrayUpdate_nat, List.length_map, fill_length _ (by omega), if_pos (by omega : j < 4),
      ← List.map_set, fill_set (fun i => packedWord bs (8 * i) 8) hj]

theorem denote'_byteOfWordE {r : String} {ws : List Nat} (hr : env r = some (wordsVal ws))
    (hw : ∀ w ∈ ws, w < 2 ^ 64) (hl : ws.length = 4) {k : Nat} (hk : k < 32) :
    denote' bi fuel (byteOfWordE r k).erase env = (.val (.int (wordByteLE ws k)), env) := by
  have hk8 : k / 8 < ws.length := by omega
  have hwk : ws[k / 8] < 2 ^ 64 := hw _ (List.getElem_mem hk8)
  have hs : 8 * (k % 8) < 64 := by omega
  refine denote'_app_two (v₁ := .int ((ws[k / 8] >>> (8 * (k % 8)) : Nat)))
    (denote'_app_two (v₁ := .int (ws[k / 8] : Nat))
      (denote'_app_two (v₁ := wordsVal ws) ?_ rfl (denote'_litE _) rfl ?_)
      rfl (denote'_litE _) rfl ?_) rfl (denote'_litE 255) rfl ?_
  · rw [TExpr.erase, denote'_var_run, hr]
  · rw [hbi "index" (by simp [wrapperHeads]), hax64Builtins_index_wordsVal hk8]
  · rw [hbi "Shr#64" (by simp [wrapperHeads]), hax64Builtins_shr_nat hwk hs]
  · rw [hbi "BitAnd#64" (by simp [wrapperHeads]),
      hax64Builtins_bitAnd_nat (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hwk) (by decide)]
    simp [wordByteLE, hk8]

theorem denote'_unpackE {r : String} {ws : List Nat} (hr : env r = some (wordsVal ws))
    (hw : ∀ w ∈ ws, w < 2 ^ 64) (hl : ws.length = 4) {k : Nat} (hk : k ≤ 32) :
    denote' bi fuel (unpackE r k).erase env =
      (.val (wordsVal (((List.range k).map (wordByteLE ws)) ++ List.replicate (32 - k) 0)),
        env) := by
  induction k with
  | zero =>
    refine denote'_app_two (denote'_litE 0) rfl (denote'_litE 32) rfl ?_
    rw [hbi "repeat" (by simp [wrapperHeads]), hax64Builtins_repeat_nat]
    simp [wordsVal]
  | succ k ih =>
    refine denote'_app_three (ih (by omega)) rfl (denote'_litE k) rfl
      (denote'_byteOfWordE hbi hr hw hl (by omega)) rfl ?_
    rw [hbi "array_update" (by simp [wrapperHeads]), wordsVal, wordsVal,
      hax64Builtins_arrayUpdate_nat, List.length_map, fill_length _ (by omega), if_pos (by omega : k < 32),
      ← List.map_set, fill_set (wordByteLE ws) hk]

theorem denote'_argE {q : String × ArgConv} {v : Value} (hq : env q.1 = some v)
    (ha : q.2.Admits v) :
    denote' bi fuel (argE q).erase env = (.val (q.2.apply v), env) ∧
      (q.2.apply v).isControlFlow = false := by
  obtain ⟨p, c⟩ := q
  cases c with
  | bytes =>
    obtain ⟨bs, rfl, hl, hb⟩ := ha
    refine ⟨?_, rfl⟩
    rw [argE, denote'_packE hbi hq hb hl (Nat.le_refl 4)]
    simp only [wordsVal, ArgConv.apply, List.map_map, List.append_nil, Nat.sub_self,
      List.replicate_zero]
    simp [Function.comp_def, hax64WordNat, packLE]
  | keep => exact ⟨by rw [argE, TExpr.erase, denote'_var_run, hq]; rfl, ha⟩

theorem denoteArgs'_argE (params : List (String × ArgConv)) (vals : List Value)
    (hlen : params.length = vals.length)
    (hargs : ∀ q v, (q, v) ∈ params.zip vals → env q.1 = some v ∧ q.2.Admits v) :
    denoteArgs' bi fuel ((params.map argE).map TExpr.erase) env =
      (some (List.zipWith (fun q v => q.2.apply v) params vals), env) := by
  induction params generalizing vals with
  | nil =>
    cases vals with
    | nil => exact Total.denoteArgs'_nil_run bi fuel env
    | cons _ _ => simp at hlen
  | cons q qs ih =>
    cases vals with
    | nil => simp at hlen
    | cons v vs =>
      obtain ⟨hq, ha⟩ := hargs q v (by simp)
      obtain ⟨he, hc⟩ := denote'_argE hbi hq ha
      exact Total.denoteArgs'_cons_of_val he hc
        (ih vs (by simpa using hlen) fun q' v' h => hargs q' v' (by simp [h]))

end Eval

/-! ## The wrapper -/

/-- **The wrapper computes the converted leaf call.** At a builtin table that agrees with
    `hax64Builtins` on `wrapperHeads`, in an environment holding admitted argument values
    `vals` at the parameters, when the leaf answers the converted arguments with an admitted
    result `r`, the wrapper returns the converted result: `unpackLE` of the leaf's words, or
    the flag `r ≠ 0`. -/
theorem denote'_wrapper {bi : Builtins} (fuel : Nat) (hbi : WrapperOps bi) (leaf : String)
    (params : List (String × ArgConv)) (res : ResConv) (env : Env) (vals : List Value)
    (hlen : params.length = vals.length)
    (hargs : ∀ q v, (q, v) ∈ params.zip vals → env q.1 = some v ∧ q.2.Admits v)
    {r : Value} (hleaf : bi leaf (List.zipWith (fun q v => q.2.apply v) params vals) = some r)
    (hr : res.Admits r) :
    (denote' bi fuel (traitWrapperTExpr leaf params res).erase).run' env =
      .val (res.apply r) := by
  have hv : denote' bi fuel (.app leaf ((params.map argE).map TExpr.erase)) env = (.val r, env) :=
    Total.denote'_app_of_args (denoteArgs'_argE hbi params vals hlen hargs) hleaf
  have hcf : r.isControlFlow = false := by
    cases res with
    | bytes => obtain ⟨ws, rfl, -, -⟩ := hr; rfl
    | flag => obtain ⟨z, rfl⟩ := hr; rfl
  have he : (traitWrapperTExpr leaf params res).erase =
      .letBind resVar (.app leaf ((params.map argE).map TExpr.erase)) (resE res).erase := by
    simp [traitWrapperTExpr, TExpr.erase]
  have hx : Env.extend env resVar r resVar = some r := by simp [Env.extend]
  rw [he, StateT.run', Total.denote'_letBind_of_val hv hcf]
  cases res with
  | bytes =>
    obtain ⟨ws, rfl, hl, hw⟩ := hr
    rw [resE, denote'_unpackE hbi hx hw hl (Nat.le_refl 32)]
    simp only [wordsVal, ResConv.apply, List.map_map, List.append_nil, Nat.sub_self,
      List.replicate_zero]
    simp [Function.comp_def, hax64WordNat, unpackLE]
    rfl
  | flag =>
    obtain ⟨z, rfl⟩ := hr
    have hne : bi "Ne" [.int z, .int ((0 : Nat) : Int)] = some (.bool (z != 0)) := by
      rw [hbi "Ne" (by simp [wrapperHeads])]
      unfold hax64Builtins
      rw [hax64WordOps_Ne]
      simp
    show (fun x => x.fst) <$> denote' bi fuel (.app "Ne" [.var resVar, (litE 0).erase])
      (env.extend resVar (.int z)) = _
    rw [denote'_app_two (by rw [denote'_var_run, hx]) rfl (denote'_litE 0) rfl hne]
    rfl

end ByteWords

end Hax
