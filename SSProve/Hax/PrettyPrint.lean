/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/
import SSProve.Hax.AST

/-!
# Lean 4 Pretty-Printer for ImpExpr

Emits Lean 4 source code from post-pipeline `ImpExpr`.

Assumes a runtime library providing `Hax.forFold`, `Hax.whileFold`, etc.
The output can be compiled by Lean 4 given appropriate imports.

**Not imported by the proof library** — only used by the executable.
-/

namespace SSProve.Hax

/-- Indent by `n` levels (2 spaces each). -/
private def indent (n : Nat) : String :=
  String.ofList (List.replicate (2 * n) ' ')

/-- Sanitize a name for Lean 4: wrap in French quotes if needed. -/
private def sanitizeName (n : String) : String :=
  -- Lean keywords and names with special chars need quoting
  if n.isEmpty then "«»"
  else if n.any fun c => !c.isAlphanum && c != '_' && c != '\'' then s!"«{n}»"
  else
    match n with
    | "if" | "then" | "else" | "let" | "do" | "match" | "with" | "where"
    | "fun" | "return" | "for" | "in" | "while" | "break" | "continue"
    | "true" | "false" | "def" | "theorem" | "import" | "open" | "namespace"
    | "end" | "structure" | "inductive" | "class" | "instance" | "section"
    | "variable" | "axiom" | "by" | "have" | "show" | "sorry" | "Type"
    | "Prop" | "Sort" | "Set" | "mutual" | "noncomputable" | "private"
    | "protected" | "partial" | "unsafe" => s!"«{n}»"
    | _ => n

/-- Pretty-print a pattern. -/
private def patToLean : ImpPat → String
  | .wildcard => "_"
  | .litPat (.bool true) => "true"
  | .litPat (.bool false) => "false"
  | .litPat (.int n) => toString n
  | .litPat .unit => "()"
  | .varPat n => sanitizeName n
  | .tuplePat ps => s!"({", ".intercalate (ps.map patToLean)})"
  | .somePat p => s!"some ({patToLean p})"
  | .nonePat => "none"
  | .okPat p => s!"Except.ok ({patToLean p})"
  | .errPat p => s!"Except.error ({patToLean p})"

/-- Is this expression simple enough to not need parentheses as an argument? -/
private def isAtom : ImpExpr → Bool
  | .lit _ | .var _ | .unitVal => true
  | .tuple _ => true  -- tuples have their own parens
  | _ => false

/-- Wrap in parentheses if needed. -/
private def parensIf (s : String) (needParens : Bool) : String :=
  if needParens then s!"({s})" else s

/-- Pretty-print an ImpExpr as Lean 4 source code.
    `lvl` is the current indentation level. -/
partial def toLean (e : ImpExpr) (lvl : Nat := 0) : String :=
  let ind := indent lvl
  let ind1 := indent (lvl + 1)
  match e with
  -- Literals
  | .lit (.bool true) => "true"
  | .lit (.bool false) => "false"
  | .lit (.int n) => if n < 0 then s!"({n})" else toString n
  | .lit .unit => "()"
  | .unitVal => "()"

  -- Variables
  | .var n => sanitizeName n

  -- Let binding (multi-line)
  | .letBind n val body =>
    s!"{ind}let {sanitizeName n} := {toLean val 0}\n{toLean body lvl}"

  -- Function application
  | .app f args =>
    let argStrs := args.map fun a => parensIf (toLean a 0) (!isAtom a)
    s!"{sanitizeName f} {" ".intercalate argStrs}"

  -- Tuple
  | .tuple elems =>
    s!"({", ".intercalate (elems.map fun e => toLean e 0)})"

  -- Projection
  | .proj e i =>
    s!"{parensIf (toLean e 0) (!isAtom e)}.{i}"

  -- Conditional
  | .ifThenElse c t e =>
    s!"{ind}if {toLean c 0} then\n{ind1}{toLean t (lvl + 1)}\n{ind}else\n{ind1}{toLean e (lvl + 1)}"

  -- Pattern match
  | .match_ scrut arms =>
    let armStrs := arms.map fun (p, body) =>
      s!"{ind}| {patToLean p} => {toLean body (lvl + 1)}"
    s!"{ind}match {toLean scrut 0} with\n{"\n".intercalate armStrs}"

  -- Sequence
  | .seq e1 e2 =>
    s!"{toLean e1 lvl}\n{toLean e2 lvl}"

  -- ControlFlow constructors (post-pipeline)
  | .cfBreak e =>
    s!"ControlFlow.Break {parensIf (toLean e 0) (!isAtom e)}"
  | .cfContinue e =>
    s!"ControlFlow.Continue {parensIf (toLean e 0) (!isAtom e)}"
  | .cfBreakContinue e =>
    s!"ControlFlow.Break (ControlFlow.Continue {parensIf (toLean e 0) (!isAtom e)})"

  -- Fold operations (post-pipeline)
  | .forFold v lo hi body =>
    s!"{ind}Hax.forFold {parensIf (toLean lo 0) (!isAtom lo)} {parensIf (toLean hi 0) (!isAtom hi)} fun {sanitizeName v} =>\n{ind1}{toLean body (lvl + 1)}"
  | .whileFold c body =>
    s!"{ind}Hax.whileFold (fun () => {toLean c 0}) fun () =>\n{ind1}{toLean body (lvl + 1)}"
  | .forFoldReturn v lo hi body =>
    s!"{ind}Hax.forFoldReturn {parensIf (toLean lo 0) (!isAtom lo)} {parensIf (toLean hi 0) (!isAtom hi)} fun {sanitizeName v} =>\n{ind1}{toLean body (lvl + 1)}"
  | .whileFoldReturn c body =>
    s!"{ind}Hax.whileFoldReturn (fun () => {toLean c 0}) fun () =>\n{ind1}{toLean body (lvl + 1)}"

  -- Pre-pipeline constructors (should not appear in output, but handle gracefully)
  | .borrow e => s!"(& {toLean e 0})"
  | .deref e => s!"(* {toLean e 0})"
  | .assign n rhs => s!"{sanitizeName n} := {toLean rhs 0}"
  | .forLoop v lo hi body =>
    s!"{ind}for {sanitizeName v} in {toLean lo 0} .. {toLean hi 0} do\n{ind1}{toLean body (lvl + 1)}"
  | .whileLoop c body =>
    s!"{ind}while {toLean c 0} do\n{ind1}{toLean body (lvl + 1)}"
  | .break_ none => "break"
  | .break_ (some e) => s!"break {toLean e 0}"
  | .continue_ => "continue"
  | .earlyReturn e => s!"return {toLean e 0}"
  | .questionMark e => s!"{parensIf (toLean e 0) (!isAtom e)}?"

/-- Wrap the output in a Lean 4 definition. -/
def toLeanDef (name : String) (e : ImpExpr) : String :=
  let body := toLean e 1
  s!"def {sanitizeName name} :=\n{body}\n"

/-- Generate a complete Lean 4 file from pipeline output. -/
def toLeanFile (defs : List (String × ImpExpr))
    (moduleName : String := "Generated") : String :=
  let header := s!"/-\n  Auto-generated by haxpipe (verified hax pipeline)\n-/\n\nnamespace {moduleName}\n\n"
  let body := "\n".intercalate (defs.map fun (n, e) => toLeanDef n e)
  let footer := s!"\nend {moduleName}\n"
  header ++ body ++ footer

end SSProve.Hax
