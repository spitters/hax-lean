/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/
import SSProve.Hax.AST
import SSProve.Hax.ImpType
import SSProve.Hax.TExpr
import Lean.Data.Json

/-!
# JSON Serialization for Hax AST

`FromJson`/`ToJson` instances for `ImpLit`, `ImpPat`, `ImpType`, `ImpExpr`,
`TExprKind`, and `TExpr`. These enable importing/exporting hax AST dumps
for translation validation and the verified pipeline CLI.

**Not imported by the proof library** — only used by the executable.
-/

namespace SSProve.Hax

open Lean (Json ToJson FromJson toJson fromJson?)

/-! ## ImpLit -/

instance : ToJson ImpLit where
  toJson
    | .bool b => Json.mkObj [("bool", toJson b)]
    | .int n => Json.mkObj [("int", toJson n)]
    | .unit => Json.str "unit"

instance : FromJson ImpLit where
  fromJson? j := do
    if let .str "unit" := j then return .unit
    else if let .ok b := j.getObjValAs? Bool "bool" then return .bool b
    else if let .ok n := j.getObjValAs? Int "int" then return .int n
    else throw s!"expected ImpLit, got {j}"

/-! ## ImpPat -/

private def impPatToJson : ImpPat → Json
  | .wildcard => Json.str "wildcard"
  | .nonePat => Json.str "nonePat"
  | .litPat l => Json.mkObj [("litPat", toJson l)]
  | .varPat n => Json.mkObj [("varPat", Json.str n)]
  | .tuplePat ps => Json.mkObj [("tuplePat", Json.arr (ps.map impPatToJson).toArray)]
  | .somePat p => Json.mkObj [("somePat", impPatToJson p)]
  | .okPat p => Json.mkObj [("okPat", impPatToJson p)]
  | .errPat p => Json.mkObj [("errPat", impPatToJson p)]

private partial def impPatFromJson (j : Json) : Except String ImpPat := do
  if let .str "wildcard" := j then return .wildcard
  else if let .str "nonePat" := j then return .nonePat
  else if let .ok l := j.getObjValAs? ImpLit "litPat" then return .litPat l
  else if let .ok n := j.getObjValAs? String "varPat" then return .varPat n
  else if let .ok arr := j.getObjValAs? (Array Json) "tuplePat" then
    let ps ← arr.toList.mapM impPatFromJson
    return .tuplePat ps
  else if let .ok sub := j.getObjVal? "somePat" then
    return .somePat (← impPatFromJson sub)
  else if let .ok sub := j.getObjVal? "okPat" then
    return .okPat (← impPatFromJson sub)
  else if let .ok sub := j.getObjVal? "errPat" then
    return .errPat (← impPatFromJson sub)
  else throw s!"expected ImpPat, got {j}"

instance : ToJson ImpPat where toJson := impPatToJson
instance : FromJson ImpPat where fromJson? := impPatFromJson

/-! ## ImpType -/

private def impTypeToJson : ImpType → Json
  | .bool => Json.str "bool"
  | .int => Json.str "int"
  | .unit => Json.str "unit"
  | .str => Json.str "str"
  | .unknown => Json.str "unknown"
  | .tuple es => Json.mkObj [("tuple", Json.arr (es.map impTypeToJson).toArray)]
  | .option t => Json.mkObj [("option", impTypeToJson t)]
  | .result ok err =>
    Json.mkObj [("result", Json.mkObj [("ok", impTypeToJson ok), ("err", impTypeToJson err)])]
  | .controlFlow brk cont =>
    Json.mkObj [("controlFlow",
      Json.mkObj [("brk", impTypeToJson brk), ("cont", impTypeToJson cont)])]
  | .adt name args =>
    Json.mkObj [("adt", Json.mkObj [("name", Json.str name),
      ("args", Json.arr (args.map impTypeToJson).toArray)])]
  | .fn params ret =>
    Json.mkObj [("fn", Json.mkObj [("params", Json.arr (params.map impTypeToJson).toArray),
      ("ret", impTypeToJson ret)])]
  | .ref inner isMut =>
    Json.mkObj [("ref", Json.mkObj [("inner", impTypeToJson inner),
      ("isMut", toJson isMut)])]
  | .slice t => Json.mkObj [("slice", impTypeToJson t)]
  | .array t len =>
    Json.mkObj [("array", Json.mkObj [("inner", impTypeToJson t),
      ("len", toJson len)])]
  | .typeVar n => Json.mkObj [("typeVar", Json.str n)]

private partial def impTypeFromJson (j : Json) : Except String ImpType := do
  match j with
  | .str "bool" => return .bool
  | .str "int" => return .int
  | .str "unit" => return .unit
  | .str "str" => return .str
  | .str "unknown" => return .unknown
  | _ =>
    if let .ok arr := j.getObjValAs? (Array Json) "tuple" then
      return .tuple (← arr.toList.mapM impTypeFromJson)
    else if let .ok sub := j.getObjVal? "option" then
      return .option (← impTypeFromJson sub)
    else if let .ok sub := j.getObjVal? "result" then
      return .result (← impTypeFromJson (← sub.getObjVal? "ok"))
        (← impTypeFromJson (← sub.getObjVal? "err"))
    else if let .ok sub := j.getObjVal? "controlFlow" then
      return .controlFlow (← impTypeFromJson (← sub.getObjVal? "brk"))
        (← impTypeFromJson (← sub.getObjVal? "cont"))
    else if let .ok sub := j.getObjVal? "adt" then
      let name ← sub.getObjValAs? String "name"
      let args ← (← sub.getObjValAs? (Array Json) "args").toList.mapM impTypeFromJson
      return .adt name args
    else if let .ok sub := j.getObjVal? "fn" then
      let params ← (← sub.getObjValAs? (Array Json) "params").toList.mapM impTypeFromJson
      let ret ← impTypeFromJson (← sub.getObjVal? "ret")
      return .fn params ret
    else if let .ok sub := j.getObjVal? "ref" then
      let inner ← impTypeFromJson (← sub.getObjVal? "inner")
      let isMut ← sub.getObjValAs? Bool "isMut"
      return .ref inner isMut
    else if let .ok sub := j.getObjVal? "slice" then
      return .slice (← impTypeFromJson sub)
    else if let .ok sub := j.getObjVal? "array" then
      let inner ← impTypeFromJson (← sub.getObjVal? "inner")
      let len ← sub.getObjValAs? Nat "len"
      return .array inner len
    else if let .ok n := j.getObjValAs? String "typeVar" then
      return .typeVar n
    else throw s!"expected ImpType, got {j}"

instance : ToJson ImpType where toJson := impTypeToJson
instance : FromJson ImpType where fromJson? := impTypeFromJson

/-! ## ImpExpr -/

private partial def impExprToJson : ImpExpr → Json
  | .lit v => Json.mkObj [("lit", toJson v)]
  | .var n => Json.mkObj [("var", Json.str n)]
  | .unitVal => Json.str "unitVal"
  | .continue_ => Json.str "continue"
  | .letBind n val body =>
    Json.mkObj [("letBind", Json.mkObj [("name", Json.str n),
      ("val", impExprToJson val), ("body", impExprToJson body)])]
  | .app f args =>
    Json.mkObj [("app", Json.mkObj [("f", Json.str f),
      ("args", Json.arr (args.map impExprToJson).toArray)])]
  | .tuple elems =>
    Json.mkObj [("tuple", Json.arr (elems.map impExprToJson).toArray)]
  | .proj e i =>
    Json.mkObj [("proj", Json.mkObj [("e", impExprToJson e), ("i", toJson i)])]
  | .ifThenElse c t e =>
    Json.mkObj [("ifThenElse", Json.mkObj [
      ("cond", impExprToJson c), ("thn", impExprToJson t), ("els", impExprToJson e)])]
  | .match_ scrut arms =>
    Json.mkObj [("match", Json.mkObj [
      ("scrut", impExprToJson scrut),
      ("arms", Json.arr (arms.map fun (p, e) =>
        Json.mkObj [("pat", toJson p), ("body", impExprToJson e)]).toArray)])]
  | .seq e1 e2 =>
    Json.mkObj [("seq", Json.mkObj [("e1", impExprToJson e1), ("e2", impExprToJson e2)])]
  | .borrow e => Json.mkObj [("borrow", impExprToJson e)]
  | .deref e => Json.mkObj [("deref", impExprToJson e)]
  | .assign n rhs =>
    Json.mkObj [("assign", Json.mkObj [("name", Json.str n), ("rhs", impExprToJson rhs)])]
  | .forLoop v lo hi body =>
    Json.mkObj [("forLoop", Json.mkObj [("var", Json.str v),
      ("lo", impExprToJson lo), ("hi", impExprToJson hi), ("body", impExprToJson body)])]
  | .whileLoop c body =>
    Json.mkObj [("whileLoop", Json.mkObj [
      ("cond", impExprToJson c), ("body", impExprToJson body)])]
  | .break_ none => Json.mkObj [("break", Json.null)]
  | .break_ (some e) => Json.mkObj [("break", impExprToJson e)]
  | .earlyReturn e => Json.mkObj [("earlyReturn", impExprToJson e)]
  | .questionMark e => Json.mkObj [("questionMark", impExprToJson e)]
  | .forFold v lo hi body =>
    Json.mkObj [("forFold", Json.mkObj [("var", Json.str v),
      ("lo", impExprToJson lo), ("hi", impExprToJson hi), ("body", impExprToJson body)])]
  | .whileFold c body =>
    Json.mkObj [("whileFold", Json.mkObj [
      ("cond", impExprToJson c), ("body", impExprToJson body)])]
  | .forFoldReturn v lo hi body =>
    Json.mkObj [("forFoldReturn", Json.mkObj [("var", Json.str v),
      ("lo", impExprToJson lo), ("hi", impExprToJson hi), ("body", impExprToJson body)])]
  | .whileFoldReturn c body =>
    Json.mkObj [("whileFoldReturn", Json.mkObj [
      ("cond", impExprToJson c), ("body", impExprToJson body)])]
  | .cfBreak e => Json.mkObj [("cfBreak", impExprToJson e)]
  | .cfContinue e => Json.mkObj [("cfContinue", impExprToJson e)]
  | .cfBreakContinue e => Json.mkObj [("cfBreakContinue", impExprToJson e)]

private partial def impExprFromJson (j : Json) : Except String ImpExpr := do
  match j with
  | .str "unitVal" => return .unitVal
  | .str "continue" => return .continue_
  | _ =>
    if let .ok v := j.getObjValAs? ImpLit "lit" then return .lit v
    else if let .ok n := j.getObjValAs? String "var" then return .var n
    else if let .ok sub := j.getObjVal? "letBind" then
      let name ← sub.getObjValAs? String "name"
      let val ← impExprFromJson (← sub.getObjVal? "val")
      let body ← impExprFromJson (← sub.getObjVal? "body")
      return .letBind name val body
    else if let .ok sub := j.getObjVal? "app" then
      let f ← sub.getObjValAs? String "f"
      let args ← (← sub.getObjValAs? (Array Json) "args").toList.mapM impExprFromJson
      return .app f args
    else if let .ok arr := j.getObjValAs? (Array Json) "tuple" then
      return .tuple (← arr.toList.mapM impExprFromJson)
    else if let .ok sub := j.getObjVal? "proj" then
      let e ← impExprFromJson (← sub.getObjVal? "e")
      let i ← sub.getObjValAs? Nat "i"
      return .proj e i
    else if let .ok sub := j.getObjVal? "ifThenElse" then
      let c ← impExprFromJson (← sub.getObjVal? "cond")
      let t ← impExprFromJson (← sub.getObjVal? "thn")
      let e ← impExprFromJson (← sub.getObjVal? "els")
      return .ifThenElse c t e
    else if let .ok sub := j.getObjVal? "match" then
      let scrut ← impExprFromJson (← sub.getObjVal? "scrut")
      let armsJ ← sub.getObjValAs? (Array Json) "arms"
      let arms ← armsJ.toList.mapM fun aj => do
        let p ← fromJson? (← aj.getObjVal? "pat")
        let body ← impExprFromJson (← aj.getObjVal? "body")
        return (p, body)
      return .match_ scrut arms
    else if let .ok sub := j.getObjVal? "seq" then
      let e1 ← impExprFromJson (← sub.getObjVal? "e1")
      let e2 ← impExprFromJson (← sub.getObjVal? "e2")
      return .seq e1 e2
    else if let .ok sub := j.getObjVal? "borrow" then
      return .borrow (← impExprFromJson sub)
    else if let .ok sub := j.getObjVal? "deref" then
      return .deref (← impExprFromJson sub)
    else if let .ok sub := j.getObjVal? "assign" then
      let name ← sub.getObjValAs? String "name"
      let rhs ← impExprFromJson (← sub.getObjVal? "rhs")
      return .assign name rhs
    else if let .ok sub := j.getObjVal? "forLoop" then
      let v ← sub.getObjValAs? String "var"
      let lo ← impExprFromJson (← sub.getObjVal? "lo")
      let hi ← impExprFromJson (← sub.getObjVal? "hi")
      let body ← impExprFromJson (← sub.getObjVal? "body")
      return .forLoop v lo hi body
    else if let .ok sub := j.getObjVal? "whileLoop" then
      let c ← impExprFromJson (← sub.getObjVal? "cond")
      let body ← impExprFromJson (← sub.getObjVal? "body")
      return .whileLoop c body
    else if let .ok bv := j.getObjVal? "break" then
      if bv.isNull then return .break_ none
      else return .break_ (some (← impExprFromJson bv))
    else if let .ok sub := j.getObjVal? "earlyReturn" then
      return .earlyReturn (← impExprFromJson sub)
    else if let .ok sub := j.getObjVal? "questionMark" then
      return .questionMark (← impExprFromJson sub)
    else if let .ok sub := j.getObjVal? "forFold" then
      let v ← sub.getObjValAs? String "var"
      let lo ← impExprFromJson (← sub.getObjVal? "lo")
      let hi ← impExprFromJson (← sub.getObjVal? "hi")
      let body ← impExprFromJson (← sub.getObjVal? "body")
      return .forFold v lo hi body
    else if let .ok sub := j.getObjVal? "whileFold" then
      let c ← impExprFromJson (← sub.getObjVal? "cond")
      let body ← impExprFromJson (← sub.getObjVal? "body")
      return .whileFold c body
    else if let .ok sub := j.getObjVal? "forFoldReturn" then
      let v ← sub.getObjValAs? String "var"
      let lo ← impExprFromJson (← sub.getObjVal? "lo")
      let hi ← impExprFromJson (← sub.getObjVal? "hi")
      let body ← impExprFromJson (← sub.getObjVal? "body")
      return .forFoldReturn v lo hi body
    else if let .ok sub := j.getObjVal? "whileFoldReturn" then
      let c ← impExprFromJson (← sub.getObjVal? "cond")
      let body ← impExprFromJson (← sub.getObjVal? "body")
      return .whileFoldReturn c body
    else if let .ok sub := j.getObjVal? "cfBreak" then
      return .cfBreak (← impExprFromJson sub)
    else if let .ok sub := j.getObjVal? "cfContinue" then
      return .cfContinue (← impExprFromJson sub)
    else if let .ok sub := j.getObjVal? "cfBreakContinue" then
      return .cfBreakContinue (← impExprFromJson sub)
    else throw s!"expected ImpExpr, got {j}"

instance : ToJson ImpExpr where toJson := impExprToJson
instance : FromJson ImpExpr where fromJson? := impExprFromJson

/-! ## TExpr / TExprKind -/

mutual
private partial def texprToJson : TExpr → Json
  | .mk kind ty => Json.mkObj [("kind", texprKindToJson kind), ("ty", toJson ty)]

private partial def texprKindToJson : TExprKind → Json
  | .lit v => Json.mkObj [("lit", toJson v)]
  | .var n => Json.mkObj [("var", Json.str n)]
  | .unitVal => Json.str "unitVal"
  | .continue_ => Json.str "continue"
  | .letBind n val body =>
    Json.mkObj [("letBind", Json.mkObj [("name", Json.str n),
      ("val", texprToJson val), ("body", texprToJson body)])]
  | .app f args =>
    Json.mkObj [("app", Json.mkObj [("f", Json.str f),
      ("args", Json.arr (args.map texprToJson).toArray)])]
  | .tuple elems =>
    Json.mkObj [("tuple", Json.arr (elems.map texprToJson).toArray)]
  | .proj e i =>
    Json.mkObj [("proj", Json.mkObj [("e", texprToJson e), ("i", toJson i)])]
  | .ifThenElse c t e =>
    Json.mkObj [("ifThenElse", Json.mkObj [
      ("cond", texprToJson c), ("thn", texprToJson t), ("els", texprToJson e)])]
  | .match_ scrut arms =>
    Json.mkObj [("match", Json.mkObj [
      ("scrut", texprToJson scrut),
      ("arms", Json.arr (arms.map fun (p, e) =>
        Json.mkObj [("pat", toJson p), ("body", texprToJson e)]).toArray)])]
  | .seq e1 e2 =>
    Json.mkObj [("seq", Json.mkObj [("e1", texprToJson e1), ("e2", texprToJson e2)])]
  | .borrow e => Json.mkObj [("borrow", texprToJson e)]
  | .deref e => Json.mkObj [("deref", texprToJson e)]
  | .assign n rhs =>
    Json.mkObj [("assign", Json.mkObj [("name", Json.str n), ("rhs", texprToJson rhs)])]
  | .forLoop v lo hi body =>
    Json.mkObj [("forLoop", Json.mkObj [("var", Json.str v),
      ("lo", texprToJson lo), ("hi", texprToJson hi), ("body", texprToJson body)])]
  | .whileLoop c body =>
    Json.mkObj [("whileLoop", Json.mkObj [
      ("cond", texprToJson c), ("body", texprToJson body)])]
  | .break_ none => Json.mkObj [("break", Json.null)]
  | .break_ (some e) => Json.mkObj [("break", texprToJson e)]
  | .earlyReturn e => Json.mkObj [("earlyReturn", texprToJson e)]
  | .questionMark e => Json.mkObj [("questionMark", texprToJson e)]
  | .forFold v lo hi body =>
    Json.mkObj [("forFold", Json.mkObj [("var", Json.str v),
      ("lo", texprToJson lo), ("hi", texprToJson hi), ("body", texprToJson body)])]
  | .whileFold c body =>
    Json.mkObj [("whileFold", Json.mkObj [
      ("cond", texprToJson c), ("body", texprToJson body)])]
  | .forFoldReturn v lo hi body =>
    Json.mkObj [("forFoldReturn", Json.mkObj [("var", Json.str v),
      ("lo", texprToJson lo), ("hi", texprToJson hi), ("body", texprToJson body)])]
  | .whileFoldReturn c body =>
    Json.mkObj [("whileFoldReturn", Json.mkObj [
      ("cond", texprToJson c), ("body", texprToJson body)])]
  | .cfBreak e => Json.mkObj [("cfBreak", texprToJson e)]
  | .cfContinue e => Json.mkObj [("cfContinue", texprToJson e)]
  | .cfBreakContinue e => Json.mkObj [("cfBreakContinue", texprToJson e)]
end

private partial def texprFromJson (j : Json) : Except String TExpr := do
  let kind ← texprKindFromJson (← j.getObjVal? "kind")
  let ty ← fromJson? (← j.getObjVal? "ty")
  return .mk kind ty
where
  texprKindFromJson (j : Json) : Except String TExprKind := do
    match j with
    | .str "unitVal" => return .unitVal
    | .str "continue" => return .continue_
    | _ =>
      if let .ok v := j.getObjValAs? ImpLit "lit" then return .lit v
      else if let .ok n := j.getObjValAs? String "var" then return .var n
      else if let .ok sub := j.getObjVal? "letBind" then
        let name ← sub.getObjValAs? String "name"
        let val ← texprFromJson (← sub.getObjVal? "val")
        let body ← texprFromJson (← sub.getObjVal? "body")
        return .letBind name val body
      else if let .ok sub := j.getObjVal? "app" then
        let f ← sub.getObjValAs? String "f"
        let args ← (← sub.getObjValAs? (Array Json) "args").toList.mapM texprFromJson
        return .app f args
      else if let .ok arr := j.getObjValAs? (Array Json) "tuple" then
        return .tuple (← arr.toList.mapM texprFromJson)
      else if let .ok sub := j.getObjVal? "proj" then
        let e ← texprFromJson (← sub.getObjVal? "e")
        let i ← sub.getObjValAs? Nat "i"
        return .proj e i
      else if let .ok sub := j.getObjVal? "ifThenElse" then
        let c ← texprFromJson (← sub.getObjVal? "cond")
        let t ← texprFromJson (← sub.getObjVal? "thn")
        let e ← texprFromJson (← sub.getObjVal? "els")
        return .ifThenElse c t e
      else if let .ok sub := j.getObjVal? "match" then
        let scrut ← texprFromJson (← sub.getObjVal? "scrut")
        let armsJ ← sub.getObjValAs? (Array Json) "arms"
        let arms ← armsJ.toList.mapM fun aj => do
          let p ← fromJson? (← aj.getObjVal? "pat")
          let body ← texprFromJson (← aj.getObjVal? "body")
          return (p, body)
        return .match_ scrut arms
      else if let .ok sub := j.getObjVal? "seq" then
        let e1 ← texprFromJson (← sub.getObjVal? "e1")
        let e2 ← texprFromJson (← sub.getObjVal? "e2")
        return .seq e1 e2
      else if let .ok sub := j.getObjVal? "borrow" then
        return .borrow (← texprFromJson sub)
      else if let .ok sub := j.getObjVal? "deref" then
        return .deref (← texprFromJson sub)
      else if let .ok sub := j.getObjVal? "assign" then
        let name ← sub.getObjValAs? String "name"
        let rhs ← texprFromJson (← sub.getObjVal? "rhs")
        return .assign name rhs
      else if let .ok sub := j.getObjVal? "forLoop" then
        let v ← sub.getObjValAs? String "var"
        let lo ← texprFromJson (← sub.getObjVal? "lo")
        let hi ← texprFromJson (← sub.getObjVal? "hi")
        let body ← texprFromJson (← sub.getObjVal? "body")
        return .forLoop v lo hi body
      else if let .ok sub := j.getObjVal? "whileLoop" then
        let c ← texprFromJson (← sub.getObjVal? "cond")
        let body ← texprFromJson (← sub.getObjVal? "body")
        return .whileLoop c body
      else if let .ok bv := j.getObjVal? "break" then
        if bv.isNull then return .break_ none
        else return .break_ (some (← texprFromJson bv))
      else if let .ok sub := j.getObjVal? "earlyReturn" then
        return .earlyReturn (← texprFromJson sub)
      else if let .ok sub := j.getObjVal? "questionMark" then
        return .questionMark (← texprFromJson sub)
      else if let .ok sub := j.getObjVal? "forFold" then
        let v ← sub.getObjValAs? String "var"
        let lo ← texprFromJson (← sub.getObjVal? "lo")
        let hi ← texprFromJson (← sub.getObjVal? "hi")
        let body ← texprFromJson (← sub.getObjVal? "body")
        return .forFold v lo hi body
      else if let .ok sub := j.getObjVal? "whileFold" then
        let c ← texprFromJson (← sub.getObjVal? "cond")
        let body ← texprFromJson (← sub.getObjVal? "body")
        return .whileFold c body
      else if let .ok sub := j.getObjVal? "forFoldReturn" then
        let v ← sub.getObjValAs? String "var"
        let lo ← texprFromJson (← sub.getObjVal? "lo")
        let hi ← texprFromJson (← sub.getObjVal? "hi")
        let body ← texprFromJson (← sub.getObjVal? "body")
        return .forFoldReturn v lo hi body
      else if let .ok sub := j.getObjVal? "whileFoldReturn" then
        let c ← texprFromJson (← sub.getObjVal? "cond")
        let body ← texprFromJson (← sub.getObjVal? "body")
        return .whileFoldReturn c body
      else if let .ok sub := j.getObjVal? "cfBreak" then
        return .cfBreak (← texprFromJson sub)
      else if let .ok sub := j.getObjVal? "cfContinue" then
        return .cfContinue (← texprFromJson sub)
      else if let .ok sub := j.getObjVal? "cfBreakContinue" then
        return .cfBreakContinue (← texprFromJson sub)
      else throw s!"expected TExprKind, got {j}"

instance : ToJson TExpr where toJson := texprToJson
instance : FromJson TExpr where fromJson? := texprFromJson
instance : ToJson TExprKind where toJson := texprKindToJson
instance : FromJson TExprKind where fromJson? j := texprFromJson.texprKindFromJson j

end SSProve.Hax
