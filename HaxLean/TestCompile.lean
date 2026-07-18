/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import HaxLean.Runtime

/-!
# Compilation Test for Generated Code

This file imports ONLY `Hax.Runtime` and contains definitions
matching the output of `haxpipe --emit-lean --extended`. If this file
compiles, the runtime is sufficient for generated code.
-/

-- Simple let-binding (from: let x = 42; x)
def simpleLet :=
  let x := (42 : Int)
  x

#eval simpleLet  -- 42

-- Mutation pattern (from: let mut x = 0; x = 5; x)
def simpleMut :=
  let x := (0 : Int)
  let x := (5 : Int)
  x

#eval simpleMut  -- 5

-- Arithmetic via builtins
def arithTest :=
  let a := (10 : Int)
  let b := (3 : Int)
  let sum := Hax.add a b
  let diff := Hax.sub a b
  let prod := Hax.mul a b
  (sum, diff, prod)

#eval arithTest  -- (13, 7, 30)

-- Capitalized builtins (hax adapter output)
def arithTestCap :=
  Hax.Add (Hax.Mul 3 4) (Hax.Neg 1)

#eval (arithTestCap : Int)  -- 11

-- Comparison and boolean
def compTest :=
  let x := (5 : Int)
  if Hax.gt x 3 then
    Hax.add x 1
  else
    0

#eval compTest  -- 6

-- For-fold (from: for i in 0..5 { acc += i })
def sumRange (n : Int) : ControlFlow Int Int :=
  Hax.forFold 0 n 0 fun i acc =>
    ControlFlow.Continue (Hax.add acc i)

#eval sumRange 5   -- ControlFlow.Continue 10
#eval sumRange 10  -- ControlFlow.Continue 45

-- For-fold with break
def sumUntil : ControlFlow Int Int :=
  Hax.forFold 0 10 0 fun i acc =>
    if Hax.gt i 5 then
      ControlFlow.Break acc
    else
      ControlFlow.Continue (Hax.add acc i)

#eval sumUntil  -- ControlFlow.Break 15

-- While-fold (from: while x > 0 { x -= 1 })
def countdown (start : Int) : ControlFlow Int Int :=
  Hax.whileFold start (fun x => Hax.gt x 0) fun x =>
    ControlFlow.Continue (Hax.sub x 1)

#eval countdown 5  -- ControlFlow.Continue 0

-- Match expression
def matchTest (x : Int) : Int :=
  match Hax.beq x 0 with
  | true => 100
  | false => Hax.add x 1

#eval matchTest 0  -- 100
#eval matchTest 5  -- 6

-- Nested ControlFlow (early return inside loop)
def earlyReturnLoop : ControlFlow Int (ControlFlow Int Int) :=
  Hax.forFoldReturn 0 10 0 fun i acc =>
    if Hax.gt acc 15 then
      ControlFlow.Break (ControlFlow.Break acc)  -- early return
    else
      ControlFlow.Continue (Hax.add acc i)

#eval earlyReturnLoop  -- ControlFlow.Break 21

-- Option constructors
def optionTest (x : Int) : Option Int :=
  if Hax.gt x 0 then
    some x
  else
    none

#eval optionTest 5  -- some 5
#eval optionTest 0  -- none

-- Result constructors
def resultTest (x : Int) : Except String Int :=
  if Hax.ge x 0 then
    Except.ok x
  else
    Except.error "negative"

#eval resultTest 5    -- Except.ok 5
#eval resultTest (-1) -- Except.error "negative"
