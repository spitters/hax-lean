import Hax.SemanticsCF
import Hax.Phase.FunctionalizeLoops
import Hax.Phase.CfIntoMonads

namespace Hax.TestNested

-- Test: for i in 0..3 { if i == 1 { return 42; } break 0; }
-- Expected: at i=0, body hits break 0 → loop breaks with value 0
-- Then the outer expression would continue with result 0.
-- (earlyReturn is never reached because i starts at 0, not 1)

def loopWithBreakAndReturn : ImpExpr :=
  .forLoop "i" (.lit (.int 0)) (.lit (.int 3))
    (.ifThenElse (.app "eq" [.var "i", .lit (.int 1)])
      (.earlyReturn (.lit (.int 42)))
      (.break_ (some (.lit (.int 0)))))

-- Phase 3 output
#eval functionalizeLoops loopWithBreakAndReturn

-- Phase 4 output
#eval cfIntoMonads (functionalizeLoops loopWithBreakAndReturn)

-- run' helper using denote'
def run' (fuel : Nat) (bindings : List (String × Value)) (e : ImpExpr) : Outcome :=
  let env := bindings.foldl (fun acc (n, v) => acc.extend n v) Env.empty
  (denote' defaultBuiltins fuel e env).1

-- Original semantics (denote): at i=0, eq(0,1)=false → break 0 → val 0
def runOrig (fuel : Nat) (bindings : List (String × Value)) (e : ImpExpr) : Outcome :=
  let env := bindings.foldl (fun acc (n, v) => acc.extend n v) Env.empty
  (denote defaultBuiltins fuel e env).1

#eval runOrig 100 [] loopWithBreakAndReturn
-- Expected: Outcome.val (Value.int 0)

-- After Phase 3+4 pipeline under denote':
#eval run' 100 [] (cfIntoMonads (functionalizeLoops loopWithBreakAndReturn))
-- If passthrough bug: break is misinterpreted as continue → wrong result
-- If fixed: should give val(controlFlow true (int 0)) which is encodeCF of val 0

-- Also test: the Phase 3 output (before Phase 4) under denote'
#eval run' 100 [] (functionalizeLoops loopWithBreakAndReturn)
-- Should propagate earlyRet? Or break? At i=0, break 0 → loop breaks.

end Hax.TestNested
