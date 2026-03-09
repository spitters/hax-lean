#!/bin/bash
# Integration tests for haxpipe CLI
set -e
PASS=0
FAIL=0

run_test() {
  local name="$1"
  local input="$2"
  local flags="$3"
  local expected_exit="$4"

  if echo "$input" | lake env lean --run SSProve/Hax/Main.lean $flags > /dev/null 2>&1; then
    actual_exit=0
  else
    actual_exit=1
  fi

  if [ "$actual_exit" -eq "$expected_exit" ]; then
    echo "PASS: $name"
    PASS=$((PASS + 1))
  else
    echo "FAIL: $name (expected exit=$expected_exit, got exit=$actual_exit)"
    FAIL=$((FAIL + 1))
  fi
}

echo "=== haxpipe integration tests ==="

# Test 1: Simple variable
run_test "simple variable" '{"var": "x"}' "" 0

# Test 2: Literal integer
run_test "literal int" '{"lit": {"int": 42}}' "--emit-json" 0

# Test 3: Assignment (mutation → letBind)
run_test "mutation pipeline" \
  '{"assign": {"name": "x", "rhs": {"lit": {"int": 5}}}}' \
  "--emit-json" 0

# Test 4: Borrow/deref (dropReferences)
run_test "borrow deref" \
  '{"borrow": {"var": "x"}}' \
  "--emit-json" 0

# Test 5: Early return
run_test "early return" \
  '{"earlyReturn": {"var": "x"}}' \
  "--emit-json" 0

# Test 6: Extended pipeline
run_test "extended pipeline" \
  '{"var": "x"}' \
  "--emit-json --extended" 0

# Test 7: Help flag
run_test "help" '' "--help" 0

# Test 8: Lean output mode
run_test "lean output" \
  '{"ifThenElse": {"cond": {"var": "x"}, "thn": {"lit": {"int": 1}}, "els": {"lit": {"int": 0}}}}' \
  "--emit-lean" 0

echo ""
echo "=== Results: $PASS passed, $FAIL failed ==="
[ "$FAIL" -eq 0 ]
