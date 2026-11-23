#!/usr/bin/env bash
# Run Comparator on two disposable mutations of the challenge against the real solution.
# Each run must be rejected with the expected judgment.
set -euo pipefail
cd "$(dirname "$0")/.."
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT

# Usage: expect_rejection NAME SED_SCRIPT EXPECTED_MESSAGE [COMPARATOR_ARGS...]
# A failed build, an absent export or a kernel crash cannot pass this test.
expect_rejection() {
  local name=$1 script=$2 expected=$3
  shift 3
  local dir="$scratch/$name"
  mkdir "$dir"
  sed "$script" Comparator/Challenge.lean > "$dir/Changed.lean"
  if cmp -s Comparator/Challenge.lean "$dir/Changed.lean"; then
    echo "The $name mutation did not change the challenge." >&2
    exit 1
  fi
  lake env lean -R "$dir" -o "$dir/Changed.olean" "$dir/Changed.lean"
  lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec leanexport Changed -- \
    FiveDisk.finite_iff \
    propext Quot.sound Classical.choice' _ "$dir" > "$dir/challenge.ndjson"
  local status=0
  lake comparator "$@" --challenge-from-export "$dir/challenge.ndjson" > "$dir/judge.log" 2>&1 \
    || status=$?
  if [[ $status != 1 ]] || ! grep -Fq "$expected" "$dir/judge.log"; then
    cat "$dir/judge.log" >&2
    exit 1
  fi
}

# The statement: the threshold itself would belong to the finite range.
expect_rejection endpoint 's/Finite (group r) ↔ r < radius/Finite (group r) ↔ r ≤ radius/' \
  "Challenge and solution theorem statement do not match: 'FiveDisk.finite_iff'" "$@"
echo "Comparator rejected the non-strict inequality in FiveDisk.finite_iff."

# A definition the statement uses: the challenge's threshold differs from the solution's copy.
expect_rejection radius 's/radius : ℝ := √(3 + (1 + √5) \/ 2)/radius : ℝ := √(4 + (1 + √5) \/ 2)/' \
  "Const does not match between challenge and target 'FiveDisk.radius'" "$@"
echo "Comparator rejected the changed definition of FiveDisk.radius."
