#!/usr/bin/env bash
# Exercise the stated critical radius with a disposable challenge and the real solution.
set -euo pipefail
cd "$(dirname "$0")/.."
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT

# A failed build, an absent export or a kernel crash cannot pass this test.
sed 's/sInf {r : ℝ | Infinite (group r)} = radius/sSup {r : ℝ | Infinite (group r)} = radius/' \
  Comparator/Challenge.lean > "$scratch/Changed.lean"
if cmp -s Comparator/Challenge.lean "$scratch/Changed.lean"; then
  echo "The infimum mutation did not change the challenge." >&2
  exit 1
fi
lake env lean -R "$scratch" -o "$scratch/Changed.olean" "$scratch/Changed.lean"
lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec leanexport Changed -- \
  FiveDisk.critical_radius \
  propext Quot.sound Classical.choice' _ "$scratch" > "$scratch/challenge.ndjson"
status=0
lake comparator "$@" --challenge-from-export "$scratch/challenge.ndjson" > "$scratch/judge.log" 2>&1 || status=$?
if [[ $status != 1 ]] || ! grep -Fq "theorem statement do not match: 'FiveDisk.critical_radius'" "$scratch/judge.log"; then
  cat "$scratch/judge.log" >&2
  exit 1
fi
echo "Comparator rejected the changed infimum in FiveDisk.critical_radius."
