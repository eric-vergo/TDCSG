#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
# Passing no modules to the cache tool requests all of Mathlib.
modules=$(git grep -h -E '^(public |private |meta )*import Mathlib\.' -- '*.lean' |
  awk '{ for (i = 1; i <= NF; i++) if ($i ~ /^Mathlib\.[A-Za-z0-9_.]+$/) print $i }' | sort -u)
test -n "$modules"
echo "Direct Mathlib imports: $(wc -w <<< "$modules")"
# Each validated module name is a separate cache argument.
read -r -a roots <<< "$(tr '\n' ' ' <<< "$modules")"
MATHLIB_NO_CACHE_ON_UPDATE=1 lake exe cache get "${roots[@]}"
