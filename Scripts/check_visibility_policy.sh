#!/usr/bin/env bash
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"

fail=0

check_absent() {
  local label=$1
  local pattern=$2
  if rg -n "$pattern" --glob '*.lean' Mathling Tests; then
    printf 'visibility policy violation: %s\n' "$label" >&2
    fail=1
  fi
}

check_absent 'public section' '^\s*(public|@\[expose\]\s+public) section'
check_absent 'import all' '^\s*(public )?import all\b'
check_absent 'All umbrella import' '^\s*(public )?import Mathling\..*\.All\b'

is_designated_public_module() {
  case "$1" in
    Mathling.lean|Mathling/Meta.lean|Mathling/Meta/Important.lean|Mathling/Automata.lean|\
    Mathling/Automata/Core.lean|Mathling/Automata/Regex.lean|Mathling/Automata/Pushdown.lean|\
    Mathling/Automata/Regular.lean|Mathling/Automata/Regular/*.lean|\
    Mathling/Grammar.lean|Mathling/Grammar/Core.lean|Mathling/Grammar/ContextFree.lean|\
    Mathling/Grammar/Deterministic.lean|\
    Mathling/Grammar/Regular.lean|Mathling/Grammar/Regular/*.lean|Mathling/Grammar/Pushdown.lean|\
    Mathling/Grammar/NormalForms.lean|Mathling/Grammar/NormalForms/*.lean|Mathling/Grammar/Theory.lean|\
    Mathling/Lambek.lean|Mathling/Lambek/ProductFree.lean|\
    Mathling/Lambek/ProductFree/Calculus.lean|Mathling/Lambek/ProductFree/Decision.lean|\
    Mathling/Lambek/ProductFree/Fragments.lean|Mathling/Lambek/ProductFree/Fragments/*.lean|\
    Mathling/Lambek/ProductFree/Fragments/*/*.lean)
      return 0
      ;;
    *) return 1 ;;
  esac
}

while IFS=: read -r file line _; do
  if ! is_designated_public_module "$file"; then
    printf '%s:%s: public import is reserved for designated public modules\n' "$file" "$line" >&2
    fail=1
  fi
done < <(rg -n '^\s*public import ' --glob '*.lean' Mathling Tests || true)

while IFS=: read -r file line _; do
  start=$((line - 8))
  if (( start < 1 )); then start=1; fi
  if ! sed -n "${start},${line}p" "$file" | rg -q '([Ee]xpos|公開|reduc)'; then
    printf '%s:%s: @[expose] requires an adjacent justification\n' "$file" "$line" >&2
    fail=1
  fi
done < <(rg -n '@\[expose\]' --glob '*.lean' Mathling Tests || true)

exit "$fail"
