#!/usr/bin/env bash
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"

footer='<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->'

fail=0
mapfile -t files < <(printf '%s\n' Mathling.lean; rg --files Mathling Tests -g '*.lean' | sort)

for file in "${files[@]}"; do
  if ! rg -q '^    import LiterateLean$' "$file"; then
    printf '%s: missing direct LiterateLean import\n' "$file" >&2
    fail=1
  fi
  if ! rg -q '^    open scoped LiterateLean$' "$file"; then
    printf '%s: missing explicit LiterateLean scope\n' "$file" >&2
    fail=1
  fi
  if ! head -n 1 "$file" | rg -q '^    module$'; then
    printf '%s: executable header must be indented\n' "$file" >&2
    fail=1
  fi
  if [[ $(tail -n 6 "$file") != "$footer" ]]; then
    printf '%s: canonical LiterateLean footer is not final content\n' "$file" >&2
    fail=1
  fi
  if ! awk '
    /^```lean[[:space:]]*$/ { if (inside) exit 1; inside = 1; next }
    /^```[[:space:]]*$/ { if (!inside) exit 1; inside = 0; next }
    !inside && /^#+ / {
      level = match($0, /[^#]/) - 1
      if (level == 1) headings++
      if (previous && level > previous + 1) exit 1
      previous = level
    }
    END { exit inside || headings != 1 }
  ' "$file"; then
    printf '%s: malformed Lean fences or heading hierarchy\n' "$file" >&2
    fail=1
  fi
done

exit "$fail"
