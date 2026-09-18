#!/usr/bin/env bash
# Lists, for each module under HaxLean/Rust/ ported from the Aeneas `Std` library,
# the declaration names that appear only in the port and only in its source files.
#
# Usage: scripts/aeneas-port-drift.sh <aeneas-checkout>
#
# <aeneas-checkout> is a checkout of cryspen/aeneas (pinned commit in ATTRIBUTION):
# the repository root, its backends/lean/Aeneas directory, or its
# backends/lean/Aeneas/Std directory. Each ported file names its source files in
# its header, one per line, as `  backends/lean/Aeneas/<path>`.
#
# A declaration name is the identifier after def, theorem, lemma, abbrev,
# structure, inductive, class, instance, opaque, axiom or irreducible_def,
# with the scalar-family prefixes (uscalar, iscalar, scalar, uscalar_no_usize,
# iscalar_no_isize), attributes and modifiers stripped. Anonymous instances are
# not listed. Names are compared as written, relative to the enclosing namespace.
#
# Exit status: 0 when the comparison ran (differences are reported, not failed),
# 2 on a usage or path error.

set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <aeneas-checkout>" >&2
  exit 2
fi

arg=${1%/}
if [[ -f "$arg/backends/lean/Aeneas/Std/Primitives.lean" ]]; then
  aeneas="$arg/backends/lean/Aeneas"
elif [[ -f "$arg/Std/Primitives.lean" ]]; then
  aeneas="$arg"
elif [[ -f "$arg/Primitives.lean" && "$(basename "$arg")" == "Std" ]]; then
  aeneas="$(dirname "$arg")"
else
  echo "error: no Aeneas Std library under $arg" >&2
  exit 2
fi

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

decl_names() {
  sed -nE 's/^[[:space:]]*(((u|i)?scalar(_no_usize|_no_isize)?)[[:space:]]+)?(@\[.*\][[:space:]]*)?((private|protected|noncomputable|partial|unsafe|nonrec|public|meta)[[:space:]]+)*(def|theorem|lemma|abbrev|structure|inductive|class|instance|opaque|axiom|irreducible_def)[[:space:]]+//p' "$@" \
    | grep -oE '^[^][[:space:]:({]+' \
    | sort -u || true
}

total_port_only=0
total_fork_only=0
missing_sources=0

while IFS= read -r port; do
  mapfile -t rels < <(grep -oE '^  backends/lean/Aeneas/[^[:space:]]+\.lean' "$port" | sed -E 's/^  backends\/lean\/Aeneas\///')
  if [[ ${#rels[@]} -eq 0 ]]; then
    continue
  fi
  srcs=()
  for rel in "${rels[@]}"; do
    if [[ -f "$aeneas/$rel" ]]; then
      srcs+=("$aeneas/$rel")
    else
      echo "warning: $port names missing source backends/lean/Aeneas/$rel" >&2
      missing_sources=$((missing_sources + 1))
    fi
  done
  port_names=$(decl_names "$port")
  if [[ ${#srcs[@]} -gt 0 ]]; then
    fork_names=$(decl_names "${srcs[@]}")
  else
    fork_names=""
  fi
  only_port=$(comm -23 <(printf '%s\n' "$port_names" | sed '/^$/d') <(printf '%s\n' "$fork_names" | sed '/^$/d'))
  only_fork=$(comm -13 <(printf '%s\n' "$port_names" | sed '/^$/d') <(printf '%s\n' "$fork_names" | sed '/^$/d'))
  n_port=$(printf '%s' "$only_port" | grep -c . || true)
  n_fork=$(printf '%s' "$only_fork" | grep -c . || true)
  total_port_only=$((total_port_only + n_port))
  total_fork_only=$((total_fork_only + n_fork))
  echo "== $port  (sources: ${rels[*]})"
  echo "   only in port: $n_port"
  if [[ -n "$only_port" ]]; then printf '%s\n' "$only_port" | sed 's/^/     + /'; fi
  echo "   only in source: $n_fork"
  if [[ -n "$only_fork" ]]; then printf '%s\n' "$only_fork" | sed 's/^/     - /'; fi
done < <(find HaxLean/Rust.lean HaxLean/Rust -name '*.lean' | sort)

echo
echo "total only in port: $total_port_only"
echo "total only in source: $total_fork_only"
echo "missing source files: $missing_sources"
