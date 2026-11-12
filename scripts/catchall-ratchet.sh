#!/usr/bin/env bash
# Catch-all ratchet of the typed hax adapter: the fallback arms and defaults of
# HaxAdapter, CertifiedTExprs, ClassEmit and ContractEmit against the shrink-only
# baseline scripts/catchall-baseline.tsv (see scripts/catchall_ratchet.py).
set -euo pipefail
exec python3 "$(dirname "$0")/catchall_ratchet.py" "$@"
