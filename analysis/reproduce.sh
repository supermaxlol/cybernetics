#!/bin/sh
# Verify the frozen pre-registered files, then run the self-tests (fast) or every confirm run.
# Usage: sh reproduce.sh          # hash checks + self-tests (about a minute)
#        sh reproduce.sh full     # also re-run every confirm experiment (over an hour on a laptop;
#                                 # overwrites the committed *_confirm_* outputs with fresh ones)
set -e
cd "$(dirname "$0")"
PY=${PYTHON:-python3}
echo "== frozen-file hashes"
for d in coupled_stochastic coevolution; do
  (cd "$d" && grep -E '^[0-9a-f]{64} ' FROZEN_*.sha256 | shasum -a 256 -c -)
done
echo "== self-tests"
$PY coupled_stochastic/stoch_sim.py selftest
$PY coevolution/coevo_sim.py selftest
if [ "$1" = "full" ]; then
  echo "== confirm runs"
  (cd coupled && $PY coupled_sim.py confirm && $PY coupled_ext.py confirm)
  (cd coupled_stochastic && $PY stoch_sim.py confirm && $PY analyze.py confirm && $PY indep_sim.py confirm)
  $PY fetch_fred.py && $PY run_real.py confirm
  (cd coevolution && $PY coevo_sim.py confirm && $PY coevo_analyze.py confirm)
fi
echo "OK"
