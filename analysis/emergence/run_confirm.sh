#!/bin/zsh
# Confirm runner: 5 seeds x 7 sets, 7 concurrent.
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
for s in 910 911 912 913 914; do for k in mix c0 c1 c2 c3 c4 c5; do echo "$s $k"; done; done | \
  xargs -P 7 -n 2 sh -c '../../.venv/bin/python emerge.py confirm $0 $1 400 120 > confirm_$0_$1.log 2>&1'
../../.venv/bin/python emerge_score.py confirm 910 911 912 913 914 > confirm_score.log 2>&1
