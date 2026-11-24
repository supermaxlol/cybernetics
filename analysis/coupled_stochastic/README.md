# Coupled stochastic viability — file index

Pre-registered confirmatory run. Results write-up:
[`RESULTS_stochastic_2026-11-24.md`](RESULTS_stochastic_2026-11-24.md).

## Frozen inputs (read-only, hashes in `FROZEN_stochastic.sha256`)

| File | Role |
|---|---|
| `PREREG_stochastic_2026-11-23.md` | hypotheses, pass rules, limits; frozen 2026-11-23 09:55 UTC |
| `stoch_sim.py` | simulator (`selftest`, `dev`, `confirm` modes) |
| `analyze.py` | scores the raw output into `stoch_{mode}_results.json` |
| `indep_sim.py` | independent scalar re-implementation (H14 identity check) |
| `real_env.py` | FRED VIXCLS / DTWEXBGS transfer tests (H13a–d) |

The freeze is local-only. `shasum -a 256 -c FROZEN_stochastic.sha256` must print five OK
lines (the trailing timestamp line is not a hash and warns as malformed).

## Dev artefacts (seed base 1000, 200 environments, 2026-11-23)

- `stoch_dev_raw.json`, `stoch_dev_results.json`, `indep_dev.json`, `real_dev.json`
- `dev_run2.log` — stdout of an earlier scoring pass; its H6/H9/H10b/H11/H12 lines **do
  not** match the final dev JSON and are not the dev baseline. The JSON is reproducible
  from the raw file with the frozen `analyze.py` (verified: zero differing values).
- `dev_run.log` — aborted first attempt.

## Confirm artefacts (seed base 2000, 600 environments, 2026-11-24)

- `stoch_confirm_raw.json` (3.3 MB), `stoch_confirm_results.json`,
  `indep_confirm.json`, `real_confirm.json`
- `confirm_run.log` — stdout; `scaling done 95118s`, `pop done 95219s`
- Runtime 26 h 27 m on this machine (8 GB RAM, heavy swap). The scaling grid prints no
  progress by design; silence in that log is not a hang.

## Reproduce

```
cd /Users/shehzad/Desktop/five-organ-theory/analysis/coupled_stochastic
P=/Users/shehzad/Desktop/five-organ-theory/.venv/bin/python
$P stoch_sim.py confirm     # 26 h
$P analyze.py confirm
$P indep_sim.py confirm
$P real_env.py confirm
```

The system `python3` lacks numpy and radcad; use the venv interpreter. Scored outcome: 16 of
21 hypothesis rows (18 of 23 criteria) pass; see the results document for the five failures
and what they change.
