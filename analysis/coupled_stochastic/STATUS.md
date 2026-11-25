# Status (2026-11-24)

The confirm run completed on 2026-11-24 (95,219 s). The frozen protocol, the dev outputs and
the confirm outputs are all here; `RESULTS_stochastic_2026-11-24.md` reports the scored
outcome.

Headline (corrected 2026-11-25): 16 of 21 hypothesis rows pass; "18 of 23 scored criteria" splits
two passing rows. H6 (Memory×Watcher) passes. H13a failed in dev and passed in confirm, so it did not
replicate. H7 and H8's latency trend failed again. H4b failed: all six ρ = 0.8 ratios are 0.719-0.787.
H10a failed, and its correlation comes wholly from χ = 0.8. H12 failed its pass rule; it is not shown to be reversed
(difference −0.058, bootstrap 95% interval [−0.120, +0.001], Mann-Whitney p = 0.20).
The corrections are at the top of `RESULTS_stochastic_2026-11-24.md`.

The confirm outputs are the confirmatory evidence. The dev outputs informed the thresholds
and are not.

The freeze is local-only: ordering rests on the hashes in `FROZEN_stochastic.sha256`, not on
a third-party timestamp.
