---
rg: 2
id: fpbs-mal-depth-floor-from-overfold-domination
kind: route
title: The Bernoulli floor follows from two finite statements, that overfold merges never help (deep_j = law_j) and that some profinite towers keep a uniform 2-of-3 seed density on their phi^j-twisted levels
target: fpbs-mal-bernoulli-single-stage-floor
requires:
  - fpbs-mal-floor-iff-deep-promotion-floor
  - fpbs-mal-promotion-cost-monotone-under-weak-containment
  - fpbs-mal-depth-promotion-equals-overfold-merge-number
  - fpbs-mal-overfold-merges-never-help
  - fpbs-mal-twisted-level-seed-density-uniform-witness
artifacts:
  - experiments/fpbs-depth-overfolding-2026-09-17/exact_search.py
  - experiments/fpbs-depth-overfolding-2026-09-17/law_by_depth_n120.txt
---

Notation is as in [[fpbs-mal-depth-promotion-equals-overfold-merge-number]].
`ρ` is the Bernoulli shift of `L`.

1. By [[fpbs-mal-floor-iff-deep-promotion-floor]], the target holds iff
   `inf_j Q_j(ρ) > 0`.
2. Fix `j`. Let `X_j = lim Q_m` be the witness of
   [[fpbs-mal-twisted-level-seed-density-uniform-witness]]. It is
   essentially free, profinite, with transitive levels, and has
   `r(Q_m^{(j)}) ≥ c|Q_m|`.
3. By the depth costs of
   [[fpbs-mal-promotion-cost-monotone-under-weak-containment]],
   `Q_j(c') ≤ Q_j(ρ)` for every free action `c'`. So `Q_j(ρ) ≥ Q_j(X_j)`.
4. By item 4 of [[fpbs-mal-depth-promotion-equals-overfold-merge-number]],
   `Q_j(X_j) = inf_m deep_j(Q_m)/|Q_m|`.
5. By [[fpbs-mal-overfold-merges-never-help]], `deep_j(Q_m) = law_j(Q_m)`.
   By item 2 of the depth node, `law_j(Q_m) = r(Q_m^{(j)})`.
   So `Q_j(X_j) = inf_m r(Q_m^{(j)})/|Q_m| ≥ c`.
6. So `Q_j(ρ) ≥ c` for every `j` (for `j = 0` this is (D0), already known).
   By step 1, the target holds. ∎

**Where it can fail.**
- The weak form `deep_j ≥ c_1 · law_j` of the second input suffices, with
  the constant `c · c_1`.
- Either input can fail independently.
  - If overfold merges save a factor that grows with `j`, then step 5
    fails.
  - If every tower's twisted densities decay in `j`, then step 2 fails.
- A failure of either input does not refute the target. Overfold savings
  could be offset by denser witnesses, and conversely.

**Downstream.** With `fpbs-mal-floor-gives-fixed-price-counterexample`, this
is a complete route to `fpbs-fixed-price-counterexample-exists`. Its only
open premises are the two finite statements above.
