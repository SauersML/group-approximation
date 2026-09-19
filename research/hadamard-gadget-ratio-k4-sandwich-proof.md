---
rg: 2
id: hadamard-gadget-ratio-k4-sandwich-proof
kind: route
title: Import Wiman's Had_4 gadget value from Martinsson for the lower bound, and certify the upper bound by an exact-rational group-symmetrized mixture of 35 explicit folded columns
target: hadamard-gadget-ratio-k4-sandwich
requires:
  - hadamard-gadget-deletion-ratio-window
artifacts:
  - experiments/ugc-hadamard-gadget-k4-2026-09-17/hadk_fold_ub2.py
  - experiments/ugc-hadamard-gadget-k4-2026-09-17/fold_ub2_k4_run1.log
  - experiments/ugc-hadamard-gadget-k4-2026-09-17/verify_certificate.py
  - experiments/ugc-hadamard-gadget-k4-2026-09-17/verify_k4.log
  - experiments/ugc-hadamard-gadget-k4-2026-09-17/results-2026-09-19.txt
---

## Imports

* **Martinsson (arXiv:2408.04832), verbatim.** "Wiman's Max-Had 4 gadget
  has c = 15/16 and s = 3308625759/3640066048 ≈ 0.9089".
  * Wiman's soundness is relaxed, and relaxed soundness is at least the true
    soundness, so this is a valid `(c, s)`-gadget in the sense of HHM+15
    Definition 2.24.
  * Its deletion ratio is `(1 - s)/(1 - c) = 331440289/227504128`.
  * Hence `R*(4) >= 331440289/227504128`.
* **Minimax identity.** `R*(k) = K z*(P)` is item 1 of
  `hadamard-gadget-deletion-ratio-window`.

## Upper bound

1. **Columns.** `hadk_fold_ub2.py 4 W 300 8 6` runs with `W` as in
   `results-2026-09-19.txt`. It outputs a finite list of assignments
   `f : Q -> {-1,1}`, each checked in code to be folded and pinned at its
   pattern-orbit representative.
2. **Weights.** It gives each column a rational weight. The weights on each
   pattern orbit `q` sum to exactly `|q|/2^16`.
3. **Symmetrization.** Averaging each column over the symmetry group
   (affine maps of `F_2^4`, and negation) gives a folded distribution. Its
   pattern law puts mass `|q|/2^16` on each pattern orbit, uniformly within
   the orbit by orbit-stabilizer. So it is random on `P`.
4. **Evaluation.** Its cut probability is constant on each of the 23 edge
   orbits and equals `sum_c p_c cnt_c(o)/|o|`, computed in exact rationals.
   The maximum of these, times 16, is printed on the `exact:` line of
   `fold_ub2_k4_run1.log`, as `~ 1.534726256`.
5. By the minimax identity, `R*(4) <= 1.534726256...`.
