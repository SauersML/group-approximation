---
rg: 2
id: s0-lift-affine-box-left-inverse-census-proof
kind: route
title: Enumerate the affine box, solve every slice exactly over F_3, and re-verify each dual functional from a fresh registry
target: s0-lift-affine-box-has-no-small-left-inverse
requires: []
artifacts:
  - research/artifacts/gk3-ternary-bilinear-2026-09-14.md
  - experiments/gottschalk-ternary-corner/bscreen.py
  - experiments/gottschalk-ternary-corner/runs-bilinear/summary.json
---

For fixed `lambda` the system `beta alpha = eps_- + n` is linear in `(beta, n)`. `bscreen.py --mode exhaust --family mix2
--lift-radius 2 --radius 3` enumerates all `3^9 = 19683` values of `lambda` in 16 contiguous shards (MSI job array
792373, tasks 0–15) and solves each slice by sparse elimination over `F_3`. Result: 0 SAT, 19683 UNSAT, every
functional verified, 0 unverified; about 8272 CPU seconds.

- **UNSAT certificate.** Every UNSAT slice produces a functional `phi` on the product keys with `phi([1]) != 0`. It
  kills `[c] alpha` for every `c` in the support and `[p] - 1` for every `p` in `P`, so no combination of the
  columns equals `[1]`.
- **Independent check.** Each `phi` is re-checked by recomputing every column from a fresh unit registry
  (`pscreen.verify_dual_certificate`). Products in the registry come from the normal form of
  `experiments/gottschalk-ternary-corner/tleavitt.py`, whose second computation path agreed on 466 products
  (self-test, job 784314).
- **Nonvacuity.** `pi(alpha) = s0` for every `lambda`, and the evaluated system `beta' s0 = 1 + n'` is solvable over
  `pi(span C_3)` (`image_feasible_alpha0 = true`), so no slice is UNSAT for the trivial reason that the support
  carries no left inverse of `s0` even in `R`.
- **Controls.** They pass at the start of every job (artifact §2.3).
  - K1: a planted solution is found at exactly the planted `lambda`.
  - K2: `alpha0 = e_-`, whose image has no left inverse, gives UNSAT on every slice with verified functionals.

Counts: artifact §3 and `experiments/gottschalk-ternary-corner/runs-bilinear/summary.json`.
