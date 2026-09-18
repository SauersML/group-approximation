---
rg: 2
id: fpbs-connectivity-polynomials-zero-free-around-criticality
kind: claim
title: Every nonamenable Cayley graph has zero-free, exponentially bounded connection polynomials on a domain around p_c
distinct_from:
  fpbs-pivotal-budget-universal: that is a real-variable pivotal bound on [p_c,p_0]; this is a complex zero-free region with growth control that may avoid p_c, and it forces a flat rate, which the budget does not
  fpbs-integrated-sensitivity-universal: that locates integrated sensitivity in real parameter; this is an analytic continuation statement about the finite connection polynomials
artifacts:
  - research/artifacts/fpbs-zero-free-connectivity-2026-09-17.md
  - experiments/fpbs-zero-free-2026-09-17/tree_walk_connectivity_zeros.py
  - research/artifacts/fpbs-zg-ladder-calibration-2026-09-17.md
  - experiments/fpbs-zg-ladder-zeros-2026-09-17/ladder_connectivity.py
  - experiments/fpbs-zg-ladder-zeros-2026-09-17/zeros.py
  - experiments/fpbs-zg-ladder-zeros-2026-09-17/pinch.py
  - experiments/fpbs-zg-ladder-zeros-2026-09-17/t3_disc.py
---

OPEN research hypothesis (ZG). Every nonamenable Cayley graph `G` has a simply
connected domain `U` in `C`, open intervals `I_-` in `(0,p_c]` and `I_+` in
`(p_c,1)` contained in `U`, and constants `M`, `n_0`, such that for all
`n>=n_0` and `R>=n` the walk-averaged connection polynomial `a_(n,R)(z)` has
no zero in `U` (Z) and satisfies `|a_(n,R)| <= exp(M n)` on `U` (G).

With `fpbs-zero-free-connectivity-gives-flat-rate` it gives
`fpbs-benjamini-schramm-universal`.

Status of evidence (Sections 3 and 4 of the artifact):

- On `T_d`, (G) holds with `M=0` on `|z|<=1`. (Z) on a disc about `p_c` is
  supported numerically only: for `T_3` and `n<=200`, `a_n` has no zero in
  `|z-1/2|<0.25`.
- Necessary consequences: a flat rate `lambda=rho` just past `p_c` (N1); fixed-n
  analytic continuation of `a_n` around `p_c` (N2); growth control uniform
  in `R` (N3). The parallel-routes toy `1-(1-z^L)^(2^L)` stays in `[0,1]` on
  the real axis but grows without bound off it, with zeros entering a fixed
  disc about `1/2` at `L=16`. So (G) needs cancellation among overlapping
  routes.
- First killing test: exact `a_(n,R)(z)` for small `n` and growing `R` on a
  small nonamenable Cayley graph with overlapping cycles.

## Attempts

* **First killing test on the cycle-rich Cayley graph `T_3 box K_2`**
  (swarm-0917-w8-w8-bs-break, calibration, 2026-09-17;
  `research/artifacts/fpbs-zg-ladder-calibration-2026-09-17.md`).
  **Survives, and is recalibrated.**

  The method is an exact two-terminal gadget and transfer-matrix reduction.
  It was checked against exhaustive enumeration of `B_2` and against Monte
  Carlo on `B_5`. It gives `a_(n,R)(z)` exactly for complex `z`, with
  `p_c = 0.38055` and `p_2 = 0.52620`.

  Results:
  * (Z) and (G) hold on `|z - p_c| < 0.13`: there are no zeros, and
    `max |a|^(1/n) < 0.951`. This holds for `n <= 400` and
    `R in {n, n+1, 2n, 8n}`, and does not depend on `R`.
  * Uniformity of (G) in `R` confines `U` to the bounded-orbit set of the
    gadget map `g -> 1-(1-z)(1-z^2 g)^2`. Here that set contains
    `|Im z| < 0.43` over `[-0.2, 1.2]`.
  * The zeros pinch the real axis at the l2 point `p_2`, not at `p_c`. The
    lowest zero sits near `Re z = 0.55`, and its height behaves like `n^(-1/2)`
    (`0.17`, `0.12`, `0.08` at `n = 200`, `400`, `800`).
  * A pinch lemma, using the same Vitali argument as the conditional theorem,
    forces (Z) or (G) to fail in every disc about `p_* = sup{lambda = rho}`.
    So `I_+` must lie in `(p_c, p_*)`.
  * On this graph and on `T_d`, `p_* = p_2`.

  **Correction to the evidence above.** The disc `|z-1/2| < 0.25` on `T_3`
  contains `p_* = 1/sqrt 2`. Exact counts give 2 zeros inside it at `n = 1600`
  and 4 at `n = 3200` (`t3_disc.py`). So the `n <= 200` reading was a
  transient. Valid evidence discs must avoid `p_*`. On `T_3`,
  `|z-1/2| < 0.18` stays zero-free.

  **Where it stops.** No counterexample was found. The test only shows that
  (ZG) carries no content beyond `p_c < p_*`. That content is reduced to
  `p_c < p_2` by the new hypothesis `fpbs-flat-rate-point-equals-l2-point`,
  which is OPEN, with one direction imported. A real kill would need a graph
  on which bounded-orbit loci or zeros approach `(p_c, p_*)` itself. Tree-graded
  graphs cannot supply one, because there the gadget maps contract near the
  real axis. The remaining candidates are one-ended graphs such as
  `T_3 box Z` and `F_2 x F_2`. On them the finite-volume clusters touching
  `B_R` enter (G) with no small-cluster expansion, so uniformity in `R` needs
  genuine cancellation. That case is untested.
