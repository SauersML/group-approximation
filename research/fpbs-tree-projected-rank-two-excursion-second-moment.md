---
rg: 2
id: fpbs-tree-projected-rank-two-excursion-second-moment
kind: claim
title: A second moment over fibre-returning excursion paths gives strict thresholds for rank-two tree-projected Cayley graphs of F_2 x Z with many decorations per letter
distinct_from:
  fpbs-tree-projected-oriented-second-moment-thresholds: that runs Paley–Zygmund over paths that follow reduced words, which use 3m of the 4m decorated tree edges at a vertex, so p_o m -> 1/3 > 1/(2 sqrt 3) and rank two fails; this adds depth-one excursions that leave along a letter and return to the same fibre by a different decoration, which gives limit 0.2726 < 0.2887 and covers rank two for large m.
  fpbs-tree-projected-rigid-decorations-strict-thresholds: that is the open claim for every rigid decoration of every rank; this settles rank two when the multiplicity m is large (m >= 9 with v = 0, m >= 18 with v = 2, m >= max(40, 10v) in general), for all heights, rigid or not, and does not reach small m such as S_rig.
  fpbs-rigid-f2xz-certified-strict-thresholds: that certifies the single rank-two example S_rig (m = 3) by finite Galton–Watson and Schur certificates; this is uniform over all decoration heights, but only for large multiplicity.
  fpbs-rigid-congruence-class-uniform-strict-thresholds: that covers congruence classes of rank-two patterns by a cover-quotient sandwich; this uses no pattern and no quotient, only the multiplicity.
artifacts:
  - experiments/tree-projected-excursion-second-moment-2026-09-17/criterion.py
  - experiments/tree-projected-excursion-second-moment-2026-09-17/certify.py
  - experiments/tree-projected-excursion-second-moment-2026-09-17/blockcheck.py
  - experiments/tree-projected-excursion-second-moment-2026-09-17/pathcheck.py
  - experiments/tree-projected-excursion-second-moment-2026-09-17/scan.py
  - experiments/tree-projected-excursion-second-moment-2026-09-17/output.txt
---

**ESTABLISHED (2026-09-18, computer-assisted, unreviewed)** through
`fpbs-tree-projected-rank-two-excursion-second-moment-proof`.

**Statement.** Let `Gamma = F_2 x Z` with free basis `{a, b}`, and let `S` be a finite
symmetric generating set with `pi(S) ⊆ {1, a^±1, b^±1}`. Put
`D_t = {k : (t,k) in S}` for `t in {a,b}`, `m_t = |D_t|`, `m_lo = min m_t`,
`m_hi = max m_t`, and let `v = #{g in S : pi(g) = 1}`. The heights in `D_t` are
arbitrary: no rigidity and no pattern is assumed. Then on `Cay(Gamma,S)`:

1. **`p_c` bound.** If `m_lo >= 40`, then `p_c <= 7/(25 m_lo)`.
2. **Strict thresholds, uniform multiplicity `m_a = m_b = m`.** `p_c < p_u` holds when
   * `v = 0` and `m >= 9`;
   * `v = 2` and `m >= 18`;
   * `v` is arbitrary and `m >= max(40, 10 v)`.
3. **Mixed multiplicities.** `p_c < p_u` whenever `m_lo >= 40` and
   `7 (v + 2 sqrt(3) m_hi) < 25 m_lo`.

**New input: excursion paths.** The rank-two obstruction recorded in
`fpbs-tree-projected-oriented-second-moment-thresholds` is that word-following paths
use only `3m` of the `4m` decorated tree edges at a vertex. Here the path, before each
step, may make a depth-one excursion: it leaves the fibre along any letter `e` other
than the one it arrived by, with decoration `u`, and comes straight back along the same
tree edge with a different decoration `u' != u`. That lands on a new vertex of the
same fibre.
* Excursions use the backward-looking decorated edges that word-following paths
  never touch.
* Every path is a trail with pairwise distinct edges, so `P(open) = p^(#edges)`. It
  need not be self-avoiding.
* Paley–Zygmund is run over these paths. The pair correlations are controlled by a
  lumped `2 x 2` transfer matrix whose states are *same vertex* and *same fibre,
  different vertex*.
* The matrix entries are bounded symbolically. The script enumerates the 10 pair types
  of one block, and every set `Q` of candidate shared edges. It solves the linear
  height equations and counts solutions by `m^(components) (m-1)^(forest edges)` of an
  inequality graph.

At `p = c/m` the criterion is `rho(T) < 3 w^2`. It holds for `c > c(m)`, where
`c(m) -> 0.27258`. The limit is the root of `3(c + 3c^3) = 1`, the first-moment threshold
of the excursion ensemble itself, so the counting losses vanish as `m -> infinity`. The non-backtracking bound `p_u >= p* >= 1/(v + 2 sqrt(3) m)` from
`fpbs-tree-projected-oriented-second-moment-thresholds` gives `m p* -> 1/(2 sqrt 3) = 0.2887`.

**Certificate.** `certify.py` works in exact rational arithmetic.
* *Tail.* At `p = 7/(25m)` every quantity is a Laurent polynomial in `m`. The three
  inequalities `L > alpha`, `L > delta` and `(L-alpha)(L-delta) > beta gamma` hold
  for all `m >= 40`, by a coefficient bound.
* *Range.* For `3 <= m < 40` and `v in {0, 2}`, the criterion is checked at a
  rational `p <= p*(m,v)`. It fails exactly for `m <= 8` (`v = 0`) and `m <= 17`
  (`v = 2`).

**Where it stops.** Small multiplicity, including every `m <= 8` and the recorded
example `S_rig` (`m = 3`, `v = 2`).
* At `m = 3` the criterion needs `c >= 0.373`, while `m p* = 0.267`.
* The losses are the counting bound, the one-excursion-per-slot ensemble and the
  missing torsion refinement for returns from a nonzero offset.
* For large `m` the ensemble's own limit `0.27258` is the barrier. Lowering it needs a
  richer ensemble, e.g. several excursions per slot, which gives first-moment limit
  `(sqrt 21 - 3)/6 = 0.2638`.

`S_rig` itself is certified separately in `fpbs-rigid-f2xz-certified-strict-thresholds`.
