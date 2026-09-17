---
rg: 2
id: fpbs-expander-approximant-giant-data-is-glued
kind: claim
title: Giant-component data of expander approximants sees only the glued connectivity law
distinct_from:
  fpbs-msf-excess-equals-nonuniqueness: that node is the infinite-volume identity between the free-minus-wired forest excess and the integrated distinct-infinite-cluster probability; this one proves that finite large-set expander approximants reproduce that integrand only through a two-scale limit, and that every bounded-separation giant or connectivity observable of the approximants converges to the glued law, so finite giant-window statements carry no information about p_u
  fpbs-bs-iff-finite-relative-susceptibility: that is an infinite-volume susceptibility criterion; this one concerns limits of percolation on finite expander graphs converging locally to the Cayley graph
artifacts:
  - research/fpbs-expander-approximant-giant-data-is-glued-proof.md
  - experiments/expander-glued-giant-2026-09-17/rrg_glued_calibration.py
  - experiments/expander-glued-giant-2026-09-17/output-n200000-R4-seed1.txt
---

**Obstruction (class-killing, for finite giant-component approaches).** Let
`G = Cay(Gamma,S)` be nonamenable, and let `G_n` be finite graphs (possibly
random) with maximum degree at most `D`, forming a large-set expander sequence
in the sense of Alimohammadi--Borgs--Saberi (arXiv:2103.09952), and converging
locally in probability to `G`. Write `o_n` for a uniform vertex of `G_n`, `C_i`
for the `i`th largest cluster of Bernoulli(`p`) bond percolation `omega` on
`G_n`, `zeta(p) = P_G(|C(o)| = infinity)`, and `L_R(x,y)` for the event that
`x` and `y` are joined by an open path inside `B_R(x)`.

* **(A) The giant uniqueness window is empty.** For every `p` in `[0,1]`,
  `|C_2|/n -> 0` in probability (ABS Theorem 1.1). So no statement of the form
  "two linear giants coexist on the approximants for some `p`" is available,
  whatever the value of `p_u(G)`. Calibration: random 3-regular graphs converge
  to `T_3`, where `p_c = 1/2 < p_u = 1`, and the second giant still vanishes at
  every `p`.
* **(B) Finite connectivity converges to the glued law.** For `p != p_c(G)` and
  every fixed `r`,
  `E sum_{y in B_r(o_n)} 1{o_n <-> y in G_n(p)}  ->  sum_{y in B_r(o)} P_G(o <-> y, or |C(o)| = |C(y)| = infinity)`.
  The finite two-point function identifies two vertices whenever both lie in
  infinite clusters. It is therefore the uniqueness-phase kernel even when `G`
  is in its nonuniqueness phase.
* **(C) Corollary: finite minimal spanning forests see the wired forest.** For
  iid uniform labels, `E deg_{MSF(G_n)}(o_n) -> E deg_WMSF(o) = 2`. The
  free-forest excess `delta_G` of `fpbs-msf-excess-equals-nonuniqueness` does
  not appear in the limit.
* **(D) The only surviving finite observable is a two-scale defect, and it is
  exactly the known reformulation.** Put
  `s_n(p,R) = E sum_{y ~ o_n} 1{o_n y closed, o_n <-> y, not L_R(o_n,y)}`.
  Then `lim_{R->inf} limsup_n s_n(p,R) = lim_{R->inf} liminf_n s_n(p,R) = (1-p) sum_{e=oy} P_G(o, y lie in distinct infinite clusters of omega minus e) =: (1-p) Delta(p)`,
  and `Delta(p) > 0` if and only if `G(p)` has at least two infinite clusters
  with positive probability. Integrating over `p` gives
  `delta_G = (1/2) integral_0^1 Delta(p) dp`. So a finite-approximant proof of
  `p_c < p_u` must bound this two-scale defect from below. That task is the
  same as bounding the integrand of `fpbs-msf-excess-equals-nonuniqueness`,
  with an extra limit to exchange, so it is an equivalence and not a
  simplification.

**Exact failing steps.** A "finite uniqueness window whose limit gives
`p_c < p_u`" fails at (A): the window is identically empty. A "finite
connectivity or MST estimate passing to the limit" fails at (B)/(C): the limit
is the glued/wired law, in which pairs of infinite clusters are merged. Only the
order-sensitive defect (D) sees `p_u`. Taking `R_n -> infinity` together with
`n` does not help, because `s_n(p,R) = 0` once `R` exceeds the diameter of
`G_n`. The defect is exactly the free-minus-wired integrand, so this whole
scale shift adds no estimate.

**Hypotheses.** The approximants must be large-set expanders. Their existence
is known in many cases, for example free groups via random Schreier graphs and
residually finite Kazhdan groups via finite quotients, but it is not known for
every nonamenable group. For groups without such approximants, this family of
approaches is vacuous rather than refuted.

Calibration script `rrg_glued_calibration.py` (random 3-regular graph,
`n = 200000`, `R = 4`) matches the `T_3` predictions. At `p = 0.7` it gives
`c2 = 0.0001`, glued sum `2.7058` (predicted `2.6998`), ungluded sum `3p = 2.1`,
and defect `s_R = 0.6035` (predicted `3(1-p) eta^2 = 0.5998`).

Status records a written proof from the imported ABS Theorem 1.1 and the
imported Lyons--Peres--Schramm forest identity. It is not independent referee
validation.

DERIVATION
fpbs-expander-approximant-giant-data-is-glued-proof
