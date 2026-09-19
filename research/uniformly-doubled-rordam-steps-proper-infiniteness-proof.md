---
rg: 2
id: uniformly-doubled-rordam-steps-proper-infiniteness-proof
kind: route
title: The tail factors out and rank beats half the dimension, so a trivial line embeds
target: uniformly-doubled-rordam-steps-force-proper-infiniteness
requires: []
artifacts:
  - research/artifacts/stw99-lxvi-dyadic-rordam-design-2026-08-30.md
---

The subprojection carried by the family is, at the bundle level,
`⊕_{j=1}^m M·ζ_{S_j} = ζ_T ⊗ Ξ` with `Ξ = ⊕_j M·ζ_{u_j}` of complex rank
`M m`, over the finite base `(S²)^{T ∪ u_1 ∪ … ∪ u_m}` of real dimension
`2(|T| + Σ_j |u_j|)`.  A trivial line embeds in `ζ_T ⊗ Ξ` iff
`Ξ ⊗ ζ_T^{-1}` has a nowhere-vanishing section; the obstructions to a
nowhere-zero section of a complex rank-`r` bundle over a `d`-complex live
in degrees `≥ 2r`, so they all vanish once `2·(M m) > 2(|T| + Σ|u_j|)`,
which is the hypothesis `M m > |T| + m u` (with `Σ|u_j| ≤ m u`).  So
`θ ↪ ⊕_F`, i.e. `g ≾` the family's subprojection (Rørdam Lemma 4.1's
correspondence).

For disjoint supply, partition the relevant branch occurrences into
infinitely many finite families satisfying the displayed inequality.
Their subprojections `q_l` are mutually orthogonal summands of the strict
stage decomposition.  Choose `r_l <= q_l` with `r_l ~ g`.  The strict sum
`r = direct_sum_l r_l` exists because its partial sums are dominated by
the corresponding tails of the strictly summable branch decomposition.
Rørdam's Lemma 4.2 identifies `r ~ direct_sum_l g ~ 1`.  Hence `1 ≾ Q`;
condition (iii) of Lemma 4.3 gives `Q ~ 1`, so `Q` is properly infinite.

In the paired-step design, use only the infinitely many (C2) branch
occurrences at step 1.  Each has singleton `I_beta`.  Fix one singleton
seed summand and, after step 1, follow one common branch at every later
step.  At stage `n`, every resulting member set has the form
`S_j = T disjoint_union u_j`, where `T` is the common contribution of the
later history and `|u_j| <= 2`: the step-1 branch sends the seed singleton
to at most one relabelled seed coordinate plus its singleton tensor
coordinate, and later injections preserve that bound.  Overlaps among
the `u_j` only lower the base dimension, so common early coordinates can
be moved into `T`; in every case `sum_j |u_j| <= 2m`.

After `c(n)` globally paired steps, each such branch occurrence appears
with multiplicity at least `M = 2^{c(n)}`.  Choose a stage with `M > 2`,
then choose `m > |T|/(M-2)`.  This gives `Mm > |T|+2m`, exactly the
rank/dimension inequality.  Because (C2) supplies infinitely many step-1
occurrences, partition them into infinitely many groups of this fixed
size `m`; the corresponding stage subprojections are orthogonal and give
the disjoint supply used above.  This kills the certificate and, by the
preceding strict-sum argument, the projection itself.
