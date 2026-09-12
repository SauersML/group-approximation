---
rg: 2
id: matrix-unit-root-rank-models-of-simple-el3-are-trivial
kind: claim
title: A characteristic-two rank model of EL_3 over a simple non-directly-finite ring is trivial once its unit root elements act by matrix units
distinct_from:
  block-unipotent-rank-models-of-leavitt-el3-are-trivial: that assumes block support of every root element x_ij(a), for all a in R; this assumes block support only of the six unit root elements x_ij(1) and derives it for every a from the Steinberg relations, so it also kills the hybrid models that are block unipotent on a subring and arbitrary elsewhere.
  el3-rank-models-factor-through-ring-rank-models: that is the open claim that every rank model extracts a ring rank model; this is the established case where the unit root elements already act by matrix units on a natural block with trivial complement.
artifacts:
  - research/artifacts/el3-rank-ring-rigidity-2026-09-12.md
---

**ESTABLISHED** (proof in the artifact, Section 4c). Lane `gk-l-gate-pos` independently
re-derived it on 2026-09-12, including a complement on which the unit root elements act
trivially. `gk-vf-linear` passed it (Section 22 of
`research/artifacts/gk-vf-linear-verification-2026-09-12.md`, ad4e862566), with this scope
sharpening: block support of the six unit root elements on orthogonal idempotents already
gives the matrix-unit hypotheses. The block calculus gives `u_ij u_jk = u_ik`, and shrinking
`p_i` to `u_ij u_ji` still leaves a complement that the `u`'s kill. So the claim covers every
model whose `x_ij(1)` act block-unipotently. The odd-characteristic case
is `matrix-unit-root-rank-models-of-odd-char-simple-el3-are-trivial`. Let `R` be a simple ring of characteristic two that is not directly
finite, for instance `L_K(1,n)` with `char K = 2` and `n >= 2`. Let `M` be a rank
ultraproduct of matrix algebras over a field of characteristic two, and
`sigma : EL_3(R) -> M^x` a homomorphism. Suppose there are pairwise orthogonal idempotents
`p_1, p_2, p_3` with

```text
sigma(x_ij(1)) = 1 + u_ij,   u_ij in p_i M p_j,   u_ij u_jk = u_ik,   u_ij u_ji = p_i .
```

Then `sigma` is trivial.

The Steinberg relations propagate block support from `x_ij(1)` to every `x_ij(a)`. The
coefficients form a unital ring homomorphism `R -> p_1 M p_1`, which direct finiteness of the
corner and simplicity of `R` force to vanish. Block support is required only on the unit root
elements, not on all of `R`.

**Consequence.** Every rank model built from honest modules over a subring is trivial on the
Leavitt unit group in characteristic two, however it acts outside the subring. That includes
degree truncations, approximate modules over subrings, and hybrids that are block unipotent
on a polynomial subring. So a nontrivial characteristic-two model must restrict to
`SL_3(F_2) = EL_3(F_2)` as something other than `(natural (x) W) (+) trivial`.

**Dual natural shape (`gk-vf-linear`, verification artifact Section 29, eda113e5ce).**
Transpose-inverse is an isomorphism `EL_3(R) -> EL_3(R^op)` sending `x_ij(a)` to `x_ji(-a)`,
and `R^op` is simple and not directly finite. So a model with
`sigma(x_ij(1)) = 1 - u'_ji` for matrix units `u'` is of matrix-unit form over `R^op`, and it
is trivial as well. So `(dual natural (x) W) (+) trivial` is excluded too. Models with positive
free content on `SL_3(F_2)` never meet the hypothesis
(`free-rank-models-on-sl3-admit-no-block-support`).
