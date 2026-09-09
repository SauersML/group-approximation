---
rg: 2
id: jacobson-column-first-actor-quotient-retains-full-column
kind: claim
title: Imposing the first literal actor relation still leaves the full Jacobson column visible in a matrix corona
distinct_from:
  jacobson-whole-column-normalizer-has-marked-lef-models: that gives faithful models of the free-product actor cover; this imposes its nontrivial actor relation and proves corona faithfulness only on the additive column.
artifacts:
  - research/artifacts/jacobson-column-models-satisfy-first-actor-relation-2026-09-08.md
---

For `J=F_2<S,T | TS=1>`, let `N=(J,+)^2` and let
`K=GL_2(F_2)*<h | h^2=1>` act by constants and
`h(a,b)=((1-ST)a+Sb,Ta)`. Put `r=[u,h v h]`, where
`u=x_12(1)` and `v=x_21(1)` are constant actors.

The quotient `H_1=(N semidirect K)/<<r^2>>` retains an embedded
copy of `N` and has a permutation-matrix corona homomorphism injective
on `N`. Every fixed nonzero translation is eventually at operator-norm
distance `2` from identity. All exact finite-dimensional unitary
representations nevertheless kill `(J(1-ST)J)^2`.

The finite windows have binary dimension `2n^2+n+1`. A specified
complement makes their actor representations satisfy `r^2=1` exactly
for every `n>=2`. This does not establish actor faithfulness, the MF
property of `H_1`, or models of all literal Jacobson relations. In fact
the artifact exhibits a second fixed actor relation that is literally
trivial but has permutation-unitary error exactly `2` in these windows
for every `n>=5`. Thus `H_1` remains a proper cover and this particular
corona map does not descend to the literal column normalizer. Different
even-cycle models do descend, as established subsequently in
`jacobson-literal-column-normalizer-is-lef`; the failure just described
concerns the specific windows of this artifact.

DERIVATION
jacobson-column-boundary-table-kills-first-actor-relator-proof
