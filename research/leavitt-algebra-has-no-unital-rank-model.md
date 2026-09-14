---
rg: 2
id: leavitt-algebra-has-no-unital-rank-model
kind: claim
title: The binary Leavitt algebra has no unital homomorphism into any rank ultraproduct of matrix algebras
distinct_from:
  binary-leavitt-algebra-not-directly-finite: that is the bare ring identity t_0 s_0 = 1 != s_0 t_0; this is its rank-metric consequence, that R therefore embeds unitally in no rank ultraproduct over any field.
  linear-sofic-group-algebra-is-stably-finite: that embeds the group algebra of a linear sofic group into a rank ultraproduct, using that group elements are invertible; this is the non-embedding of the bare Leavitt algebra, whose isometries are not invertible.
  binary-leavitt-unit-group-is-f2-linear-sofic: that is the open question whether the unit group R^x is F_2-linear sofic; this is the algebra-level obstruction, which forbids the algebra-homomorphism route to a model but does not settle the group question.
  binary-leavitt-nonembeddable-character: that asks for a non-Connes-embeddable tracial character of the unit group; this is a rank-metric statement about the ambient algebra with no trace.
artifacts:
  - research/artifacts/leavitt-unit-rank-model-construction-audit-2026-09-12.md
---

**ESTABLISHED.** Let `R = L_(F_2)(1,2)` and let `M = prod_omega M_(n_k)(F)/d_omega`
be any rank-metric ultraproduct of matrix algebras over any field `F`, with
`d_omega` the ideal of normalized-rank-null sequences. Then there is no unital
`F`-algebra homomorphism `R -> M`. Equivalently, there is no sequence of unital
rank-approximate homomorphisms `phi_k : R -> M_(m_k)(F)` (additive, with
`rk(phi_k(ab) - phi_k(a)phi_k(b)) -> 0`, `rk(phi_k(1) - 1) -> 0`, and
`rk(phi_k(a))` bounded away from `0` for each `a != 0`).

**Consequence for models of the unit group.** A rank model of
`H = R^x = EL_n(R)` cannot be built by modelling the coefficient algebra and
taking elementary matrices `e_ij(a) |-> 1 + phi(a) E_ij`: the Steinberg
relation `[e_12(a), e_23(b)] = e_13(ab)` forces `phi` to be an approximate
unital algebra homomorphism, which this claim forbids. Any linear sofic model
of `H` must be genuinely non-multiplicative on `R`. This does not obstruct
`binary-leavitt-unit-group-is-f2-linear-sofic`: the isometries `s_i` are never
inverted inside `EL_n(R)` (`e_ij(a)^{-1} = e_ij(-a)`), so direct finiteness of
`M` places no Section-1 constraint on a group homomorphism.

## Attempts

Established, not open; see `leavitt-algebra-has-no-unital-rank-model-proof`.
`R` is simple and not directly finite, while every rank ultraproduct is
directly finite, so no unital homomorphism can carry the one-sided inverse
`t_0 s_0 = 1` without also inverting `s_0`, which `R` forbids.
