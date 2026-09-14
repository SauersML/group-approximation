---
rg: 2
id: block-unipotent-rank-models-of-leavitt-el3-are-trivial
kind: claim
title: Rank models of EL_3 over a Leavitt algebra whose root subgroups act by block unipotents are trivial, at any block ranks
distinct_from:
  leavitt-algebra-has-no-unital-rank-model: that forbids a unital homomorphism of the algebra itself, and its verified scope remark excludes elementary-matrix models built from one given coefficient map on equal blocks; this starts from independent block maps between blocks of arbitrary, unequal ranks and derives the coefficient map from the Steinberg relations.
  binary-leavitt-unit-group-is-f2-linear-sofic: that is the open existence of rank models of the whole unit group; this excludes one family of candidates, the models that are block unipotent on root subgroups, including every model built from approximate modules.
  projective-ternary-group-is-f3-linear-sofic: that is the open F_3 gate for the ternary scalar quotient; this excludes the block-unipotent family for the ternary unit group, which embeds there.
artifacts:
  - research/artifacts/leavitt-unit-rank-model-construction-audit-2026-09-12.md
---

**ESTABLISHED.** Let `K` be a field, `n >= 2`, and `R_K = L_K(1,n)`, a simple ring with
`t_0 s_0 = 1 != s_0 t_0`. Let `M` be a directly finite ring, for instance any rank
ultraproduct `prod_omega M_(N_k)(F) / d_omega` over any field `F`. Let `e_1, e_2, e_3` be
pairwise orthogonal idempotents of `M`, of arbitrary and possibly different ranks, not
required to sum to `1`. Let `sigma` be a homomorphism from the Steinberg group
`St_3(R_K)`, or from `EL_3(R_K)`, into `M^x` with

```text
sigma(x_ij(a)) = 1 + psi_ij(a),      psi_ij(a) in e_i M e_j      (i != j, a in R_K).
```

Then `psi_ij(a) = 0` for all `i, j, a`, so `sigma` is trivial.

**Finite-stage form.** Let `sigma_k : EL_3(R_K) -> GL_(N_k)(F)` be asymptotically
multiplicative in normalized rank, and suppose that for block projections `e_i^(k)` of
arbitrary ranks each `sigma_k(e_ij(a)) - 1` lies within `o(N_k)` rank of
`e_i^(k) M_(N_k)(F) e_j^(k)`. Then `rk(sigma_k(g) - 1) = o(N_k)` for every `g`. No such
sequence separates elements, so none is a linear sofic approximation.

**The relations that force multiplicativity.** Only two Steinberg relations are used:

```text
(A)  x_ij(a) x_ij(b) = x_ij(a + b)    gives   psi_ij(a + b) = psi_ij(a) + psi_ij(b),
(B)  [x_ij(a), x_jk(b)] = x_ik(ab)    gives   psi_ij(a) psi_jk(b) = psi_ik(ab)   (i, j, k distinct).
```

(B) on ordered triples makes `u_ij = psi_ij(1)` a system of matrix units between the
corner idempotents `p_i = u_ij u_ji`, which therefore all have the same rank. Every
`psi_ij(a)` is supported on these corners, and `phi(a) = psi_12(a) u_21` is a unital ring
homomorphism `R_K -> p_1 M p_1`. Corners of directly finite rings are directly finite,
so simplicity and `t_0 s_0 = 1 != s_0 t_0` force `p_1 = 0`.

**Unequal block dimensions do not help.** The Weyl element
`w_ij = x_ij(1) x_ji(-1) x_ij(1)` goes to `(1 - p_i - p_j) + u_ij - u_ji`: the signed swap
of two equal-rank corners, and the identity elsewhere. The relations force
`rk(p_i) = rk(p_j)` but not `rk(e_i) = rk(e_j)`, and `e_i - p_i` carries the trivial
action. So an ansatz with unequal blocks, suggested by `R_R = R_R^2`, is an equal-corner
model plus a trivial summand, and the equal-corner part dies. The Kazhdan fixed-ideal
conditions are never reached.

**Scope.** For `R = L_K(1,2)`, `R_R = R_R^2` gives `M_3(R) = R` and `R^x = GL_3(R)`, and
`GL_3(R) = EL_3(R)` over `F_2` (`leavitt-gl-equals-el-and-perfect-unit-group`). So a rank
model of `R^x` that is block unipotent for some 3-block decomposition, with respect to
some identification `R^x = EL_3(R)`, is trivial. That includes every model built from
approximate `R`-modules, at any ranks. For `L_(F_3)(1,2)^x`, restrict the model to the
nontrivial subgroup `EL_3`. A surviving model must, for every such decomposition, either
act non-additively on some root subgroup, meaning
`(sigma(x_ij(a)) - 1)(sigma(x_ij(b)) - 1)` is not rank-null, or have square-zero parts
that are not simultaneously supported on orthogonal blocks.

## Attempts

Established; see `block-unipotent-rank-models-of-leavitt-el3-proof`. This answers
negatively the question recorded in Section 4 of the artifact, whether the Leavitt
multiplication can be carried on off-diagonal blocks of elementary matrices with
`o(n)` rank defect, at every choice of block dimensions.
