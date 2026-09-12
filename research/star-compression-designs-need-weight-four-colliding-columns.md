---
rg: 2
id: star-compression-designs-need-weight-four-colliding-columns
kind: claim
title: Star compression designs in the odd-measure crossed product need colliding weight-four columns carrying half the mass
distinct_from:
  odd-measure-space-has-no-honest-thompson-compression: that forbids honest monomial partial isometries with disjoint images; this constrains every star design, including multi-point signed columns, and says where its mass must sit.
  odd-measure-crossed-product-carries-mod-three-trace: that is a mod-3 trace which does not obstruct the target; this is a real Haar counting constraint that applies only to star designs.
artifacts:
  - research/artifacts/odd-measure-star-compression-designs-2026-09-12.md
---

Let `B = C(M_-, F_3) ⋊_alg V` be the signed Thompson crossed product
(`signed-thompson-algebra-is-odd-measure-crossed-product`), with Haar measure `lambda` on `M_-`,
`q_[0] = 1_(U_[0])`, and involution `(f[g])* = (f o g)[g^-1]`. Call `x = sum_(g in F) a_g [g] in B` a
*star compression design* if `x* x = eps_-` and `q_[0] x = x`. Such an `x` solves
`odd-measure-crossed-product-unit-below-cylinder-idempotent` with `b' = x` and `c' = x*`.

Put `c(mu) = #{g : a_g(g mu) != 0}` (column weight) and `n(nu) = #{g : a_g(nu) != 0}` (image
multiplicity). For every star design:

1. `c(mu) ≡ 1 mod 3` everywhere, and `∫ c dlambda = ∫ n dlambda`, with `n` supported in `U_[0]`.
2. The collision set `{n >= 2}` carries `∫ n dlambda >= 1/2`.
3. Almost every collision is between two distinct columns that share at least two points, with
   products of entries summing to `0` in `F_3`.
4. Columns of weight at least `4` carry at least half the mass: `∫_(c >= 4) c dlambda >= 1/2`, so
   `lambda(c >= 4) >= 1/(2|F|)`.

In particular no cancellation-free design exists. That extends
`odd-measure-space-has-no-honest-thompson-compression` from honest pieces to arbitrary signed columns.

Scope: this concerns star designs only. A general solution `c' q_[0] b' = eps_-` with
`c' != b'*` has no square-counting identity. Theorem 4.1 of the artifact, route
`star-compression-weight-four-proof`.
