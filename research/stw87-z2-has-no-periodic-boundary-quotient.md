---
rg: 2
id: stw87-z2-has-no-periodic-boundary-quotient
kind: claim
title: The Z2 uniform Roe boundary has no periodic quotient or torus retraction
distinct_from:
  stw87-invariant-mean-retraction-has-coset-order-zero-gap: that theorem shows that the canonical ucp retraction onto the group algebra has a positive order-zero defect; this theorem excludes every homomorphic retraction fixing the group algebra and every periodic coefficient quotient.
  stw87-diagonal-expectation-order-zero-obstruction: that theorem quantifies failure of the diagonal conditional expectation on one finite matrix packet; this theorem uses freeness of the Stone--Cech action and applies to boundary and limit-operator constructions.
  stw87-coarse-embedding-corner-lower-bound: that theorem produces hereditary embeddings and genuine nuclear-dimension inequalities; the periodic torus blocks found here are only subalgebras of limit images and therefore give no such inequality.
artifacts:
  - research/artifacts/stw87-z2-boundary-limit-operator-audit-2026-08-30.md
---

Put `G=Z^2`, `D=ell^infinity(G)=C(beta G)`, and

```text
A=C*_u(G)=D crossed_product_r G.
```

Then:

1. every nonidentity translation acts without fixed points on `beta G`; in
   particular `beta G` has no nonempty finite `G`-invariant subset;
2. there is no unital `G`-equivariant star homomorphism from `D` onto the
   functions on a nonempty finite `G`-set, so no periodic coefficient
   quotient induces a crossed-product quotient of `A`;
3. there is no star-homomorphic retraction

   ```text
   A -> C*_r(G)=C(T^2)
   ```

   which fixes the canonical group algebra pointwise.

On the other hand, every Stone--Cech limit representation `Phi_omega` fixes
`C*_r(G)` and, for every finite-index subgroup `H<G` of index `k`, its image
contains the periodic crossed product

```text
C(G/H) crossed_product_r G
  ~= M_k(C*_r(H))
  ~= M_k(C(T^2)).
```

Thus limit operators retain the two-dimensional periodic torus blocks only
as subalgebras.  Nuclear dimension is not monotone for arbitrary
subalgebras, and the absent quotient/retraction is exactly what prevents
this observation from proving `dim_nuc(C*_u(Z^2))>=2`.
