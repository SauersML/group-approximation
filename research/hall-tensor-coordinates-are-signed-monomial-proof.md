---
rg: 2
id: hall-tensor-coordinates-are-signed-monomial-proof
kind: route
title: Read the Hall tensor models as signed permutations on doubled bases
target: leavitt-hall-tensor-mf-trace-quotients-are-sofic
requires:
  - leavitt-presentation-double-has-all-fold-mf-moments
  - signed-monomial-tracial-images-are-sofic
  - sofic-radical-soficization
---

In `(AFM5)`, both summands of `bar_sigma_n` are permutation
representations.  The rank-one projection `p_n` is a coordinate projection
onto the base coset, so

```text
bar_V_n=(1-2p_n) directSum 1
```

is a diagonal sign matrix.  Hence both vertex representations in `(AFM7)`
take values in a finite signed permutation group.  Tensor products of
signed permutation matrices are signed permutation matrices on the tensor
basis, and direct-sum swap symmetrization preserves the same property.

For every fixed `k in K`, the two vertex maps agree on `k` eventually.
Thus the free-product coordinate homomorphisms send every defining amalgam
relation to the identity eventually and induce a homomorphism

```text
P -> product_omega(B_(N_n),||.||_2),                    (HGT1)
```

where `N_n` is the final tensor/direct-sum coordinate dimension.

For a group element `g`, the squared GNS norm of `u_g-1` under the limiting
trace is exactly the ultralimit of `||rho_n(g)-1||_2^2`; therefore the
kernel of `(HGT1)` is `ker(pi_(tau_t))`.  Apply
`signed-monomial-tracial-images-are-sofic` to obtain a faithful permutation
ultraproduct representation of the quotient `(HGS1)`.  Finally
`sofic-radical-soficization` gives `(HGS2)`, while `(HGS3)` gives `(HGS4)`.
