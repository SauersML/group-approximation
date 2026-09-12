---
rg: 2
id: stable-finite-actions-blocks-codense-kazhdan-coset-soficity
kind: claim
title: Stability in finite actions rules out a permutation-co-dense Kazhdan coset action
distinct_from:
  codense-tau-coset-soficity-forces-permutation-instability: that concludes a sofic coset atlas cannot be Hamming-corrected to genuine actions; this needs only the weaker weak-containment property called stability in finite actions and concludes that no sofic atlas exists.
  codense-kazhdan-coset-action-forces-permutation-outliers: that proves the finite exact-atlas gap; this converts the gap into nonsoficity under one named stability modulus for the actor.
  sofic-stable-implies-residually-finite: that tests the regular action and concludes residual finiteness of the group; this tests one nonfree coset atlas of an already residually finite actor.
---

Let `C<A` be a proper finitely generated subgroup.  Assume:

1. `A` is residually finite and stable in finite actions;
2. `C` has a finite Kazhdan set with constant `kappa>0`;
3. `rho(C)=rho(A)` in every finite action `rho` of `A`.

Then the transitive set action

```text
A curvearrowright A/C                                             (SFA1)
```

is not sofic.

The conclusion uses no Hamming correction theorem.  Stability in finite
actions says that the p.m.p. limit of every sofic approximation of `A` is
weakly contained in finite `A`-actions.  A hypothetical sofic orbit atlas
for `(SFA1)` can be multiplied by separating finite quotients of the
residually finite actor, making its actor maps a sofic approximation without
changing the atlas statistics.  Weak containment would then reproduce its
two-site partition statistics in genuine finite actions.  The uniform gap
`codense-kazhdan-coset-action-forces-permutation-outliers` forbids exactly
those statistics.

Thus full flexible P-stability is substantially more than this argument
needs.  The single named modulus is **stability in finite actions**.

DERIVATION
stable-finite-actions-coset-nonsofic-proof
