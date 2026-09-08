---
rg: 2
id: jacobson-ts-cell-is-independent-after-first-raw-commutation
kind: claim
title: The explicit Jacobson TS cell remains independent after both braids and the first raw-tail commutation
distinct_from:
  binary-jacobson-first-alternating-ts-closure-relation: that separates the TS word from the one-step virtually free envelope; this proves that it remains nontrivial after both braid relations and an additional nonpermutation-tail commutation.
  jacobson-two-braid-infimum-is-zero: that constructs the amenable seven-ray quotient retaining the full packet; this computes the TS word as a nontrivial finite transvection in that quotient.
artifacts:
  - research/artifacts/jacobson-ts-cell-after-seven-ray-countermodel-2026-09-08.md
  - research/artifacts/jacobson-gamma2-universal-pair-structure-2026-09-08.md
---

In the two-braid presentation `Gamma`, put

```text
c=(I+E_13)_P,  z_Q=(I+E_23)_Q,  z_P=(I+E_23)_P,
z=z_Q z_P,     k=(I+E_31)_Q (I+E_31)_P,
Gamma_1=Gamma/<<[h c h,z_P]>>,
W=[[h c h,k],h z h] z.
```

Then `W` is nontrivial in `Gamma_1`. In its amenable seven-ray quotient
the word sends `a_(3,0)` to

```text
a_(3,0)+a_(1,1)+b_(3,1)+a_(2,0),
```

with the three added terms distinct independent basis vectors.

More strongly, in this seven-ray quotient one has
`[(I+E_12)_Q,W]=w`. Thus every unitary representation of that quotient
retaining `w` satisfies `||rho(W)-I||>=1`. This identity and bound
are not asserted for all representations of `Gamma_1`.

The literal map to `EL_3(F_2<S,T|TS=1>)` kills `W` and retains the
entire finite packet. Consequently `Gamma_1/<<W>>` is an explicit finite
presentation with a nontrivial head mark and a strictly stronger mixed
relation. This establishes no MF or non-MF conclusion for that quotient.

DERIVATION
jacobson-ts-cell-seven-ray-transvection-proof
