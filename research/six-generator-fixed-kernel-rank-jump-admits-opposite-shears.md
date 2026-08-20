---
rg: 2
id: six-generator-fixed-kernel-rank-jump-admits-opposite-shears
kind: claim
title: A six-generator fixed-kernel rank jump admits opposite polynomial shears
artifacts:
  - experiments/six_generator_fixed_kernel_clock_search.py
distinct_from:
  paired-frame-fixed-kernel-polynomial-clock-no-go: that proves no four-generator paired frame can have the required fixed kernel and opposite clock; this shows that one additional hyperbolic plane removes the alternating-form obstruction.
  phase-inverting-fourth-root-lifts-opposite-pauli-shears: that repairs the quadratic involution relations for the shears; this concerns only their preservation of the alternating commutator pencil.
---

On `F_2^6`, let `J,K` be the alternating forms

```text
J=e_0 wedge e_1+e_2 wedge e_3,        K=e_4 wedge e_5.          (SFK1)
```

Their rank profile on the two central-character bits is

```text
rank(0)=0,       rank(K)=2,       rank(J)=4,       rank(J+K)=6. (SFK2)
```

Over `F_2[x]`, both opposite transvections

```text
S_+=I+xE_01,                  S_-=I+xE_10                       (SFK3)
```

preserve `J` and `K` separately.  Their product has strictly growing
polynomial degree.  Thus a baseline rank-four packet and its one-Pauli-pair
rank jump coexist with a fixed two-form kernel and an opposite-shear clock.

The exhaustive artifact searched all `18,228` rank-four marked forms whose
sum with the complementary form is the standard rank-six form.  It found
`183` form pencils admitting an opposite elementary polynomial-shear pair;
`(SFK1)` is a minimum-weight witness.  This is an alternating-form theorem
only.  Without the fourth-root correction, `(SFK3)` need not preserve the
quadratic requirement that the Pauli generators be involutions.
