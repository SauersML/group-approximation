---
rg: 2
id: same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps
kind: claim
title: Same-center prefix Whitehead transports give two quarter swaps, not a one-eighth selector
artifacts:
  - research/same-center-prefix-whitehead-swap-proof.md
distinct_from:
  marked-root-star-carries-three-anchored-cells: that uses three distinct commuting q-center roots to place the coefficient factorizations on one carrier; this uses one common q-center root and computes the exact label action of the adjacent partial-Whitehead transports.
  binary-leavitt-native-two-scale-cross-gram-positive: that needs native selector label fractions one quarter and one eighth; this proves that the most direct common-center transport construction has label fractions one quarter and one quarter.
---

Put `R=L_(F_2)(1,2)`, `q=s_1t_1`, and, for `m=1,2,3`,

```text
a_m=s_1t_(0^m),                 b_m=s_(0^m)t_1.
```

Let `z=x_13(q)`, `C=x_42(q)`, and let

```text
F=((1-rho(z))/2)((1-rho(C))/2).
```

The two root involutions commute, and the marked-root overlap theorem gives

```text
tau(F)>=tau((1-rho(z))/2)/4.                           (SCW1)
```

For `k_1=7,k_2=8,k_3=9`, define

```text
A_m=x_(4,k_m)(a_m),             B_m=x_(k_m,2)(b_m).
```

On `FH`, the three pairs are mutually cross-commuting and satisfy

```text
[A_m,B_m]=C=-1.                                        (SCW2)
```

They therefore generate the standard three-qubit Pauli factor
`M_8(C)` with one common multiplicity reservoir.

For `m=1,2`, put

```text
c_m=s_(0^(m+1))t_(0^m),       d_m=s_(0^m)t_(0^(m+1)),
W_m=x_(k_(m+1),k_m)(c_m)
    x_(k_m,k_(m+1))(d_m)
    x_(k_(m+1),k_m)(c_m).                              (SCW3)
```

Each `W_m` commutes with `z` and `C`, preserves `F`, swaps the `m`-th and
`(m+1)`-st Pauli pairs, and fixes the remaining pair.  Consequently, after
identifying

```text
FH=(C^2)^(tensor 3) tensor M,
```

there are reservoir unitaries `V_m` such that

```text
rho(W_1)|_F=SWAP_(1,2) tensor V_1,
rho(W_2)|_F=SWAP_(2,3) tensor V_2.                     (SCW4)
```

If the chosen elementary lifts are involutions, then the `V_m` are
involutions.  In either case the two fixed label actions are ordinary
adjacent swaps.  Each has a two-dimensional negative eigenspace in the
eight-dimensional label factor, hence negative fraction `1/4`.  Thus this
literal common-carrier construction produces label fractions

```text
(q_1,q_2)=(1/4,1/4),                                  (SCW5)
```

not the native `(1/4,1/8)` pair required by the two-scale selector
compiler.  A successful second row must contain a genuinely controlled
three-bit incidence; merely shifting the common-center prefix factorization
one level deeper cannot close `(NCG1)`.

No Property T, stability input, or literature theorem is used.

DERIVATION
same-center-prefix-whitehead-swap-proof
