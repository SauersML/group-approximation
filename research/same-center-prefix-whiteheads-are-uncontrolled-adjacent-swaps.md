---
rg: 2
id: same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps
kind: claim
title: Same-center prefix Whitehead transports put both native scale rows on one carrier
artifacts:
  - research/same-center-prefix-whitehead-swap-proof.md
distinct_from:
  marked-root-star-carries-three-anchored-cells: that uses three distinct commuting q-center roots to place the coefficient factorizations on one carrier; this uses one common q-center root and computes the exact label action of the adjacent partial-Whitehead transports.
  binary-leavitt-native-two-scale-cross-gram-positive: that asks for the cross-Gram and mixed-Pauli estimates for the two actual selector transports; this identifies those literal partial-Whitehead words on one reducing carrier and computes their transport-label normal forms.
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
involutions.  In either case the two fixed **transport** label actions are
ordinary adjacent swaps.  Each has a two-dimensional negative eigenspace in
the eight-dimensional label factor, hence negative fraction `1/4`.

This `1/4,1/4` calculation is not the selector-rank pair.  The controlled
selector groupifications attached to the two rows have the separate fixed
label factors `C_(1/4)` and `C_(1/8)`; their external multiplicity unitaries
are the `V_1,V_2` carried by the coefficient transports in `(SCW4)`.  The
role of `(SCW4)` is to put those transports, and hence those gauges, on one
physical carrier.

Indeed, after the fixed packet relabelings used by the selector rows, put

```text
S_m=F rho(W_m) F : FH -> FH.
```

Because both `W_m` commute with the two defining involutions of `F`, these
are unitaries on `FH`, and therefore

```text
tau(S_1^*S_2S_2^*S_1)=tau(F).                         (SCW5)
```

After removing the two canonical adjacent swaps, the relative polar gauge
is `V_1^*V_2` in the common three-qubit Pauli commutant.  Its two mixed
source-Pauli commutators vanish exactly.  Thus `(SCW1)` and `(SCW5)` provide
the native two-scale cross-Gram front end; they do not replace or alter the
controlled `1/4,1/8` selector label factors.

No Property T, stability input, or literature theorem is used.

DERIVATION
same-center-prefix-whitehead-swap-proof
