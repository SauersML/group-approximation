---
rg: 2
id: external-weyl-native-relative-word-proof
kind: route
title: Exchange the marked and common roots by two constant Weyl factors
target: external-weyl-dressed-native-pair-is-root-valued
requires:
  - native-local-occurrence-closure-fixes-mark
  - same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps
  - root-valued-relative-transport-forces-cross-gram
  - root-valued-overlap-does-not-undress-external-selector
---

In the elementary-matrix quotient, `w_14(1)` and `w_23(1)` are the two
disjoint coordinate transpositions `(1 4)` and `(2 3)`.  Their product `h`
sends the matrix unit `E_13` to `E_42` and conversely.  The standard
Steinberg Weyl conjugation formula gives `(EWN2)`; characteristic two removes
the usual sign.

Every factor of `W_1,W_2` has indices in `{7,8,9}`, so it commutes with both
`z=x_13(q)` and `C=x_42(q)`.  It follows that the three words `W_1,W_2,h`
normalize the commuting pair `{z,C}` and preserve `F=P_zP_C`.  Using
`W_1^2=W_2^2=1`, calculate

```text
(W_1hW_2)z(W_1hW_2)^(-1)
 =W_1h z h^(-1)W_1^(-1)
 =W_1 C W_1^(-1)
 =C.
```

This proves `(EWN4)`.

For `(EWN5)`, Weyl conjugation simply applies the same coordinate
permutation to both root indices.  Since every `k_m` lies in `{7,8,9}`, it
is fixed by `h`; index `4` goes to `1` and index `2` goes to `3`.  Thus the
dressing exchanges the entire named Pauli chart with a different one.  No
required occurrence relation identifies these two charts, and the final
required fence shows that positive root overlap cannot erase the mover
analytically.

