---
rg: 2
id: literal-prefix-whitehead-relative-word-fixes-mark
kind: claim
title: Every literal prefix-Whitehead relative word fixes the marked root
artifacts:
  - research/literal-prefix-whitehead-relative-word-proof.md
distinct_from:
  same-center-whitehead-gram-is-not-native-selector-gram: that refutes the attempted unequal-selector typing by comparing label ranks; this computes the full relative group word and rules out the separate root-valued cross-Gram criterion for the whole literal prefix-Whitehead subgroup.
  arbitrary-profile-selector-type-menu-dichotomy: that gives a character-type test after literal occurrence words have been authenticated; this shows that the available prefix-Whitehead words never enter its root-valued alternative.
  root-valued-relative-transport-forces-cross-gram: that proves a positive estimate when the relative word moves the mark to a disjoint nonzero root; this proves that its hypothesis fails for the current literal prefix packet.
---

Retain the binary Leavitt coefficients and literal adjacent prefix-Whitehead
words of `same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps`:

```text
z=x_13(q),
W_m=x_(k_(m+1),k_m)(c_m)
    x_(k_m,k_(m+1))(d_m)
    x_(k_(m+1),k_m)(c_m),             m=1,2,           (LPF1)
```

where `k_1,k_2,k_3` are disjoint from `1,3`.  Let

```text
Omega=<W_1,W_2>.
```

Then every `w in Omega` centralizes `z`.  In particular, for every two
literal prefix transport words `g_1,g_2 in Omega`, their relative word
`u=g_1^(-1)g_2` satisfies

```text
u z u^(-1)=z.                                           (LPF2)
```

Thus no such pair satisfies the disjoint-root hypothesis

```text
u z u^(-1)=x_ij(a),       a!=0,       {i,j} disjoint {1,3}    (LPF3)
```

of `root-valued-relative-transport-forces-cross-gram`.  This includes the
actual adjacent pair: since the Whiteheads are involutions,

```text
u=W_1^(-1)W_2=W_1W_2,
u^3=1,
u z u^(-1)=z.                                           (LPF4)
```

The conclusion is unchanged after multiplying either word on the left or
right by fixed packet relabelings which centralize `z`: all resulting
relative words remain in the centralizer of `z`.

This is an exact obstruction to the most direct arbitrary-profile MF
shortcut, not a refutation of the desired native cross-Gram claim.  One
could multiply a transport by an extra word which moves `z`, but then that
word is new occurrence holonomy.  The existing prefix covariance and braid
relations do not authenticate that dressing as the prescribed unequal
selector transport or control its mixed Pauli gauge.  In particular the
literal packet still supplies two adjacent one-quarter label swaps and no
actual one-eighth selector occurrence.

No Property `(T)`, Kazhdan input, canonical trace, or literature theorem is
used.

DERIVATION
literal-prefix-whitehead-relative-word-proof
