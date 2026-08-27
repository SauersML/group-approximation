---
rg: 2
id: b2-full-hecke-first-support-proof
kind: route
title: Use the B2 commutator to exchange the two r signs on Q
target: b2-pairs-full-hecke-first-support
requires:
  - center-chain-mixed-hecke-overlap-is-common-pauli-source
  - native-j1-extension-gives-gl5-but-only-second-whitehead-gram
---

We first check that the displayed spectral cut is intrinsic to `Q`, not
only to the coarser source `p_2`.  Recall

```text
H=<x_65(q),x_54(q),x_42(q)>,
r=x_58(a_2),
d=x_82(b_2), f=x_94(b_3), c=x_97(b_3a_1), k=x_92(b_3),
v=x_57(a_1), w=x_67(a_1), s=x_68(a_2).               (1)
```

Conjugation by `r` fixes the displayed generators except for the two
ordinary Steinberg corrections

```text
x_65(q) |-> x_65(q)s,
d         |-> d x_52(q),                              (2)
```

up to orientation.  Here `qa_2=a_2` and `a_2b_2=q`.  The correction `s`
has positive `lambda_0` sign and `x_52(q)` is a positive derived root of
`H`.  Hence `r` normalizes `(L_0,lambda_0)` and commutes with its signed
character projection `Q`.

The proof of
`center-chain-mixed-hecke-overlap-is-common-pauli-source` already checks
that `B_2=x_84(b_2)` normalizes the same signed pair: its only corrections
are `d` and positive derived roots of `H`.  Thus `B_2Q=QB_2` as well.

The adjacent-root commutator relation gives

```text
[x_58(a_2),x_84(b_2)]
  =x_54(a_2b_2)=x_54(q)=C_2.                          (3)
```

All three elements in `(3)` are involutions, and `C_2` commutes with
`r`.  Therefore `(3)` is equivalently

```text
B_2rB_2^(-1)=rC_2                                    (4)
```

with the same conclusion under the opposite commutator convention.  By
definition of the signed source character,

```text
C_2Q=-Q.                                              (5)
```

Combining `(4)--(5)` gives

```text
(B_2Q)(rQ)(B_2Q)^*=-rQ.                              (6)
```

Thus the unitary `B_2Q` maps the positive eigenspace of `rQ` isometrically
onto its negative eigenspace and conversely.  The two eigenspaces have
equal dimension and sum to `QH`, proving `(BFS5)`.

Finally, `native-j1-extension-gives-gl5-but-only-second-whitehead-gram`
computes the exact first compression on `p_2` as

```text
p_2(J_1p_2J_1)p_2=p_2(1+r)/2.                        (7)
```

Since `Q<=p_2` and `Q` commutes with `r`, multiplying `(7)` on both sides
by `Q` proves `(BFS6)`.

`experiments/full_q_b2_r_support_audit.py` provides an independent faithful
finite check of the normalization inputs.  Rather than replacing coefficient
roots by constant arrows or enumerating the `8,192`-element source, it checks
the conjugation image of each of the ten actual sparse Leavitt generators.
It verifies that both `r` and `B_2` preserve every generator sign and checks
`B_2rB_2^(-1)=rC_2`.  Its MSI run is subsecond after imports.
