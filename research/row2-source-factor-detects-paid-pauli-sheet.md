---
rg: 2
id: row2-source-factor-detects-paid-pauli-sheet
kind: claim
title: The literal row-two source factor detects the paid Pauli sheet root
artifacts:
  - research/row2-source-factor-sheet-cube-proof.md
distinct_from:
  paid-pauli-menu-has-two-row2-indistinguishable-sheets: that tests the composite row-two operators and proves that all five commute with the sheet root; this descends one authenticated factor in the actual A2 row and finds the first noncommuting occurrence.
  row2-parallel-a2-return-diamond-has-gl8-model: that authenticates the two factor paths returning A2 and gives a finite same-root-identification fence; this computes the new factor's exact cube with the paid D/Y2 menu and proves that its sheet output is a nonzero root.
  middle-index-heisenberg-packet-is-not-center-chain-invariant: that computes the q-valued ejection [A2,Y2]=x_53(q); this retains the uncompressed paid coefficient and computes the larger s1h-valued sheet detector.
---

**ESTABLISHED MINIMAL FACTOR-LEVEL SHEET DETECTOR.**  Retain

```text
D=x_78(d),          d=(1+s_0)t_00,
Y_2=x_83(b_2),      b_2=s_00t_1,
H=[D,Y_2]=x_73(h),  h=db_2=t_1+s_0t_1,               (SFD1)
```

and descend one step into the already authenticated factorization of the
actual row-two arm:

```text
S_57=x_57(s_1),     T=x_78(t_00),
[S_57,T]=A_2=x_58(s_1t_00).                           (SFD2)
```

Unlike the composite `A_2`, the literal factor `S_57` is incident to the
sheet position `(7,3)`.  Ordinary Steinberg collection gives the exact
nontrivial root

```text
K=[S_57,H]=x_53(s_1h)
 =x_53(s_1t_1+s_1s_0t_1) !=1.                        (SFD3)
```

Moreover this is the missing face of the paid factor cube:

```text
K=[[S_57,D],Y_2],
Y_2^(-1)[S_57,D]Y_2=[S_57,DH]=[S_57,D]K.             (SFD4)
```

Thus the two sheets have different literal factor-level signatures.  The
first row-two Heisenberg ejection is visible inside the same cube:

```text
[[S_57,T],Y_2]=[A_2,Y_2]=x_53(q),   q=s_1t_1.        (SFD5)
K=[A_2,Y_2]x_53(s_1s_0t_1).                         (SFD6)
```

This occurrence has minimum possible ordinary-word length in the native
inventory: `S_57` is itself one elementary-root factor, and it is tied to
the prescribed row by `(SFD2)`.  No nonidentity ordinary word can use fewer
than one factor.  It corrects the scope of the previous two-sheet fence:
the composite menu is blind to `H`, but the authenticated factor closure is
not.

The detector cannot disappear in a norm-matrix-corona representation which
retains the marked root.  Its coefficient `s_1h` is nonzero, so
`binary-leavitt-nonzero-roots-have-uniform-corona-rank-scale` gives its
nontrivial spectral projection at least one quarter of the marked rank
scale after active reblocking.  Hence the two commutator signatures in
`(SFD4)` cannot be identified by killing `K` on the whole active model.

Here “source factor” means the literal source-side coefficient arm in
`(SFD2)`; it does **not** mean that `S_57` reduces the signed Reynolds
projection.  This is an exact sheet **detector**, not yet the signed-source
selector.  No established relation justifies compression of `(SFD3)` or
`(SFD4)` to either the paid constant-atom cut or the signed source
`Q=e_(L_0,lambda_0)`.  In particular, neither cut is currently known to
reduce `S_57`, and no present estimate controls the leakage term created by
that compression.  Nor is either signature in `(SFD4)` authenticated as
the prescribed quarter/eighth source compression.  A continuation may now
charge leakage of `S_57` from a paid/Reynolds cut, or attach the nonzero `K`
carrier to the actual signed source; it no longer needs to search for an
ordinary word which merely fails to commute with `H`.  No Property T,
canonical trace, literature input, local computation, or Lean compilation
is used.

DERIVATION
row2-source-factor-sheet-cube-proof
