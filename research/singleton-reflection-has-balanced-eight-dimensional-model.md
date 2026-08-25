---
rg: 2
id: singleton-reflection-has-balanced-eight-dimensional-model
kind: claim
title: The singleton Leavitt reflection word has a minimal balanced eight-dimensional specialization
distinct_from:
  odd-selector-row-balances-or-kills-outer-action: That gives the general odd-selector dichotomy for a Clifford implementer; this computes the exact singleton BAF word and its undecoded support defect, proves minimal spectator dimension, and records extension to the native Whitehead occurrence chart.
  literal-fiber-unequal-reflection-row-collapses-packet: That rules out making both unequal corners literal packet projections; this keeps the fine reflection non-semisimple/groupified and exhibits the residual multiplicity twist explicitly.
  btb-balanced-loops-stop-at-same-object-reflection: That gives a rectangular-Weyl countermodel until the support row is imposed; this satisfies the proposed singleton group-word row itself while falsifying its identification with the physical fine-corner reflection.
---

**ESTABLISHED MINIMAL SPECIALIZATION COUNTERMODEL.**  Let `S=C^4` be the
marked two-qubit Pauli spin module, let

```text
r=Z_1,              f=((1-Z_1)/2)((1-Z_2)/2),
C=1-2f.                                                (SLR1)
```

Thus `r` has normalized trace zero, while `C` has normalized trace `1/2`.
On `P=S tensor C^2`, put

```text
V=diag(1,-1),          t=C tensor V,
r_P=r tensor I_2.                                      (SLR2)
```

Both `t` and `r_P` are involutions with four positive and four negative
eigenvalues.  Hence there is a unitary `W` with

```text
t=W r_P W^*.                                           (SLR3)
```

The singleton ordinary word proposed for the same-object row is therefore
exact:

```text
D=t W r_P W^*=I.                                       (SLR4)
```

Nevertheless the physical fine reflection is `C tensor I_2`, and

```text
||(C tensor I_2)-t||_2^2=||I_2-V||_2^2=2,
||(C tensor I_2)W r_P W^*-I||_2^2=2.                  (SLR5)
```

So zero packet, covariance, and singleton-word defect coexist with a full
positive carrier `P` and a fixed failure of the decoded coarse-to-fine
support row.  The word `D` authenticates only the twisted group element
`C tensor V`; it does not authenticate `C tensor I`.

This is dimension-minimal for the marked spin packet.  With multiplicity one,
the traces of `r` and `C` differ, so they cannot be conjugate.  To make
`tr(C tensor V)=0`, a multiplicity involution must have trace zero; its
smallest dimension is two.  Hence the first countermodel has dimension
`4*2=8`.

Adding the native finite Steinberg/Whitehead occurrence does not remove this
specialization.  The rectangular coefficient chart realizes the signed
three-root Whitehead word on equal-rank typed source and target corners, and
`separate-balanced-hnn-cross-gram-is-typed-overlap` gives the explicit finite
amalgam/regular-amplification construction identifying that occurrence with
the chosen `W` while retaining the balanced model.  Thus every finite
occurrence table, multiplication triangle, Clifford covariance row, and the
singleton word `(SLR4)` can hold exactly while `(SLR5)` remains.

The model does not extend to the full affine-Leavitt Steinberg presentation;
exact finite-dimensional active-root collapse forbids that.  Consequently a
successful decoder must use a genuinely global coefficient-occurrence row
from the full presentation to force `V=I` on the prescribed fiber.  The
singleton reflection word and any finite rectangular occurrence chart do not
do so.

DERIVATION
balanced-spin-gauge-cancels-singleton-support-word
