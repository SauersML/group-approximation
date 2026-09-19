---
rg: 2
id: generator-diagonal-does-not-couple-to-root-leak
kind: claim
title: The distinguished generator diagonal does not couple formally to the unbalanced root leak
invalidates:
  - sl3-fdg-via-generator-diagonal-root-leak
artifacts:
  - research/generator-diagonal-root-leak-countermodel-proof.md
distinct_from:
  unbalanced-root-leak-does-not-charge-off-spectral-separators: that uses an independently chosen positive separator and one auxiliary root coordinate which does not commute with the stable letter; this makes the entire selected generator tuple stable-letter-central and takes the separator to be exactly B_s=X_s/sqrt(|S|).
  generator-diagonal-is-a-central-matrix-range-separator: that proves the distinguished diagonal has positive gap whenever the primal tuple is outside the matrix range; this shows that its special algebraic form supplies no formal coupling to the unbalanced-root defect.
  two-conjugate-letter-overlap-data-is-morita-neutral: that preserves arbitrary separator gaps by tensoring the two-letter and overlap data onto a spectator factor; this is one explicit unbalanced-torus packet in which the leaking root itself supplies both the generator-diagonal gap and its off-spectral mass.
---

**ESTABLISHED LOCAL FIREWALL.**  There is an exact four-dimensional packet
for the variables in `unbalanced-torus-word-localizes-britton-leak` with

```text
eta_R=eta_L=eta_B=0,        eta_21=2.                    (GDR1)
```

Let `S_0` be the six displayed lattice coordinates

```text
{A_12,W_12,A_23,W_23,B_21,B_32}.
```

Every `X_s`, `s in S_0`, commutes with the stable letter `T`.  Nevertheless,
for the matrix range of `C^*(C_2*F_5)` with `B_21` assigned to the `C_2`
generator, the distinguished tuple

```text
C_s=X_s/sqrt(6)                                         (GDR2)
```

has separation gap exactly

```text
Delta(C;X)=1/sqrt(6).                                   (GDR3)
```

Moreover the leaking coordinate contributes definite mass outside the
intrinsic spectral algebra of `T`:

```text
E_(W^*(T))(C_(B_21))=0,       ||C_(B_21)||_2=1/sqrt(6). (GDR4)
```

Thus maximal named-root leakage, exact unbalanced closure, exact
stable-letter centrality of the whole generator tuple, positive
generator-diagonal gap, and aligned off-spectral mass are mutually
compatible.  No dimension-free inequality assembled only from those data
can charge the distinguished separator.

The packet violates the additional base relation `B_21^2=1` in the test
matrix range (its value squares to `-I`).  It is therefore not an
arithmetic HNN microstate and does not refute
`sl3-hnn-finite-window-central-dual-gap`.  It proves that the shortcut must
use further approximate `SL_3` relations to build a ucp comparison point;
the special choice `C_s=X_s/sqrt(|S|)` does not remove the matrix-order
seam isolated by the earlier root-leak firewall.

The artificial omission is quantitatively exact rather than cosmetic.
`test-involution-pays-free-envelope-gap` proves that for the test envelope
which replaces the infinite-order arithmetic root coordinate by the extra
relation `B_21^2=1`, the generator-diagonal gap is at most
`||B_21^2-I||_2^2/(4 sqrt(6))`; this packet attains equality.  This diagnoses
the manufactured `C_2*F_5` gap, but it is not an omitted `SL_3(Z)` root
relation: `x_21(-1)` has infinite order.  Any actual arithmetic residual
must therefore be carried by mixed lattice relations.
