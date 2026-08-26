---
rg: 2
id: one-mixed-a2-word-does-not-control-fold-square
kind: claim
title: One mixed A2 word still leaves the swap fold square free
invalidates:
  - sl3-fold-square-from-one-mixed-a2-word
artifacts:
  - research/one-mixed-a2-fold-countermodel-proof.md
distinct_from:
  unbalanced-torus-and-swap-commutation-do-not-control-fold-square: that exact M2 packet omits the first mixed A2 identity; this exact M4 packet satisfies it as well.
  unbalanced-torus-relator-closes-product-projective-sector: that starts with one exact lattice representation and a single multiplicity unitary; this packet retains independent internal root data and is not a representation of the full lattice.
  sl3-swap-extension-has-defect-only-fold-square-rigidity: that uses every relation of a fixed arithmetic presentation; this refutes only the smaller local interface with one mixed rank-two word.
---

Use the notation of
`unbalanced-torus-and-swap-commutation-do-not-control-fold-square`, including

```text
D_12=A_12 H B_21 H^* A_12 W_12^*,
D_23=A_23 H B_32 H^* A_23 W_23^*,
R_tor=H^*D_12D_23.
```

There is an exact assignment in `M_4` satisfying

```text
S^2=H^*H=I,
[S,A_12]=[S,B_21]=[S,W_12]=[S,E_12]=0,
[S,A_23]=[S,B_32]=[S,W_23]=[S,E_23]=0,             (OMA1)

A_12=E_12^2,             W_12=E_12B_21E_12,
A_23=E_23^2,             W_23=E_23B_32E_23,        (OMA2)

R_tor=I,
W_12E_23W_12^*=[E_12,E_23].                         (OMA3)
```

Nevertheless, for `V=HSH^*S`,

```text
Re tr(V^2)=-1/2,
||V^2-I||_2^2=3,
tr(QPQ-(QPQ)^2)=3/32,                                (OMA4)
```

where `P=(I-S)/2`, `Q=HPH^*`, and traces and Hilbert--Schmidt
norms are normalized.  Thus the first mixed `A_2` identity does not convert
the unbalanced torus closure into a defect-only fold-square estimate.

The packet deliberately omits the rest of the lattice presentation.  It
shows that a proof of the full arithmetic terminal must consume at least one
additional joint rank-two relation.  In particular, merely adding the first
eliminated-root equality to the two separate rank-one packages cannot work.

DERIVATION
one-mixed-a2-fold-countermodel-proof

