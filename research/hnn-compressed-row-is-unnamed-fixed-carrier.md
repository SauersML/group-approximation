---
rg: 2
id: hnn-compressed-row-is-unnamed-fixed-carrier
kind: claim
title: One compressed HNN intertwining row is an unnamed fixed carrier for a Britton word
distinct_from:
  fanizza-coherent-verifier-wandering-promotion: that asks one stable word to compress to the whole verifier reflection; this uses only one same-letter rectangular intertwining row and never names the returned operator.
  finite-graph-packet-compression-wandering-no-go: that rules out a finite Bass--Serre packet as the source of a representation-independent return; this uses Bass--Serre only to certify wandering and leaves the compressed row as an explicitly matrix-only input.
  two-letter-dihedral-swap-wordizes-one-gram-row: that pays a row between two independently named letters by making its four-letter word a relator; this keeps one base letter on both sides and turns its non-relator HNN commutator into the marked wandering word.
---

Let

```text
Gamma=<B,t | t A t^(-1)=C>
```

be an HNN extension, with the displayed notation abbreviating a fixed
isomorphism from `A` onto `C`.  Let `a in B\(A union C)`, and let
`p=p^*=p^2 in C[B]` commute with `a`.  Put

```text
u=a t a^(-1)t^(-1),          X=t p.                   (HCR1)
```

Then `u` has infinite order and, in every unitary representation into a
finite tracial algebra,

```text
||(u-1)X||_2=||a t p-t p a||_2,
||X||_2^2=tau(p).                                     (HCR2)
```

Equivalently, with the model-dependent range projection

```text
P=t p t^(-1),
```

one has

```text
||(u-1)P||_2=||a t p-t p a||_2.                       (HCR3)
```

Consequently, if fixed packet exactification gives
`tau(p_U)>=alpha-o(1)` and a matrix-only estimate

```text
||a(U)t(U)p_U-t(U)p_Ua(U)||_2=o(1),                   (HCR4)
```

then the projections `P_U=t(U)p_Ut(U)^*` are unnamed positive-density
approximate fixed spaces for the infinite-order word `u`.  In particular

```text
||(u(U)^2-1)P_U||_2=o(1),                              (HCR5)
```

so `unnamed-fixed-space-wandering-promotion` is complete for this
presentation.

This is a non--Bass--Serre division of labor.  Britton normal form supplies
only the infinite wandering word.  The finite graph of groups does not and
cannot supply `(HCR4)`; exact finite packet models remain countermodels to
that inference.  The entire finite-only input has been reduced to one
positive-density compressed same-letter row.

