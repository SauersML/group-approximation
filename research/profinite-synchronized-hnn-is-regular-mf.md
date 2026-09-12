---
rg: 2
id: profinite-synchronized-hnn-is-regular-mf
kind: claim
title: Profinite-synchronized edge embeddings give a regular-MF HNN extension
distinct_from:
  regular-mf-central-hnn-closure: that treats the identical edge map using Shulman's central-HNN theorem; this permits two different edge embeddings but requires synchronized finite quotients.
  mf-safe-asymmetric-hnn-replacement: that asks for an effective gadget for the Higman rope edge; this is a permanence theorem once a concrete finite-quotient synchronization has been supplied.
  hnn-mark-collapse-requires-profinite-edge-incompatibility: that detects a necessary profinite mismatch for one collapse phenomenon; this gives a sufficient positive MF criterion from equality of the two edge kernels in a cofinal quotient family.
---

Let `A` and `S` be countable groups and let

```text
theta_0, theta_1 : S -> A
```

be injective homomorphisms.  Suppose there is a sequence of finite quotients
`p_n:A->A_n` such that

```text
every a!=1 survives in p_n for all sufficiently large n,       (PSH1)
ker(p_n o theta_0)=ker(p_n o theta_1) for every n.              (PSH2)
```

Then the HNN extension

```text
H=<A,t | t theta_0(s) t^-1=theta_1(s), s in S>                 (PSH3)
```

is regularly operator-MF realized.  In particular, `H` is MF in the
norm-matrix-corona sense.

The proof uses the regular representations of the finite quotients.  Equal
kernels in `(PSH2)` make the two restricted representations unitarily
conjugate at every coordinate.  Ueda's universal-HNN corner identification
and Shulman's compatible-corona criterion then make the ambient universal
C-star HNN algebra MF.  The regular ultralimit trace and the reduced HNN
normal form prove that the abstract group in `(PSH3)` embeds in that algebra
and retain its regular character.

