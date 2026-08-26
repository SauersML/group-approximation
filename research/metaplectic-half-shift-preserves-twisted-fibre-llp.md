---
rg: 2
id: metaplectic-half-shift-preserves-twisted-fibre-llp
kind: claim
title: Tensoring with one exact metaplectic model preserves LLP of every Maslov twisted fibre
distinct_from:
  metaplectic-half-parameter-is-ce: that proves Connes embeddability at the half parameter; this uses the finite quotient behind that proof to obtain an exact projective representation and a mutual ucp-retract equivalence of full twisted C-star algebras.
  maslov-mod3-gap-is-metaplectic-base-degree-six-gap: that transfers projective microstate existence between the one-third and one-sixth parameters; this transfers the local lifting property between the corresponding full twisted C-star algebras.
  twisted-c-star-opposite-inverts-cocycle: that identifies theta with minus theta by taking opposites; this identifies theta with theta plus one-half by a metaplectic matrix amplification and compression.
---

**ESTABLISHED.**  Let `Gamma=Sp_4(Z)`, let `b` be the integral
Meyer--Maslov cocycle, and write

```text
A_theta = C^*(Gamma; exp(2 pi i theta b)).
```

For every `theta in R/Z`, `A_theta` and `A_(theta+1/2)` are mutual ucp
retracts of matrix amplifications of one another.  Consequently

```text
A_theta has LLP  iff  A_(theta+1/2) has LLP.             (MHS1)
```

The point specific to the metaplectic base is that residual finiteness of
the double cover supplies a **finite-dimensional exact** half-projective
representation, not merely approximate half-projective microstates.  Its
tensor product with its conjugate contains the invariant identity vector;
compression to that vector retracts the matrix-amplified half shift.

The proof is `metaplectic-half-shift-ucp-retract-proof`.
