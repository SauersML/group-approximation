---
rg: 2
id: leavitt-regular-atlas-hyperlinearity-criterion-proof
kind: route
title: Regularize both finite atlas factors and descend the universal central extension
target: leavitt-regular-atlas-hyperlinearity-criterion
requires: []
artifacts:
  - notes/EXPLICIT_LEAVITT_ATLAS.md
---

This is the theorem proved in Section 9 of
`notes/EXPLICIT_LEAVITT_ATLAS.md`; the argument is recorded here so it is
canonical Cairn state.

For the forward implication, pull a trace-preserving hyperlinear model of
`Q` back along `bar_rho`.  On each finite factor `K_i~=A_8`, finite-group
normalized-HS stability corrects the restriction to an exact representation,
allowing an `o(d_n)` padding.  Because each nonidentity element of each
`K_i` remains nonidentity in `Q`, the normalized characters of these exact
factor representations converge to the regular character.  Character
orthogonality therefore makes every irreducible multiplicity converge to its
Plancherel proportion.

Take `|A_8|` copies of the corrected model.  Its restriction to either factor
has a common subrepresentation with `d_n` copies of the regular
representation on relative dimension `1-o(1)`.  After unitary conjugacy,
replace each factor by the exact regular representation on the whole space.
Every fixed free-product word changes by `o(1)`, so the finitely many elements
of `bar_S` still converge to the identity.  Align the first factor once and
absorb the second alignment into a single relative unitary `U_n`; this is
exactly the displayed normal form in the claim.

Conversely, a sequence in that normal form killing `bar_S` asymptotically
defines a homomorphism

```text
Psi : U_Q = bar_P/bar_N -> prod_omega U(20160 k_n).
```

It is nontrivial: choose two noncommuting elements in the first `A_8` factor;
their nontrivial commutator has normalized-HS distance `sqrt(2)` from the
identity in the regular representation.  The universal central extension
`U_Q` is quasisimple, so `ker(Psi)` is central.  Its image is hyperlinear and
is a central extension of `Q`; hyperlinearity passes to central quotients.
Hence `Q` is hyperlinear.
