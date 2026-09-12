---
rg: 2
id: boolean-phase-r6-d16-sector-audit-proof
kind: route
title: Compute the guarded AND phase and expose its regular wrong sectors
target: boolean-phase-packet-does-not-wordize-r6-guarded-return
requires:
  - boolean-predicate-central-phase-word
  - regular-finite-controlled-phase-has-half-wrong-mass
  - hadamard-does-not-semidir-independent-selector-blocks
---

# Compute the guarded AND phase and expose its regular wrong sectors

Apply the algebraic-normal-form packet to the cubic monomial `(BPR1)`.  Its
top transvection is the iterated commutator `(BPR2a)`, so substitution of the
commuting native R6 signs makes it trivial.  If assignment irreducibles are
instead externally matched to native selector labels, restrict the finite
regular representation to `<D,c>`.  When `c` is independent of `D`, each
selector character has both phase extensions with equal mass; when it lies
in `D`, it is affine.  Finally an independent D16 tensor makes `c` act
identically on both selector lines, while attempting to normalize a
controlled version through Hadamard forces those blocks equal.  These exact
calculations prove the native-input/coefficient/soundness separation.
