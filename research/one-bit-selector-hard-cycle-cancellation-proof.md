---
rg: 2
id: one-bit-selector-hard-cycle-cancellation-proof
kind: route
title: The selector flip supplies the reverse hard character at equal multiplicity
target: one-bit-selector-cannot-orient-paired-frame-hard-cycle
requires:
  - one-bit-clifford-selector-halves-a-chosen-bcs-atom
  - paired-frame-hard-characters-form-forced-two-cycle
  - paired-frame-forbidden-scalar-overlap-gap
  - gauge-symmetrizing-hard-pair-cancels-paired-overlap-gap
---

On the forbidden atom, the Clifford relation is `p q p q=-1`; hence
`q p q=-p`.  Conjugation by `q` swaps the two spectral projections of `p`.
Because the current carrier reduces both selector involutions, it contains
the two spectral halves with equal trace and equal packet multiplicity.

The proposed ownership coupling makes this same conjugation implement the
paired-frame automorphism.  The finite edge classification identifies its
two characters as `101` and `011`, and proves that they form a two-cycle.
The equal-multiplicity direct sums are exactly those in `(GHC4)`, so their
Reynolds projections are unitarily conjugate.  The scalar overlap can
therefore be full after summing the selector halves, proving that no positive
oriented deficit survives on a selector-reducing carrier.
