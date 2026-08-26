---
rg: 2
id: kt-pair-group-double-is-not-hyperlinear
kind: claim
title: The group double of the Kun--Thom infranormal Kazhdan pair is not hyperlinear
refuted_by:
  - kt-double-mixed-word-trace-selection
distinct_from:
  kt-double-mixed-word-trace-selection: that is the positive side, equivalent to hyperlinearity of the double by the established mixed-word criterion; this is its negation, recorded so that the double decides one of the two program roots either way.
  kt-pair-group-double-is-nonsofic: that is the established nonsoficity of the double (Kun--Thom, version 3); this asks the strictly stronger and open non-hyperlinearity, which would make the double the first non-hyperlinear group.
  kt-centralizer-normalization-hs: that is the rigidity input for refuting hyperlinearity of the coset WREATH through Theorem A's endgame; this is the corresponding open statement for the DOUBLE, which no wreath route implies, since the wreath is only a quotient of the free-lamp group containing the double.
---

OPEN.  Let `Gamma < G` be the Kun--Thom Theorem E pair and
`D = G *_Gamma G`.  Claim: `D` is not hyperlinear, i.e. by
`kt-double-hyperlinear-iff-mixed-word-trace-selection` the mixed reduced-word
trace data `(KMW1)--(KMW4)` do not exist.

**Why the double is win-win.**  `D` is nonsofic
(`kt-pair-group-double-is-nonsofic`).  If `D` is hyperlinear it is the
Pestov 3.4 separation (`kt-double-mixed-word-selection-yields-hyperlinear-nonsofic`);
if not, it is a finitely generated non-hyperlinear group and closes the main
goal through `non-hyperlinear-from-kt-double`.  Both roots are therefore
served by a decision either way, and the only way to lose is to leave the
double undecided.  The claim is recorded with `refuted_by` pointing at the
positive side so the two nodes stay exact negations.

## Attempts

- **Rigidity-side routes for the wreath do not transfer.**  The coset wreath
  `W` is a quotient of the free-lamp group `E = D x| C_2`, not a subgroup of
  `D`, so a refutation of `hyperlinear-wreath-model` through
  `kt-centralizer-normalization-hs` or `invariant-cartan-completion` says
  nothing about `D`; conversely non-hyperlinearity of `D` would not follow
  from the wreath routes.  A proof must control the mixed reduced words of
  `D` directly (`kt-double-canonical-vertex-marginals-admit-large-amalgam-twists`
  shows that exact vertex data do not suffice).
- **Constraints any refutation may use.**  Every unitary model of `D`
  represents `Gamma` non-amenably (`amenable-kazhdan-models-absorb-compression`),
  and splits into an atomic corner that is never faithful, a corner with the
  regular `Gamma`-character mod center, and a remainder carrying
  compression-fixed mixtures of infinite-index Lavi--Levit induced
  characters when `r >= d + 2`
  (`kt-remainder-corner-characters-are-infinite-index-induced`).  A
  refutation of the regular corner alone is the canonical question; a
  refutation of the remainder is `kt-compression-fixed-tracial-states-are-atomic-or-regular`.
- **Gao's relative embeddability.**  As for the arithmetic pairs,
  hyperlinearity of `D` is equivalent to relative embeddability of
  `L(Gamma) < L(G)` over `L(Gamma)` in Gao's sense (the argument of
  `sl3-arithmetic-double-hyperlinear-iff-relative-embeddable` is pair-independent);
  no relative-embeddability result is known for a compressed pair.  Not
  attempted here.
