---
rg: 2
id: hyperlinear-to-sofic-via-defect-congruence
kind: route
title: Independently match the unitary colours, exactify their good relation defects by quotient, and retain separation through the weighted blow-up
target: hyperlinear-implies-sofic
requires:
  - hs-defect-is-mean-square-sphere-displacement
  - spherical-tight-single-colour-near-perfect-matching
  - partial-schreier-completion-preserves-sofic-loss
  - spherical-relation-defect-pairs-small-chord
  - defect-congruence-exactifies-permutation-table
  - spherical-defect-congruence-preserves-separation
---

Fix a finite multiplication/word window and a target Hamming error `eps`.
Take a sufficiently accurate regular-character unitary microstate.  The
mean-square sphere-displacement identity converts every tested multiplication
defect into a pointwise-small defect outside a set of arbitrarily small
spherical measure.

Choose one sufficiently large iid spherical cloud and, independently across
the finitely many labels, simultaneous arbitrarily tight near-perfect
matchings from `spherical-tight-single-colour-near-perfect-matching`.  Complete
the missing `o(N)` pieces arbitrarily; by
`partial-schreier-completion-preserves-sofic-loss` these pieces can simply be
charged to the exceptional root sets.

On every good root of a relation `gh=k`,
`spherical-relation-defect-pairs-small-chord` places the conflicting outputs
`sigma_g sigma_h(i)` and `sigma_k(i)` on a short chord.  Form the invariant
defect congruence from those good pairs.  The new noncollapse claim supplies a
choice of the tight matchings for which distinct tested words remain
`E`-inequivalent on `1-eps` of the roots.

Now apply `defect-congruence-exactifies-permutation-table`.  Its weighted
blow-up has the same cardinality `N`; every relation has Hamming defect bounded
by the already small exceptional-root fraction, while its exact separation
formula turns the `E`-noncollision conclusion into the required Hamming
separation.  This is a sofic model of the chosen finite window.  Since the
window and `eps` were arbitrary, every hyperlinear group is sofic.

Unlike `hyperlinear-implies-sofic-via-spherical-design`, this route never asks
the final permutations to remain edges of one geometric candidate graph.  The
sphere is used only to make the relator defects geometrically structured
before the quotient exactification.