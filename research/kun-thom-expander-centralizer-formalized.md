---
rg: 2
id: kun-thom-expander-centralizer-formalized
kind: claim
title: The Kun-Thom expander-centralizer theorem, proved in the development
distinct_from:
  kun-thom-nonsofic-wreath: That is a later external theorem of the same authors, about generalized wreath products over infranormal Kazhdan pairs, imported as established; this is the expander-centralizer theorem their earlier paper proves, and it is formalized here.
  kun-expander-decomposition-formalized: That produces a union of expanders from property (T) and concludes nothing about any group; this consumes a single expander on the whole approximation set and concludes that the commuting factor is LEF.
  kt-centralizer-normalization-hs: That asks for a Hilbert-Schmidt analogue of the centralizer normalization and is open; this is the permutation-model theorem over the normalized Hamming distance.
artifacts:
  - GroupApproximation/KunThom/KunThomTheorem.lean
  - GroupApproximation/KunThom/KunThomEssential.lean
  - GroupApproximation/KunThom/KunThomCorrelation.lean
  - GroupApproximation/KunThom/KunThomDiagonal.lean
  - GroupApproximation/KunThom/KunThomParameters.lean
---

ESTABLISHED, and proved here rather than quoted.
`KunThom/KunThomTheorem.isLEF_of_exactProductExpansion`: let `K` have property
`(T)` with Kazhdan pair `(Q, κ)`, let `A` be a sofic approximation of `K × J`,
and suppose the first-factor labelled graphs of `A` satisfy a uniform Cheeger
lower bound `h > 0` eventually.  Then `J` is LEF.

Every numerical parameter -- the improvement scale `k`, the tolerances `η`,
`δ`, `β` -- is constructed internally from the Kazhdan and Cheeger constants
(`KunThom/KunThomParameters`), so the statement takes only mathematical data
and never a theorem-shaped callback.
`KunThom/KunThomEssential.isLEF_of_matchingCertificate` is the form the
criterion uses: a `MatchingCertificate` is repaired to an exactly expanding
action first, and the exact theorem then applies.

This is G. Kun and A. Thom, *Inapproximability of actions and Kazhdan's
property (T)*, arXiv:1901.03963.

## The hypothesis that makes it hard to apply

It wants **one** expander on the whole approximation set, while property `(T)`
alone gives a union of them -- [[kun-expander-decomposition-formalized]].  The
hypothesis cannot simply be weakened: a commuting group may move between
components without being LEF, so an arbitrary union really is insufficient.
Supplying a single component is the work of
[[one-sided-compression-nonsofic-criterion]], and it is what makes the
nonsoficity mechanism go through.
