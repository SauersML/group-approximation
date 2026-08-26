---
rg: 2
id: deligne-triple-cover-is-hyperlinear
kind: claim
title: Deligne's triple cover of Sp4(Z) is hyperlinear
refuted_by:
  - deligne-central-mark-hs-collapse
  - maslov-mod3-projective-defect-gap
invalidates:
  - deligne-central-mark-collapse-via-maslov-sector
  - nonhyperlinear-via-deligne-central-mark-collapse
distinct_from:
  deligne-sector-gap-is-exactly-nonhyperlinearity: that proves that the Maslov defect gap and the one-word central collapse are each equivalent to non-hyperlinearity of the triple cover; this is the positive side, recorded so that the two horns of the cover are exact negations in the graph.
  deligne-central-mark-hs-collapse: that is the negative horn in its one-word analytic form; this is its negation and is refuted by it.
  kt-free-lamp-hnn-group-is-hyperlinear: that is the positive horn for the Kun--Thom free-lamp group, whose nonsoficity is known; this is the positive horn for an arithmetic central extension whose nonsoficity is itself open.
artifacts:
  - research/artifacts/thom-0810-2180-verified.md
---

OPEN (two-sided by design).  Let `1 -> Z/3 -> E_3 -> Sp_4(Z) -> 1` be
Deligne's triple cover, `alpha` the multiplier of a section.  Claim: `E_3`
is hyperlinear; by Thom's Lemma 3.3 (`research/artifacts/thom-0810-2180-verified.md`)
equivalently the twisted group von Neumann algebras `L_(alpha)[Sp_4(Z)]`
and `L_(alpha^2)[Sp_4(Z)]` are Connes embeddable, and by
`deligne-sector-gap-is-exactly-nonhyperlinearity` equivalently the
`alpha`-projective presentation defect of `Sp_4(Z)` has no dimension-free
lower bound.

**Why it is recorded.**  The graph carries the negative horn only (routes
into `non-hyperlinear-group` through the collapse and Maslov-gap claims and
through the LLP lifting square).  Yet the soficity of `E_3` is also open
(`deligne-triple-cover-is-not-sofic`), and the pair (hyperlinear, nonsofic)
would be the Pestov 3.4 separation (`hyperlinear-nonsofic-from-deligne-triple-cover`).
`E_3` is a finitely presented Kazhdan group (finite central extension of a
Kazhdan group), not residually finite (Deligne), whose central mark is
invisible in every finite-dimensional unitary representation
(`deligne-triple-cover-fd-central-invisibility`).

## Attempts

- **Abstract embedding.**  By `abstract-unitary-embedding-upgrades-to-hyperlinear`
  it suffices to embed `E_3` abstractly in `U(N)` for a Connes-embeddable
  `N`, i.e. to find a unitary representation of `E_3` in which `z` is not
  `1` and the group is faithfully represented; any such model has its
  atomic corner blind to `z` (the finite-dimensional representations kill
  `z`), so the faithful part lives on non-amenable corners, and on the
  tempered corner the character of `Sp_4(Z)` is regular by BKKO (trivial
  amenable radical).  The tempered corner is exactly the twisted regular
  setting `L_(alpha)[Sp_4(Z)]`, i.e. the canonical question again.
- **Twisted microstates.**  The sector formulation
  (`deligne-sector-gap-is-exactly-nonhyperlinearity` and the strategies
  artifact `research/artifacts/deligne-maslov-hyperlinear-strategies-2026-08-21.md`)
  asks for `alpha`-projective almost representations of `Sp_4(Z)` with
  vanishing normalized-HS defect; none is known, and Dogon's Corollary 1.9
  (`dogon-sp2g-weak-ucp-nonhyperlinear`) shows they cannot exist if
  `Sp_4(Z)` is weakly ucp-stable.  So this claim is equivalent to the
  failure of weak ucp-stability of `Sp_4(Z)` restricted to this cocycle.
