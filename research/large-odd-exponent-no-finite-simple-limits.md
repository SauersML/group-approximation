---
rg: 2
id: large-odd-exponent-no-finite-simple-limits
kind: claim
title: For some large odd exponent, no infinite group of that exponent is a limit of nonabelian finite simple groups
distinct_from:
  large-odd-exponent-lef-burnside-groups-are-finite: that asserts finiteness of LEF groups of the exponent with a fixed number of generators; this forbids infinite limits of finite simple groups of the exponent with any number of generators, which implies it at every number of generators
  large-odd-exponent-local-restricted-burnside: that is the local restricted Burnside principle for finite groups with the exponent law on short words; this is the equivalent statement about limits of finite simple groups
  non-residually-finite-hyperbolic-group: that is the existence of a non-residually-finite hyperbolic group; this is a statement about limits of finite simple groups that implies it
artifacts:
  - research/artifacts/hl-lef-burnside-literature-2026-09-13.md
---

**OPEN.** For some `m >= 2` and some odd `N >= n_1(F_m)`, no infinite finitely
generated group of exponent dividing `N` is the limit, in the space of marked
groups, of a sequence of nonabelian finite simple groups.

This is the negative answer to Caprace's Problem `prob:limits`(ii)
(arXiv:1709.05949, l.1299) at one large odd exponent. Caprace calls
Ivanov--Olshanskii's Problem 2 a more precise version; that paper was not read.

By clause 1 of `lef-burnside-groups-iff-finite-simple-limits`, it is equivalent
at that exponent to: every finitely generated LEF group of exponent dividing `N`
is finite. Route `large-odd-exponent-lef-burnside-via-no-simple-limits` feeds it
into `large-odd-exponent-lef-burnside-groups-are-finite`, and from there into
`non-residually-finite-hyperbolic-group`.

## Attempts

1. **Literature.**
   - Bradford (arXiv:2104.07111, l.1676): "it is not known whether infinite free
     Burnside groups are LEF".
   - Caprace poses the question as Problem `prob:limits`(ii).
   - Verbatim pins: `research/artifacts/hl-lef-burnside-literature-2026-09-13.md`.
2. **Laws are no obstruction as such.** Cornulier (Caprace, Proposition
   `prop:Cor`, l.1315): the metabelian group `C_p ≀ Z` is a limit of alternating
   groups of prime degree. So limits of finite simple groups can satisfy laws.
   The question is specific to the exponent law.
3. **Shape of a counterexample.** By clause 3 of
   `lef-burnside-groups-iff-finite-simple-limits`, a counterexample can be taken
   perfect and without nontrivial finite quotients. Its simple approximants
   eventually avoid every bounded linear degree, so (by CFSG, not pinned) they
   are alternating of unbounded degree or classical of unbounded rank.
4. **What refutes it.** If all hyperbolic groups are residually finite, it fails
   at every large odd exponent. This is clause 4 of the equivalence; Caprace's
   Corollary `cor:Olsh5` and remark (l.1344–1348) give the stronger form for the
   Burnside groups themselves.
