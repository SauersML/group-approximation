---
rg: 2
id: stw99-problem-xxxii-z-stable-crossed-products
kind: claim
title: Free minimal actions give Z-stable crossed products, amenable and nonamenable halves (STW Problem XXXII)
root: true
artifacts:
  - research/artifacts/stw99-dynamics-cluster-2026-08-30.md
---

**Problem XXXII of Schafhauser--Tikuisis--White, arXiv:2506.10902**, two
parts.  (1) `G` countably infinite discrete amenable, `X` compact
metrisable of FINITE covering dimension, `G ↷ X` free minimal: is
`C(X) ⋊ G` `Z`-stable?  (2) `G` countable discrete exact non-amenable,
`X` compact metrisable (no dimension restriction), `G ↷ X` free minimal
amenable: is `C(X) ⋊ G` `Z`-stable?

Known: (1) for polynomial growth (SWZ via Rokhlin dimension; also
Hirshberg--Wu long-thin covers), locally subexponential growth
(Kerr--Szabo + Downarowicz--Zhang), all elementary amenable groups
(Kerr--Naryshkin); generic free minimal Cantor actions are almost
finite (CJKMST).  The Giol--Kerr example shows (1) FAILS if the
dimension hypothesis is dropped.  (2) for groups with paradoxical
towers and their products (GGKN), including non-amenable hyperbolic and
Baumslag--Solitar groups; no counterexample candidate is known and no
non-Kirchberg crossed product of such an action has ever been found.

## Attempts

* Both parts follow from Problem XXXIII alone
  (`stw99-xxxiii-implies-xxxii`): finite-dimensional base gives the
  small boundary property for free, so dynamical comparison would give
  almost finiteness (Kerr--Szabo) and then `Z`-stability (Kerr); in
  the non-amenable case invariant measures cannot exist at all, so
  comparison is dynamical pure infiniteness and Ma plus Kirchberg
  finish.  The problem is therefore exactly as hard as dynamical
  comparison on these two classes.
* The known-groups frontier for (1) is the gap between elementary
  amenable and all amenable groups: every positive result to date
  either bounds a dimension (polynomial growth) or runs a
  tiling/exhaustion argument unavailable beyond (locally
  subexponential ∪ elementary amenable); the first test cases outside
  are the (amenable) Grigorchuk-type groups of intermediate growth,
  where neither tool applies and nothing is recorded.
