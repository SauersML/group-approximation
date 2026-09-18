---
rg: 2
id: free-minimal-zn-derived-full-groups-are-never-fp
kind: claim
title: For no free minimal action of Z^N on a Cantor set is the derived subgroup of its topological full group finitely presented
distinct_from:
  circle-rotation-zd-derived-full-groups-are-not-fp: that proves non-finite-presentation for codings of free circle-rotation Z^d actions only; this is the general free minimal Z^N case that Matui leaves open.
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

**OPEN** (stated in the expected negative direction; the printed source asks whether
finite presentation can occur). H. Matui, *Topological full groups of étale
groupoids*, arXiv:1602.00383v2 (TeX main.tex l.1402–1406): after recalling that
Grigorchuk–Medynets proved `[[G_φ]]` locally embeddable into finite groups for
minimal `Z`-actions, "which implies that D([[G_φ]]) never be finitely presented",
Matui writes:

> We do not know if D([[G_φ]]) can be finitely presented when φ is a free minimal
> action of Z^N.

**Status on main.** `circle-rotation-zd-derived-full-groups-are-not-fp` (review
PASS) settles one family of free minimal `Z^d` actions. For `N = 1` the answer is
the Grigorchuk–Medynets LEF argument. The natural general route is local
embeddability into finite groups for free minimal `Z^N` actions (an infinite simple
LEF group is not finitely presented). The relevance to Boone–Higman: these groups
are finitely generated, infinite, simple and amenable (`zaremsky-1-10-fp-infinite-simple-amenable-group`),
so a finitely presented one would answer Zaremsky's Problem 1.10.

**Related printed problem.** AIM problem list *Amenability of discrete groups*
(http://aimpl.org/amenablediscrete), section "Topological Full group, IET and PRG",
Problem 2.5: "Find an example of a Z²-action on a Cantor set such that the commutator
subgroup of the topological full group is f.p." This allows Z² actions that are not free
or not minimal. So even if this node holds, the AIM problem stays open for those actions.
Accessed 2026-09-18; recorded in `research/artifacts/gq-bh-openq-lists.md`.
