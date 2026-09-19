---
rg: 2
id: osin-acylindrical-trichotomy-and-cayley-models
kind: claim
title: Osin - a group acting acylindrically on a hyperbolic space is elliptic, virtually cyclic loxodromic, or non-elementary, and a non-elementary acylindrical action upgrades to an acylindrical hyperbolic Cayley graph
distinct_from:
  fpbs-osin-ah-groups-not-products-not-torsion: that imports Osin's corollary on products and torsion from the same paper; this imports the trichotomy (Theorem 1.1) and the equivalence of the definitions (Theorem 1.2), which that node does not state.
  fa-groups-finitely-many-homs-to-rel-hyperbolic-groups: that is the Drutu--Sapir finiteness theorem for relatively hyperbolic targets; this is the basic structure theory of acylindrical actions, and contains no finiteness statement about homomorphisms.
artifacts:
  - research/osin-acylindrical-trichotomy-and-cayley-models-citation.md
---

**ESTABLISHED** by import: `osin-acylindrical-trichotomy-and-cayley-models-citation`.

D. Osin, *Acylindrically hyperbolic groups*, arXiv:1304.1246v4 (16 Apr 2015); Trans. Amer. Math.
Soc. 368 (2016), 851--888.

**(AC) Acylindricity** (Introduction, p. 1). An isometric action of `G` on a metric space `S` is
*acylindrical* if for every `ε > 0` there are `R, N > 0` such that for all `x, y` with
`d(x, y) ≥ R`, at most `N` elements `g` satisfy `d(x, gx) ≤ ε` and `d(y, gy) ≤ ε`.

**(O1) Theorem 1.1.** A group acting acylindrically on a hyperbolic space satisfies exactly one of:
(a) bounded orbits; (b) virtually cyclic and containing a loxodromic element; (c) infinitely many
independent loxodromic elements. For acylindrical actions, non-elementarity (limit set with more
than two points) is equivalent to (c).

**(O2) Theorem 1.2 and Definition 1.3.** The following are equivalent, and define *acylindrically
hyperbolic*:
- (AH1) there is a generating set `X` of `G` with `Γ(G, X)` hyperbolic, `|∂Γ(G, X)| > 2`, and the
  action of `G` on `Γ(G, X)` acylindrical;
- (AH2) `G` admits a non-elementary acylindrical action on a hyperbolic space.

The action in (AH1) is cobounded; Osin notes that those in (AH2) need not be.

Status records an imported theorem, not independent verification.

**Consumer.** `acylindrical-hosts-break-witness-host-inner-pigeonhole`.
