---
rg: 2
id: disjoint-footprint-decoders-proof
kind: route
title: Disjoint footprints keep the composite reduced, so the identity is formal
target: disjoint-footprint-decoders-force-kaplansky-failure
requires:
  - formal-polynomial-strict-pairs-need-unstable-linearization
artifacts:
  - research/artifacts/formal-polynomial-strict-pairs-2026-09-12.md
---

Artifact, Section 5.
1. At `g`, a decoder monomial `c prod_((s,j) in T) Y_(s,j)` becomes
   `c prod mu_j((X_(gsm))_(m in F_j))`. The variable sets `g s F_j` are pairwise disjoint, because
   left translation preserves disjointness.
2. A product of reduced polynomials in disjoint variable sets is reduced, and so is a sum of reduced
   polynomials. So every coordinate of the formal composite is reduced.
3. Reduced representatives of functions on `F_q`-points are unique. So each coordinate equals
   `X_(g,i)` formally.
4. By the prerequisite, direct finiteness of `M_n(F_q[G])` would make `tau` bijective. Restriction
   of scalars embeds `M_n(F_q[G])` as a unital subring of `M_(nk)(F_p[G])`.
