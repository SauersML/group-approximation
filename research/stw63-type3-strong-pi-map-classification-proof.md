---
rg: 2
id: stw63-type3-strong-pi-map-classification-proof
kind: route
title: Establish strong pure infiniteness and apply the internal C-star target theorem
target: stw63-arbitrary-type3-vn-asymptotic-uniqueness
requires:
  - stw63-strongly-purely-infinite-targets-have-uniqueness
artifacts:
  - research/artifacts/stw63-z-embedding-audit-2026-08-30.md
---

Let `M` be any type-III von Neumann algebra, regarded only as a unital
C*-algebra.  Blanchard--Kirchberg, *Non-simple purely infinite C*-algebras:
the Hausdorff case*, explains that an AW*-algebra is type III exactly when
it satisfies their pure-infiniteness conditions.  More precisely, AW*
algebras have real rank zero, and the Kirchberg--Rordam chain through
Corollary 6.9, Proposition 4.7, and Theorem 4.16 says that such an algebra is
strongly purely infinite exactly when all its nonzero projections are
properly infinite.  Equivalently one can invoke Blanchard--Kirchberg
Theorem 4.17.

Thus `M` is a unital strongly purely infinite C*-algebra, with no
separability, nuclearity, factoriality, or sigma-finiteness assumption.
Apply `stw63-strongly-purely-infinite-targets-have-uniqueness`.  It gives
asymptotic unitary equivalence of the two Jiang--Su embeddings directly in
`M`.  Proper norm ideals arising from projection cardinalities cause no
problem: fullness of every nonzero image element is built into the general
target theorem.
