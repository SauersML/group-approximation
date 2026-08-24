---
rg: 2
id: wreath-base-conjugacy-multiset-proof
kind: route
title: Read the conjugation formula and count multisets of a fixed class
target: wreath-base-conjugacy-classes-are-finite-multisets
requires: []
artifacts:
  - research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md
---

Complete direct proof, written out in the target node.  No Lean counterpart
exists.

The only step worth care is the converse: matching two supports of equal size
needs the multisets to agree as multisets and not merely as sets, which is
why the invariant is stated with multiplicity.  Stated with sets it would be
a coarser invariant, still infinite in general but not a complete one, and
the "conversely" paragraph would be false.
