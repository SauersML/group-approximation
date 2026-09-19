---
rg: 2
id: elementary-amenable-torsion-free-strong-atiyah
kind: claim
title: Torsion-free elementary amenable groups satisfy the Strong Atiyah Conjecture
distinct_from:
  strong-atiyah-torsion-free: that is the open conjecture over all torsion-free groups; this is Linnell's established theorem for the elementary amenable ones, and is the literature input the refutation uses.
  hnn-torsion-theorem: that is torsion-freeness permanence for HNN extensions, a combinatorial group theory statement; this is integrality of von Neumann ranks for a class of groups already assumed torsion-free.
  torsion-free-higman-embedding: that embeds recursively presented torsion-free groups into finitely presented ones; this asserts an L^2-arithmetic property of elementary amenable ones and involves no embedding and no presentation.
  whitehead-vanishing-torsion-free: that is the open Whitehead conjecture over all torsion-free groups; this is an established Atiyah-type theorem restricted to elementary amenable ones. Different invariant, different class, different status.
artifacts:
  - research/artifacts/strong-atiyah-audit-2026-08-17.md
---

Every torsion-free elementary amenable group satisfies the Strong Atiyah
Conjecture over `C`; equivalently its Linnell division closure is a division
ring, and its complex group algebra is a domain.

Literature import (Linnell).  Recorded verbatim from Fisher--Ng,
arXiv:2606.19606 Section 1.1, read from source 2026-08-17: the Strong Atiyah
Conjecture over `C` is "known for many classes of groups, including all
locally indicable groups, braid groups, **elementary amenable groups**,
virtually compact special groups, and 3-manifold groups", the elementary
amenable entry citing Linnell.

Used by `linnell-skew-field-can-be-centrally-infinite`, where it is the only
external input: the calibration group is solvable, hence elementary amenable,
hence its Linnell closure is a genuine division ring, which is what makes the
faithful embedding of a group with nontrivial defect into it a refutation
rather than a curiosity.

Trust surface: a `requires: []` literature import at survey-pinpoint level.
Linnell's original paper was not read; the survey sentence naming the class
was.  That is enough for the use made of it, since the use is to certify a
*known* case rather than to extend one, but a route needing the theorem's
hypotheses in detail should read the source first.
