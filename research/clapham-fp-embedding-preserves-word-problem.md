---
rg: 2
id: clapham-fp-embedding-preserves-word-problem
kind: claim
title: Every finitely generated group with solvable word problem embeds in a finitely presented group with solvable word problem
distinct_from:
  boone-higman-thompson-simple-envelope: that produces a finitely generated COMPUTABLY presented SIMPLE envelope; this produces a finitely PRESENTED envelope with no simplicity at all. The two adjectives traded are exactly the ones the Boone-Higman conjecture asks to have at once, and neither theorem gives both.
  mikaelian-explicit-higman-embedding: that is an explicit form of Higman's embedding theorem for recursively presented groups, with control on the construction; this is the decidability-preserving refinement, whose content is that the ENVELOPE keeps a solvable word problem, which Higman's theorem alone does not give.
  quantitative-higman-embedding-with-dehn-control: that is a Higman embedding with control on the Dehn function of the envelope; this controls decidability of the envelope's word problem and nothing metric.
  torsion-free-higman-embedding: that is a Higman embedding preserving torsion-freeness; this preserves solvability of the word problem, an algorithmic rather than an algebraic property, and neither refinement is known to imply the other.
  novikov-boone-fp-group-undecidable-word-problem: that exhibits a finitely presented group with unsolvable word problem; this embeds groups on the decidable side into finitely presented groups that stay decidable, so the two statements are about complementary halves of the class of finitely presented groups.
artifacts:
  - research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md
---

Every finitely generated group with solvable word problem embeds in a
finitely presented group with solvable word problem.

Clapham, *An embedding theorem for finitely generated groups*, Proc. London
Math. Soc. (3) 17 (1967), 419--430.  The uniform form -- an algorithm taking
a word-problem algorithm for `G` to a finite presentation of an envelope
together with a word-problem algorithm for the envelope -- is the
Higman--Clapham--Valiev theorem.

**Verification status.**  Bibliographic data and statement confirmed
2026-08-24 (Proc. LMS (3) 17, 419--430; the survey
Belk--Bleak--Matucci--Zaremsky arXiv:2306.16356 cites it in this form, and
the audit `research/artifacts/boone-higman-audit-2026-08-17.md` section D.4
already used it).  The primary paper was not read.

## Why it is worth a node of its own

It is the step that lets a Boone--Higman route assume its input is finitely
presented **without** giving up decidability, and it is free.  Both routes
authored on 2026-08-24 begin with it, and the second one
(`boone-higman-via-shift-higman-compiler`) is unusable without it, because
the compiler statement it reduces to quantifies over finitely presented
groups only.

The prose of `boone-higman-via-finitely-presented-simple-ring-quotient`
already used the theorem without a node; that reference now has one.
