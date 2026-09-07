---
rg: 2
id: sofic-cyclic-mf-quotient-proof
kind: route
title: Glue a weight-one affine element to a coprime-order two-block lamp word
target: sofic-cyclic-mf-quotient-with-full-radical
requires:
  - finite-block-perfect-lamps-have-exact-mf-radical
  - cyclic-hnn-radical-absorption
artifacts:
  - research/artifacts/sofic-cyclic-mf-quotient.md
  - non_mf_groups_exist.tex
---

Sections 2--3 prove that r=tx^-1 normally generates the affine quotient,
that d=a t b t^-1 has infinite order and normally generates B in E,
and that the two cyclic subgroups have trivial intersection. Apply the
absorption claim. Section 6 verifies Collins--Dykema's sofic HNN theorem
and proves that the kernel is not finitely generated. Section 7 checks
all hypotheses of Bryder--Ivanov--Omland Proposition 4.12 and
Minasyan--Osin Corollary 2.3, giving the Powers and acylindrical conclusions.

These named classical inputs are cited exactly in the artifact; the new
argument is a complete written proof relative to the two prerequisites.
The argument is integrated as Theorem G and Proposition 6.1 of the
manuscript, without adding a Lean verification badge.
