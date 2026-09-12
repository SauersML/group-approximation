---
rg: 2
id: tabei-radius4-unit-census-citation
kind: route
title: Import Tabei's certified radius-four one-sided census and integral separation theorem
target: promislow-radius4-one-sided-and-integral-separation
requires: []
---

Source: Moe Tabei, *The one-sided unit count of F_2[P] at radius four, and
an integral separation theorem*, arXiv:2608.00103v1 (30 July 2026),
Theorems 1.1 and 1.2 and Proposition 4.1.

For completeness, the proof architecture is as follows.

1. The Promislow group has a free abelian translation subgroup of index
   four.  Left multiplication embeds its group ring into `4 x 4` matrices
   over a three-variable Laurent polynomial ring, so unit-hood is decided
   by the determinant being a signed monomial.
2. Craven--Pappas syllable-length symmetry, intersected over three shifted
   dihedral amalgam decompositions in each coordinate, puts the inverse of
   every radius-four unit inside one explicit `155`-element box (of maximum
   word radius eight).  This removes every a priori inverse-support bound.
3. Exact convolution over `F_2` gives `52` positive witnesses.  Completeness
   is one propositional unsatisfiability after blocking those witnesses; the
   supplied `5.7` GB DRAT proof was independently checked by `drat-trim`.
   Each positive unit and inverse is also verified directly by exact
   determinant and convolution arithmetic.
4. For a hypothetical integral lift write `u=u_0+2s` and
   `u^(-1)=v_0+2t`.  Exact congruence linear algebra modulo four excludes
   `48` of the `52` nontrivial residues.  The other four have an affine
   depth-one solution space of dimension `11`; exhaustive traversal of its
   `2048` points shows that every depth-two system modulo eight is
   inconsistent.  Hence no nontrivial residue lifts.

The theorem is uniform in integral coefficient height.  The cited source
explicitly leaves only the residue-trivial integral Case A at radius four,
and the full one-sided census at radius five, open.  QED
