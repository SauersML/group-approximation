---
rg: 2
id: howie-locally-indicable-nonsingular-citation
kind: route
title: Import Howie's locally indicable Gerstenhaber--Rothaus theorem as recorded by Klyachko--Thom
target: howie-locally-indicable-nonsingular-equations-are-solvable
requires: []
artifacts:
  - research/artifacts/kl-nonamenable-shapes-2026-09-13.md
---

Citation import, second hand. Source read: A. Klyachko and A. Thom, *New
topological methods to solve equations over groups*, arXiv:1509.01376, file
`main.tex`, fetched on MSI on 2026-09-13. TeX macros are stripped in the quotes.

- **l.112:** Gerstenhaber--Rothaus "studied the more involved question whether
  m equations of the form w_1,…,w_m ∈ G ∗ F_n in n variables can be solved
  simultaneously over G. Their main result is that this is the case if G is
  finite (or more generally, locally residually finite) and the presentation
  two-complex X := K⟨x_1,…,x_n | ε(w_1),…,ε(w_m)⟩ satisfies H_2(X,Z)=0".
- **l.113:** "Later, Howie [MR614523] proved the same result for locally
  indicable groups and conjectured it to hold for all groups -- we call that
  Howie's Conjecture."
- **Bibliography, l.872–878:** MR614523 is J. Howie, *On pairs of 2-complexes and
  systems of equations over groups*, J. Reine Angew. Math. 324 (1981), 165--174.

**Specialization.** With `n = m = 1` and `ε(w_1) = x^d`, the complex `X` has one
0-cell, one 1-cell and one 2-cell whose boundary has degree `d`. So
`H_2(X; Z) = ker(d : Z -> Z)`, which is `0` exactly when `d != 0`.

**Trust surface.** Howie's paper was not read. A fetch of the publisher PDF from
MSI returned an empty file. The attribution and scope are Klyachko--Thom's, and
they agree with the prose record on `kl-holds-over-thompson-v`.
