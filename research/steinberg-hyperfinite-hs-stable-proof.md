---
rg: 2
id: steinberg-hyperfinite-hs-stable-proof
kind: route
title: Import the hyperfinite HS stability theorem from the corpus
target: steinberg-hyperfinite-hs-stable
requires: []
artifacts:
  - notes/NOTEPAD.md
---

Corpus import, not a reproof.  The theorem and its proof are at
`notes/NOTEPAD.md:22220-22232`, for the group fixed at `notes/NOTEPAD.md:22149`
(`L=L_(F_2)(1,2)`, `Q=EL_4(L)`, `U=St_5(L)`), with the sources pinned at
`:22249-22253`.

The argument is three lines and rests on two inputs already carried by this
graph.  A von Neumann amenable character of a property-`(T)` group is
finite-dimensional; every finite-dimensional representation of `U` is
trivial, so the only von Neumann amenable character of `U` is the trivial
character, which is already the normalized trace of a one-dimensional
representation.  Dogon--Vigdorovich's character criterion for hyperfinite
HS stability then applies.

The criterion is source-verified: Dogon--Vigdorovich, *Hyperlinearity,
stability and asymptotic spectral gap of higher rank lattices*,
arXiv:2506.20843, Definition 6.1 and Theorem 6.2 -- for finitely generated
`Gamma`, hyperfinite HS stability is equivalent to every von Neumann
amenable character being a limit of finite-dimensional traces.  Two citation
traps, both checked this session.  This is **not** Hadwin--Shulman's
theorem (arXiv:1706.08405, J. Funct. Anal. 275 (2018) 761--792), whose
Theorem 3 is one-directional and phrased for *embeddable* characters and
whose converse (Theorem 4) assumes the group amenable; Dogon--Vigdorovich
describe their Theorem 6.2 as a generalization of it.  And
Dogon--Vigdorovich invert the standard convention: their footnote 2 says
their unqualified "Hilbert--Schmidt stable" means *flexibly* stable, and the
Becker--Lubotzky notion is their "strictly HS-stable".  This route imports
only the hyperfinite statement, where no such ambiguity arises.
