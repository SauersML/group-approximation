---
rg: 2
id: profinite-integer-function-groups-are-free-citation
kind: route
title: "Import Nöbeling's theorem on continuous integer-valued functions on profinite spaces"
target: profinite-integer-function-groups-are-free
requires: []
---

Citation import.

- Original source: G. Nöbeling, "Verallgemeinerung eines Satzes von Herrn
  E. Specker", Invent. Math. 6 (1968), Satz 1. That paper proves the more
  general statement that the bounded functions from any set to `Z` form a free
  abelian group. It was not opened here.
- Statement read on 2026-09-16 from the LaTeX source of D. Asgeirsson,
  "Towards solid abelian groups: A formal proof of Nöbeling's theorem",
  arXiv:2309.07252v2 (revised 28 May 2024), §4 "The theorem", Theorem 18:

  > (Nöbeling's theorem). Let `S` be a profinite space. Then the abelian group
  > `C(S, Z)` of continuous maps from `S` to `Z` is free.

- The same paper records a complete formalization in Lean 4 / Mathlib, as the
  instance `LocallyConstant.freeOfProfinite (S : Profinite) :
  Module.Free ℤ (LocallyConstant S ℤ)`. Its introduction says the special case
  is Satz 1 of Nöbeling's paper.
- The number 18 comes from counting the theorem-like environments before it in
  the source, which share one counter under the LIPIcs class.
