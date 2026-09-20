---
rg: 2
id: class-transposition-groups-finite-orbits-is-undecidable-proof
kind: route
title: "Split the class transpositions of bh-free-58's word F_M = s_2 s_1 into the two disjoint-support families; the generated group then has the orbits of the dihedral group ⟨s_1, s_2⟩, which are finite iff F_M has only finite cycles, iff M is periodic"
target: class-transposition-groups-finite-orbits-is-undecidable
requires:
  - ct-z-finite-cycle-problems-are-undecidable
---

Lane proof (bh-k1847, 2026-09-19), not independently reviewed. The argument is in the body of
`class-transposition-groups-finite-orbits-is-undecidable`. It uses:
- from `ct-z-finite-cycle-problems-are-undecidable` (refereed): the set `X`, the map `f`, the
  classes `c(L)` and `λ_c`, and the disjointness of the supports inside `s_1` and inside `s_2`;
  part 1 of its Theorem; its Remark on finite order; and Kari–Ollinger Theorems 3 and 4;
- new: Lemma 1 (orbits of `⟨S_1 ⊔ S_2⟩` equal the orbits of `⟨σ_1, σ_2⟩`), and the standard
  Lemmas 2 (dihedral orbits) and 3 (bounded orbits force a finite group).
