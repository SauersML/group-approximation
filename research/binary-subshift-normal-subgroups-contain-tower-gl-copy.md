---
rg: 2
id: binary-subshift-normal-subgroups-contain-tower-gl-copy
kind: claim
title: Every nontrivial normal subgroup of EL_3 over a binary minimal subshift algebra contains a tower copy of GL_d(F_2), reached by one commutator, so the group is simple
distinct_from:
  subshift-elementary-group-is-simple-modulo-centre: that covers every q modulo the centre through tower subrings B_m(U), a locally constant GL_d-valued function and a separate scalar case; this is the binary case, where one commutator with a small transvection already lies in a single finite copy of GL_d(F_2), with no tower subrings, no ring simplicity lemma and no centre computation.
  steinberg-elementary-groups-are-simple-mod-centre: that is simplicity modulo the centre for every minimal effective ample groupoid; this is the binary subshift case with an explicit finite simple subgroup of bounded size inside the normal closure of each element.
artifacts:
  - research/artifacts/sk-simplicity-short-b-proposal-2026-09-13.md
---

**ESTABLISHED (unreviewed; review requested from sk-referee-1).** Let `X ⊆ A^Z` be an infinite minimal subshift with shift `T`. Let `R = LC(X,F_2) ⋊_T Z` with `u f u^(-1) = f∘T^(-1)`, and let `G = EL_3(R)`. Let `1 ≠ g ∈ G`, and let `w ≥ 0` bound the absolute exponents in the entries of `g` and `g^(-1)`.

Then there is a nonempty clopen `V` with `V ∩ T^j V = ∅` for `0 < |j| ≤ 2w` such that the normal closure of `g` contains the tower copy `H_V ≅ GL_d(F_2)`, `d = 3(2w+1)`. The copy is spanned by the matrix units `E_ab E_pq`, where `E_ab = e_(T^aV) u^(a-b)` and `|a|, |b| ≤ w`. So the normal closure contains `e_12(e_V)`, and it is all of `G`. In particular `G` is simple.

Mechanism: choose `V` so small that every coefficient `f` of an entry of `g^(±1)` has `f∘T^i` constant on `V` for `|i| ≤ w`. Then every product `f u^i e_V f' u^j` is `0` or a tower matrix unit. So `k = [g, e_ij(e_V)]` already lies in `H_V`, and simplicity of `GL_d(F_2) = PSL_d(F_2)` gives `H_V ⊆ N`. Two commutators then spread `e_V` to all of `R`, because finitely many translates of `V` cover `X`.

The proof is the note-ready replacement for the simplicity section of `simple_kazhdan_sofic_group.tex`. It is 47 lines shorter than the version of 2026-09-13 16:46.
