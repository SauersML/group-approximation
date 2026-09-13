---
rg: 2
id: virtually-free-groups-embed-in-aut-free-groups-proof
kind: route
title: Embed the free finite-index subgroup by inner automorphisms and induce up
target: virtually-free-groups-embed-in-aut-free-groups
requires:
  - aut-free-embeddability-passes-to-finite-index-overgroups
---

Let `F ≤ G` be free of finite index. A finite-index subgroup of a finitely
generated group is finitely generated, so `F ≅ F_r` for some `r ≥ 0`.

- **r ≥ 2.** `F_r` has trivial centre, so `x ↦ ι_x` embeds `F_r` in
  `Inn(F_r) ≤ Aut(F_r)`.
- **r = 1.** In `F_2 = ⟨x, y⟩`, `ι_x^j = ι_{x^j}` is the identity only for `j = 0`
  (the centre is trivial), so `Z ≅ ⟨ι_x⟩ ≤ Aut(F_2)`.
- **r = 0.** `G` is finite of order `q`; permuting a free basis of `F_q` by the
  regular representation embeds `G` in `Aut(F_q)`.

In every case some finite-index subgroup of `G` embeds in some `Aut(F_k)`, and
item 2 of `aut-free-embeddability-passes-to-finite-index-overgroups` gives
`G ↪ Aut(F_n)`. Item 3 there gives an embedding in some `Out(F_m)`.

**The example.** `Γ(3) = ker(SL_2(Z) → SL_2(Z/3))` is torsion-free (standard for
level `≥ 3`). `SL_2(Z) ≅ Z/4 ∗_{Z/2} Z/6`, and a torsion-free subgroup meets every
vertex stabilizer of the Bass--Serre tree trivially, so it acts freely and is free.
Its index in `SL_2(Z)` is `|SL_2(Z/3)| = 24`, and the orbifold Euler characteristic
of `SL_2(Z)` is `1/4 + 1/6 − 1/2 = −1/12`, so `χ(Γ(3)) = −2` and `Γ(3) ≅ F_3`.
Reduction mod 3 maps `GL_2(Z)` onto `GL_2(Z/3)` (onto `SL_2(Z/3)` from `SL_2(Z)`,
plus `diag(−1, 1)`), and its kernel is `Γ(3)`, since a kernel element has
determinant `≡ 1 mod 3`, hence `= 1`. So `[GL_2(Z) : Γ(3)] = |GL_2(Z/3)| = 48`, and
item 2 of the lemma gives `GL_2(Z) ↪ Aut(F_{48·3}) = Aut(F_144)`.
