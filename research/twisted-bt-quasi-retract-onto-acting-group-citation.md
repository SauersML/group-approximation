---
rg: 2
id: twisted-bt-quasi-retract-onto-acting-group-citation
kind: route
title: Import the Belk--Zaremsky quasi-retraction of SV_G onto G
target: twisted-brin-thompson-groups-quasi-retract-onto-acting-group
requires: []
---

Citation import. Read on 2026-09-18 from the TeX source of J. Belk and M. C. B. Zaremsky,
*Twisted Brin--Thompson groups*, arXiv:2001.04579. The statement is at TeX l.164 (label
`thm:quasi-retracts`), and the proof is at l.536–550. In this source it is Theorem 2: the introduction is
unnumbered, and theorems are numbered by section only from l.237 on. Other versions may number it
differently, so cite it by label.

The proof fixes a point `κ ∈ C^S` and puts `ρ(h) = gtwist_κ(h)`, the `G`-twist of `h` at `κ`. It then
checks three facts against the generating set `ι_∅(A_G) ∪ ι_1^s(A_G) ∪ (finitely many elements of SV)`
of their Corollary `cor:gen_sets`:
- left multiplication by `ι_∅(a)` multiplies `ρ` by `a`;
- left multiplication by `ι_1^s(a)` multiplies `ρ` by `a` or leaves it unchanged;
- left multiplication by an element of `SV` leaves `ρ` unchanged.

So `ρ` is nonexpanding, and `ρ ∘ ι_∅ = id`. The abstract also states the corollary: "every finitely
generated group embeds quasi-isometrically as a subgroup of a two-generated simple group".
