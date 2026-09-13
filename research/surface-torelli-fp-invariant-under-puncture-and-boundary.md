---
rg: 2
id: surface-torelli-fp-invariant-under-puncture-and-boundary
kind: claim
title: "For g >= 2 the surface Torelli group is finitely presented closed iff with one marked point iff with one boundary component"
---

Fix `g >= 2`. Let `S_g` be the closed oriented genus `g` surface, `S_{g,1}` the same
surface with one marked point, and `S_g^1` the surface with one boundary component.
Let `I_g`, `I_{g,1}` and `I_g^1` be the kernels of the actions of `Mod(S_g)`,
`Mod(S_{g,1})` and `Mod(S_g^1)` on `H_1(S_g; Z) ≅ Z^{2g}`. For `S_g^1`, gluing in a
disk identifies `H_1(S_g^1; Z)` with `H_1(S_g; Z)`. Then

`I_g` finitely presented ⟺ `I_{g,1}` finitely presented ⟺ `I_g^1` finitely presented.

So the surface family of Zaremsky Problem 3.1
(`surface-torelli-groups-fp-for-large-genus`,
`surface-torelli-not-fp-for-infinitely-many-genera`) has the same answer for the
closed surface, one marked point and one boundary component. These are exactly
the cases `b + p <= 1` covered by Kassabov–Putman (Theorem A, `b ∈ {0,1}`) and
by Gaifullin (arXiv:2606.13517, Theorem A). The proof is in
`surface-torelli-fp-invariant-under-puncture-and-boundary-proof`.
