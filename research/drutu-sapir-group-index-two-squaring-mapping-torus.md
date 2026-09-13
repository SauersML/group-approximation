---
rg: 2
id: drutu-sapir-group-index-two-squaring-mapping-torus
kind: claim
title: The Druţu--Sapir group is an ascending HNN extension of F_2, isomorphic to (Z[1/2] * Z[1/2]) ⋊ Z, and contains BS(1,2)
distinct_from:
  drutu-sapir-group-satisfies-boone-higman: that is the open Boone--Higman problem for this group; this is its elementary structure, which records which known theorems cannot reach it.
  virtually-free-by-cyclic-groups-contain-no-bs-one-n: that is a general subgroup obstruction; this supplies the BS(1,2) subgroup it is applied to.
---

**ESTABLISHED** through `drutu-sapir-index-two-reidemeister-schreier-proof`.
It is elementary. Druţu--Sapir surely know this structure, and no priority is
claimed.

Let `DS = <a, b | a^2 b^2 a^-2 b^-1>`. Linton--Nyberg-Brodda, arXiv:2501.18306,
p. 27, call it "the non-linear but residually finite Druţu–Sapir group
⟨a,b | a²b²a⁻²b⁻¹ = 1⟩ studied in [DS05]". Here [DS05] is C. Druţu and M. Sapir,
*Non-linear residually finite groups*, J. Algebra 284 (2005). That source was not
read here.

1. **(DS0) Ascending HNN form.** Put `x = a b a^-1` and `y = a^2 b a^-2`. Then
   `DS = <F(x,y), a | a^-1 x a = y^2, a^-1 y a = x>`, the ascending HNN extension
   of `F_2 = F(x,y)` along the injective endomorphism `ψ(x) = y^2`, `ψ(y) = x`.
2. **(K1) Index two.** The kernel `K` of `DS -> Z/2`, `a ↦ 1`, `b ↦ 0`, is
   `<b_0, b_1, c | c b_0^2 c^-1 = b_0, c b_1^2 c^-1 = b_1>` with `b_0 = b`,
   `b_1 = a b a^-1` and `c = a^2`.
3. **(K2) Amalgam.** `K ≅ BS(1,2) *_<c> BS(1,2)`. In particular `<b, a^2> ≅ BS(1,2)`
   lies in `DS`.
4. **(K3) Squaring torus.** `K` is the ascending HNN extension of `F(b_0, b_1)`
   along `φ = ψ^2`, that is `φ(b_i) = b_i^2`.
5. **(K4) Semidirect form.** `DS ≅ N ⋊ Z` and `K ≅ N ⋊ 2Z`, where
   `N = Z[1/2] * Z[1/2]`. The generator `a^-1` acts by `Ψ`, which maps the first
   factor to the second by `t ↦ 2t` and the second to the first by `t ↦ t`.
   `Ψ^2` is multiplication by `2` on each factor.
6. **(DS1) Torsion.** `DS` is torsion-free. The relator is cyclically reduced of
   prime length 7, so it is not a proper power. Apply the Karrass--Magnus--Solitar
   theorem as quoted in Linton--Nyberg-Brodda, Theorem 1.5.1: "G has elements of
   finite order if and only if r is a proper power in F_A".
