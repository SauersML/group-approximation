---
rg: 2
id: one-fp-simple-group-contains-every-brin-thompson-subgroup-proof
kind: route
title: Thompson's F acting on dyadic rationals gives a finitely presented simple twisted Brin-Thompson group containing every nV
target: one-fp-simple-group-contains-every-brin-thompson-subgroup
requires:
  - twisted-brin-thompson-finite-presentation-criterion
  - virtually-special-groups-embed-in-some-brin-thompson-group
  - rationals-embed-in-brin-thompson-group-2v
  - bs13-embeds-in-brin-thompson-3v
---

Lane proof, elementary once the imported theorems are granted.

**Item 1.** Check Zaremsky's three conditions (`twisted-brin-thompson-finite-presentation-criterion`,
read from arXiv:2405.18354 and FFWZ arXiv:2603.24687, Theorem B) for `F ↷ D`,
`D = Z[1/2] ∩ (0,1)`.
- `F` is finitely presented (classical: two generators, two relators).
- **Pairs.** `F` acts transitively on increasing pairs `x < y` of points of `D`: for
  dyadic `x < y` and `x' < y'` there is a dyadic PL homeomorphism of `[0,1]` with
  slopes in `2^Z` sending `x ↦ x'` and `y ↦ y'` (glue affine-dyadic maps of the three
  subintervals; this is the standard transitivity of `F` on finite increasing tuples
  of dyadic rationals). Every 2-element subset has exactly one increasing ordering, so
  there is one orbit of 2-element subsets.
- **Stabilizers.** For `x ∈ D`, `Stab_F(x) ≅ F_{[0,x]} × F_{[x,1]} ≅ F × F`, since `x`
  is dyadic. It is finitely generated.
So `DV_F` is finitely presented. `F` acts faithfully on `D`, since `D` is dense, so
`DV_F` is simple (same node, from Belk–Zaremsky).

*Copies of `nV`.* For a finite subset `T ⊆ D` with `|T| = n`, the elements of the
untwisted group `DV` supported on the coordinates in `T` (acting as `g` on the
`C^T` factor of the Cantor cube `C^D` and trivially on the remaining coordinates)
form a subgroup isomorphic to `nV`; `g ↦ g × id` is an injective homomorphism. `D` is
infinite, so every `n` occurs. This is the containment stated in the Belk–Zaremsky
abstract; the coordinate description is from the definition of `SV` and was not
re-read in their TeX.

**Item 2.** Compose embeddings `G ↪ nV ↪ U`. The imported nodes supply the embeddings
of the listed classes. `F, T, V ≤ V = 1V`, every finite group embeds in `V`, and
`Z ≀ Z ≤ V`.

**Item 3.** Put `G = G_1 × … × G_k` acting on `S = ⊔ S_i`, with `G_i` acting on `S_i`
and trivially elsewhere.
- `G` is finitely presented, as a finite direct product of finitely presented groups.
- Faithful, since each factor acts faithfully on its own piece.
- **Pairs.** A 2-element subset lies in one `S_i`, giving finitely many `G_i`-orbits
  there, or meets two pieces `S_i, S_j`. Each orbit of 2-subsets of `S_i` meets at most two orbits of points, and every
  point of `S_i` lies in some 2-subset when `|S_i| ≥ 2`, so `G_i` has finitely many
  orbits on `S_i`. The mixed orbits are then products of finitely many point orbits.
- **Stabilizers.** `Stab_G(s) = Stab_{G_i}(s) × Π_{j≠i} G_j` for `s ∈ S_i`, a finite
  product of finitely generated groups.
- `S` is infinite, so `SV_G` contains every `nV` as in item 1, and `G_i ≤ G ≤ SV_G`.
∎
