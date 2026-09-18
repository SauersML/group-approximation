---
rg: 2
id: twisted-integral-affine-full-group-is-finitely-presented
kind: claim
title: The derived group of the twisted integral-affine Brin-Thompson full group on Z_2^D is finitely presented; it is simple and contains every GL_n(Z)
distinct_from:
  one-fp-simple-group-contains-every-brin-thompson-subgroup: that is DV_F, where only prefix replacements and coordinate permutations are allowed; this adds integral linear maps on finitely many coordinates, which DV_F is not known to contain.
  fp-self-similar-groups-embed-in-fp-simple-groups: that is Zaremsky's theorem for one self-similar group on one tree; this needs every GL_n(Z) at once, over infinitely many coordinates twisted by F.
---

**OPEN.** Identify `C^D` with `X = Z_2^D` (binary digits). Let `W` be the group of
homeomorphisms `h` of `X` with a finite partition into pieces `P_i`, each a coset of an
open subgroup of `Z_2^{T_i}` (for a finite `T_i ⊆ D`) times the other coordinates, such
that on `P_i`
- `h` permutes coordinates by some `f_i ∈ F` (acting on `D`), and
- on the coordinates in `T_i`, `h` is affine `x ↦ M_i x + b_i` with `M_i ∈ GL_{T_i}(Z[1/2])`
  and `b_i ∈ Z[1/2]^{T_i}`.

**Claim.** The derived subgroup `W'` is finitely presented.

**What is known, and why this suffices.**
- `W` is the topological full group of its groupoid of germs, which is ample, Hausdorff
  (affine maps agreeing on an open set agree on the whole piece), effective and minimal
  (the subgroup `DV_F ≤ W` already has dense orbits). By Nekrashevych (*Simple groups of
  dynamical origin*, ETDS 2019; recalled, not re-read here: minimal implies the
  alternating full group is simple) and Matui's comparison results for purely infinite
  minimal groupoids, `W'` should be simple. The exact hypotheses still need a source read.
- `W ⊇ G_D^E = E(Z; D) ⋊ F` (`finitary-steinberg-extensions-by-oligomorphic-actions-are-fp`),
  acting faithfully: finitary integer matrices act 2-adic-linearly on finitely many
  coordinates, and `F` permutes coordinates. Hence `W ⊇ Σ ⊇ GL_n(Z)` for every `n`.
- `Σ` embeds in `W'`: let `r` be the index reflection `e_k ↦ e_{−k}`, so `r t r^{-1} = t^{-1}`.
  Double `Σ` on two disjoint clopen copies of `X` inside `X`, using `σ` on one and
  `r σ r^{-1}` on the other. The image of `t` becomes a commutator, and `E(Z)` is perfect.
- So the claim gives a finitely presented simple group containing every integral linear
  group: route `integral-linear-one-host-via-twisted-integral-affine-full-group`.

**Why it is plausible.** `W` fuses the two finite-presentation theorems behind the known
Boone–Higman results:
- Zaremsky's twisted Brin–Thompson criterion, where `F ↷ D` is of type `[A_2]`;
- Nekrashevych's and Zaremsky's finite presentation of Röver–Nekrashevych groups of
  finitely presented self-similar groups. The affine groups `Z^n ⋊ GL_n(Z)` on
  `Z_2^n` are finitely presented and self-similar.

The finite presentability of `G_D^E` is the "linear part" of this fusion, proved by
the same orbit-counting that underlies the twisted criterion. What is missing is a
Stein–Farley complex, or a relation-compression argument, mixing the two.

**Obstacle to the naive approach.** Faithful actions of groups containing `E(Z)` by
integral-linear maps carry `Z`-valued pair invariants (the index of `Zv + Zw`), so `W`
cannot be reached as an untwisted `S'V_{G'}` with a type-`[A_2]` action through the
linear action on vectors. The twisting has to stay on the coordinate set `D`.
