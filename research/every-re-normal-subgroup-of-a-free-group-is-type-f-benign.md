---
rg: 2
id: every-re-normal-subgroup-of-a-free-group-is-type-f-benign
kind: claim
title: "Open: every recursively enumerable normal subgroup of a finitely generated free group is type F benign (the benign half of Higman's theorem with type F witnesses)"
root: true
distinct_from:
  two-occurrence-realizability-is-type-f-benignness: That proves the equivalences, the closure properties, the reduction to Higman's universal group and the halting-subgroup base case; this is the open universal statement those reduce the two-occurrence window to.
  every-finitely-presented-group-embeds-in-an-f-infinity-group: That is an embedding statement, impossible in type F for groups with torsion and blocked above FP_2 for the rope trick; this asks only for a type F group Λ ⊇ F and a type F subgroup Σ with Σ ∩ F = N, which every finite group already satisfies.
---

**OPEN.** For every finite `A` and every normal subgroup `N ⊴ F(A)` that is
recursively enumerable, there are a group `Λ ⊇ F(A)` of type `F` and a
subgroup `Σ ≤ Λ` of type `F` with `Σ ∩ F(A) = N`.

**Equivalent forms** (`two-occurrence-realizability-is-type-f-benignness`,
items 1 and 3).
- It is equivalent to the same statement for the single relation subgroup
  `N_U ⊴ F(B)` of Higman's universal finitely presented group `U`, which is the
  normal closure of finitely many words.
- It is equivalent to: every finitely generated recursively presented group
  `G` is a section `D/(D ∩ Σ)` of a type `F` group, with `Σ` of type `F`.
- It is equivalent to: every such `G` has a type `F` Mikhailova triple
  `(H, S, phi)` with `WP(G) = phi^{-1}(S)`.
- It is equivalent to: the torsion-free, finitely generated, recursively
  presented double `F(B) *_{N_U} F(B)` embeds in a group of type `F`
  (`type-f-benignness-is-embedding-of-the-double`). Its `F_m` version is
  implied by `E_m`, the universal form of Zaremsky 1.1. Conversely, a
  counterexample to its `F_{n+1}` version answers Zaremsky 1.1 negatively.

**Why it matters for Zaremsky 1.1.** It implies that every such `WP(G)` reduces
to the word problem of a type `F` group by the inverse-respecting
two-occurrence pattern `X -> [X, q]`. Such reductions are linear-size. This
closes the opposite-sign two-occurrence window for word-problem obstructions
at every level `F_{n+1}`. After that, only the equal-sign pattern `X Q X = Q`
and three occurrences would remain.

**Known.**
- The base case holds for halting subgroups `T_M ≤ Z * Z^2` of modular machines (item 5 of the reduction claim).
- It holds for finite `F/N` and for subgroups of quotients `Γ/M` of type `F` groups by type `F` normal subgroups.
- The classical, finitely presented / finitely generated version is Higman's lemma.

**The exact missing step** is a type `F` witness for joins or normal closures
of type `F` benign subgroups.

## Attempts

- **The normal-closure lemma is the whole problem, not a step; the classical
  join witness is not even finitely presented** (proposed-established,
  w6-117, 2026-09-18).
  - The statement is equivalent to: `<<C>>` is `F_m`-benign for every
    finitely generated `C ≤ F`.
  - It follows from: every finitely generated subgroup of `F × F` is
    `F_m`-benign. One join suffices: `<C × 1, ΔF> ∩ (F × 1) = <<C>> × 1`.
  - The classical witness for that join is the Mikhailova fibre product
    `F ×_P F`, which is not finitely presented for infinite `P` (BHMS).
  - See `type-f-normal-closure-lemma-is-the-whole-benign-problem`.
- **Separable witnesses are dead** (proposed-established, w6-117).
  - If `Σ` is profinitely closed in `Λ`, then `F/N` is residually finite.
  - `U` is not residually finite, so every witness for `N_U` has a
    non-closed `Σ`.
  - This kills, as a class: LERF hosts, virtual retracts of residually finite
    hosts, type `FP_k` subgroups of products of `k` limit groups (so every
    type `F` witness in a product of free groups), and Bestvina--Brady or
    Kropholler-type kernels in residually finite groups.
  - The Boone-tower base case is consistent: its `Σ` is non-separable.
  - See `separable-benign-witness-forces-rf-quotient`.
- **Semidirect join holds for normalized witnesses; the converse is one
  fibre product** (proposed-established, w7-117, 2026-09-18).
  - If `H ≤ K` of type `F` normalizes the witness `Σ` of `L` and `H ∩ L = 1`,
    then `(Λ, ΣH)` witnesses `LH`.
  - (d) is equivalent to benignness of the single fibre product
    `F(B) ×_U F(B)`, and (d) gives type `F` benignness of every r.e.
    subgroup of a free group (the full type `F` Higman benign theorem).
  - Sufficient: `U` embeds in `N_Λ(Σ)/Σ` for a type `F` pair ("`U` is
    Weyl"), which is the same as an `F`-normalized witness for `N_U`.
  - Still open: root ⇒ normalized witness. The Boone-tower witness is not
    normalized.
  - See `normalized-benign-witnesses-give-the-semidirect-join`.
- **The Weyl class is closed under free products and liftable HNN
  extensions; the lift is benignness again** (proposed-established, w8-117,
  2026-09-18).
  - `G_1 * G_2` is Weyl via `(Λ_1 × Σ_2) *_{Σ_1 × Σ_2} (Σ_1 × Λ_2)`. In
    particular `G` Weyl ⇒ `G * Z` Weyl.
  - HNN extensions and amalgams are Weyl when the identification lifts to a
    `Σ`-preserving isomorphism of type `F_m` extensions `A/Σ -> B/Σ`.
  - Lifting forces type `F_m` associated subgroups (Higman's construction
    then needs type `F_m` benign witnesses, so it is circular) and matching
    outer actions on `Σ`.
  - See `weyl-class-closes-under-free-products-and-liftable-hnn`.
- **Obstruction: a normalized witness for `N_U` needs an `Out`-universal
  `Σ`** (proposed-established, w8-117).
  - With `Λ` torsion-free, the outer action of the Weyl group on `Σ` has
    abelian kernel on every finite subgroup (Schur).
  - So `U`'s alternating groups embed in the homologically trivial part of
    `Out(Σ)`.
  - This kills `Σ` free, free abelian, surface, RAAG or with finite `Out`.
  - The Weyl route survives only if some type `F` group has `A_n` in its
    Torelli `Out` for infinitely many `n`.
  - See `u-weyl-pairs-need-out-sigma-to-contain-all-finite-simples`.
- **Kill: `U` is not type `F` Weyl, so the normalized route is dead**
  (proposed-established, w9-117, 2026-09-18).
  - In a torsion-free pair, every elementary abelian `p`-subgroup of
    `N_Λ(Σ)/Σ` has rank `≤ 2 cd Σ + Σ_i rk_p Aut H_i(Σ; Z)`. This is
    Browder's exponent bound on the projective complex `Z ⊗_{ZΣ} P_*`.
  - `U ⊇ (Z/2)^r` for all `r`, so `N_U` has no `F(B)`-normalized type `F`
    witness.
  - The same holds for `V`, `Z/2 ≀ Z` and Grigorchuk's group.
  - What remains for (d) is non-normalized witnesses only, or `F_m` variants
    with torsion in `Λ`.
  - See `type-f-weyl-groups-have-bounded-elementary-abelian-ranks`.
