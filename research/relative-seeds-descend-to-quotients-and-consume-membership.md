---
rg: 2
id: relative-seeds-descend-to-quotients-and-consume-membership
kind: claim
title: A relative seed (an SFT point isolated by a pattern, with stabilizer C) descends to Λ/N for every normal N ≤ C, keeping isolation, density and quantum rigidity, and makes membership in C decidable relative to WP(Λ); so an HNN tower over a Mihailova subgroup of F_2 x F_2 only relocates the seed problem into Q x Q
distinct_from:
  locally-finite-splittings-preserve-rigid-sft-compactifications: that glues seeds over finite-index edge groups; this constrains the relative seeds needed over infinite-index edge groups (CAP rung 1c) and shows which associated subgroups can carry new complexity.
---

**ESTABLISHED** (lane proof, bh-free-56, 2026-09-18; elementary; not reviewed). The item on
rigidity is a sketch.

**Setting.** `Λ` is finitely generated, `W ⊆ A^Λ` is an SFT, and `(g·z)(h) = z(g^{-1}h)`.
- A *relative seed* for `C ≤ Λ` is a point `z_* ∈ W` with `[p] ∩ W = {z_*}` for some finite
  pattern `p` (isolation), and `Stab(z_*) = C`.
- It is *dense* if `Λ·z_*` is dense in `W`.
- `C = 1` is a seed in the sense of SYNTHESIS v6. Gluing an HNN extension over an
  infinite-index `C` needs relative seeds for its associated subgroups
  (`locally-finite-splittings-rigid-compactification-proof`, §5).
- `z_*` is constant on right cosets `Ch`. So a relative seed is a coloring of the Schreier graph
  `C\Λ` that local rules on the Cayley graph of `Λ` force from one pattern.

## Statement

1. **Consumption, quantitatively.** Decidability of membership in `C` is item 3 of
   `relative-seeds-glue-graphs-of-groups-into-class-c` (bh-invent-03), with `g ∈ C` iff `z_*` shows `p`
   at `g^{-1}`. Only the cost bound below is added here.
   - *Modulus.* Let `m(n)` be the least `R` such that every locally admissible pattern on `B_R`
     extending `p` agrees with `z_*` on `B_n`. It is finite by compactness.
   - *Cost.* Words of length `n` are decided after enumerating the patterns on balls up to
     radius `m(n) + r`, where `r` is the rule radius.
2. **Descent.** Let `N ◁ Λ` with `N ≤ C`. Then `z_* = z̄_* ∘ π` for a relative seed `z̄_*` of
   `C/N` in an SFT `W̄` over `Λ/N`. Density descends, and so does quantum rigidity (sketch below).
3. **Mihailova towers relocate.** Let `Q = F_2/N` be finitely presented and
   `M(Q) = {(u,v) : u = v in Q} ≤ F_2 × F_2`.
   - Any relative seed for `M(Q)` descends to a relative seed for the diagonal `Δ_Q ≤ Q × Q`,
     because `N × N ◁ F_2 × F_2` lies in `M(Q)`.
   - Its point has the form `z̄_*(x, y) = c(x^{-1}y)` for a coloring `c : Q → A`, forced by rules
     that multiply on both sides.
   - So the HNN extension `(F_2 × F_2) *_{M(Q)}`, whose word problem is that of `Q`, can enter
     `𝒞` only through a two-sided seed on `Q` itself.

## Proof

1. **Consumption, quantitatively** (the decision procedure is that of the cited item 3).
   - `g·z_* = z_*` iff `g·z_* ∈ [p]`, since `[p] ∩ W = {z_*}`. That holds iff
     `z_*(g^{-1}f) = p(f)` for `f ∈ supp p`.
   - To compute `z_*` on a finite set, enumerate the locally admissible patterns on `B_R` that
     extend `p`, for `R = 1, 2, …`, and stop when they all agree there.
   - Balls are computable from the word problem. Compactness gives termination at
     `R = m(n) + r`.
2. **Descent.**
   - *Right invariance.* For `n ∈ N`, `z_*(hn) = ((h n^{-1} h^{-1})·z_*)(h) = z_*(h)`, since
     `h n^{-1} h^{-1} ∈ N ≤ C`. So `z_*` factors through `π : Λ → Λ/N`.
   - *The SFT.* Put `W̄ = {z̄ : z̄ ∘ π ∈ W}`. A forbidden pattern `φ` on `F` either takes two
     values on one fiber of `π|_F`, and then never occurs in an `N`-invariant point, or pushes
     forward to a pattern `φ̄` on `π(F)`. So `W̄` is an SFT.
   - *Isolation and stabilizer.* If `z̄ ∈ W̄ ∩ [p̄]`, then `z̄ ∘ π ∈ W ∩ [p] = {z_*}`. And
     `ḡ·z̄_* = z̄_*` iff `g ∈ C`.
   - *Density.* If `z̄ ∈ W̄`, then `z̄ ∘ π = lim g_n·z_*`. Each `g_n·z_*` is `N`-invariant,
     since `g_n C g_n^{-1} ⊇ N`, and equals `(ḡ_n·z̄_*) ∘ π`.
   - *Rigidity (sketch).* A `D`-family `(E_ℓ(x̄))` for `W̄` pulls back to `E_ℓ(π h)` on `Λ`. It
     commutes at distance `≤ 2D`, because `π` does not increase distances. It kills the forbidden
     patterns of `W`: the pushed ones by the family property, and the fiber-inconsistent ones
     because distinct letters at one site are orthogonal. So `D`-rigidity of `W` gives it for
     `W̄`.
3. **Mihailova.**
   - `M(Q)` is the preimage of `Δ_Q` under `F_2 × F_2 → Q × Q`, so it contains `N × N`.
   - A point of `A^{Q×Q}` with stabilizer containing `Δ_Q` is constant on the orbits
     `Δ_Q (x, y)`. These are indexed by `x^{-1}y`.
   - `g ∈ M(Q)` iff `[t, g] = 1` in the trivial HNN extension, and Britton's lemma reduces its
     word problem to membership in `M(Q)`, that is, to `WP(Q)`. `∎`

## What this says for rung 1c (machine-simulating HNN towers)

- **Only core-free associated subgroups carry new complexity.** By descent, a relative seed for
  `C` is a relative seed for `C/core(C)` in `Λ/core(C)`. In particular it is a seed of that
  quotient when `C` is normal.
- **Product towers are the wrong test.** Towers over subgroups that contain a normal subgroup,
  such as the Mihailova subgroups of `F_2 × F_2` (the usual source of hard membership in
  products), move the problem into the quotient. There the required object, a two-sided seed on
  `Q`, is at least as strong as a seed on `Q`.
- **The genuine test.** Use a machine subgroup that is core-free: the Aanderaa–Cohen tower
  `Z² * Z ≤ K_M ≤ G_M = K_M *_{T'_M}`, treated rung by rung in
  `aanderaa-cohen-tower-subgroups-are-decidable`. In `K_M`, the finitely generated
  subgroup `T'_M` contains `t(α, β)` iff the modular machine `M` halts at `(0,0)` from `(α, β)`.
  - By item 1, a relative seed for `T'_M` must refute every false membership claim at finite
    distance, so `M` must be total.
  - For total `M` the refutation sits at the rejecting configuration, so the modulus grows with
    the running time. Rigidity must survive that.
- **Still to check.** Core-freeness of `T'_M`. Relative seeds for the rung-1 subgroups of `Z² * Z` are
  in `relative-seeds-glue-graphs-of-groups-into-class-c` (bh-invent-03).

## Lesson for general BH

A relative seed is a finite-type forcing of a Schreier graph. Forcing only ever sees the
core-free part. So complexity can enter `𝒞` through an HNN extension only along a core-free
associated subgroup whose Schreier graph itself computes: a machine configuration graph, not the
Cayley graph of a quotient. Choosing towers built from normal subgroups (products, Mihailova,
fibre products) cannot beat CAP; those towers only move the problem into a quotient.
