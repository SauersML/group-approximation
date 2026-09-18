---
rg: 2
id: artin-deligne-boundary-actions-are-topologically-free
kind: claim
title: A finite-type Artin group acts faithfully on its Deligne normal-form boundary, topologically freely when irreducible, and so does its quotient by the central Garside power
distinct_from:
  artin-groups-mod-central-garside-power-are-continuous-automatic: that proves the quotient normal form is a continuous automatic structure and claims nothing about faithfulness; this proves the boundary actions are faithful and topologically free.
  artin-normal-form-boundary-full-groups-fix-a-point: that finds the two global fixed points of the Deligne boundary and shows its full group is not simple; this proves that no nontrivial element fixes an open set.
artifacts:
  - research/artifacts/gq-bh-bh-free-15-2026-preprints.md
---

**ESTABLISHED** (lane proof, elementary Garside theory, not reviewed; no priority claimed).

## Why this is needed

Belk--Bleak--Chatterji--Matucci--Perego (BBCMP, preliminary 2026) state in Theorem 2.4
that `A` acts faithfully on `∂L`.
- **What the proof shows.** The printed proof (p. 12) shows only that each Artin
  generator acts nontrivially: `a_i·a_j^∞ = (a_i a_j) a_j^∞`. That does not rule out a
  nontrivial kernel.
- **What is unaffected.** Their embedding into the rational group (Theorem 1.11 via
  Corollary 1.9) is fine. It goes through `A ∗ Z`, whose faithfulness (Theorem 2.9)
  follows from the free-product structure.

## Setting

- `A` is of finite type with atom set `S`, `|S| ≥ 2`, positive monoid `A^+`, Garside
  element `Δ`, and `τ(x) = ΔxΔ^{-1}`. Write `≤` for left divisibility and `∧` for the
  left gcd.
- `x → y` means `pref(xy) = x`. For simples this holds iff `Start(y) ⊆ Fin(x)`, the
  left and right descent sets.
- `∂L` is the BBCMP boundary.
  - Its positive points are the infinite left-greedy forms `z = z_1 z_2 ⋯`, with
    `z_i ∈ (1,Δ]`.
  - Such a point has the ideal `I(z) = ∪_k Div(z_1 ⋯ z_k)`. Distinct positive points
    have distinct ideals, since `z_1⋯z_k = max(I(z) ∩ Div(Δ^k))`.
- **Action of a positive element.** For `p ∈ A^+`, `p·z` is positive and
  `I(p·z) = ∪_n Div(p z_1 ⋯ z_n)`.
  - The first `k` factors of the form of `p z_1⋯z_n` are `(p z_1⋯z_n) ∧ Δ^k`.
  - This is increasing in `n` and stabilizes to the first `k` factors of `p·z`.
- **The quotient.** `z_c = Δ^c` is central, with `c ∈ {1,2}`. The quotient `Ā = A/⟨z_c⟩`,
  its normal form `L̄` and the boundary `∂L̄ = {Δ^p x_1 x_2 ⋯ : 0 ≤ p < c}` are as in
  `artin-groups-mod-central-garside-power-are-continuous-automatic`.

## Statement

1. **Two points suffice.** For distinct atoms `a ≠ b`, the only `g ∈ A` with
   `g·a^∞ = a^∞` and `g·b^∞ = b^∞` is `g = 1`. In particular `A` acts faithfully on
   `∂L`.
2. **Topological freeness.** If `A` is irreducible, no `g ≠ 1` fixes a nonempty open
   subset of `∂L` pointwise.
3. **The quotient.** If `A` is irreducible, `Ā` acts faithfully and topologically freely
   on the compact space `∂L̄`.

## Proof

1. **Reduction to a positive element.**
   - Write `g = Δ^{-k} p` with `k ≥ 0` and `p ∈ A^+`. Then `g·a^∞ = a^∞` gives
     `p·a^∞ = Δ^k·a^∞`.
   - The right side has normal form `Δ^k a a ⋯`, so its ideal contains `Δ^k`. Hence
     `Δ^k ≤ p a^M` for some `M`, and likewise `Δ^k ≤ p b^M` after enlarging `M`.
   - **Gcd distributes.** `p x ∧ p y = p (x ∧ y)`. If `d ≤ px` and `d ≤ py`, then
     `d ∨ p = p e` with `e ≤ x` and `e ≤ y`, by left cancellation.
   - The only positive word for `a^M` is `a^M` itself, since no relation applies. So
     `Div(a^M) = {a^i}` and `a^M ∧ b^M = 1`. Hence `Δ^k ≤ p`, and `g = Δ^{-k}p ∈ A^+`.
   - **The positive case.** Now `g ∈ I(g·a^∞) = I(a^∞) = {a^i}` and likewise
     `g ∈ {b^j}`. So `g = 1`, because `A^+` embeds in `A` and `a^i ≠ b^j` unless
     `i = j = 0`.
2. **Topological freeness.**
   - **Cylinders.** Every nonempty open set of `∂L` contains a cylinder
     `C = {Δ^j x_1 ⋯ x_m w}`, where `j ∈ Z`, `m ≥ 1`, each `x_i ∈ (1,Δ)`, and `w` runs
     over `T(x_m) = {w : x_m → w_1}`. Near `Δ^{±∞}`, the sets `[Δ^{±n}]` contain such
     cylinders.
   - With `h = Δ^j x_1⋯x_m`, left multiplication gives the concatenation, so
     `C = h·T(x_m)`. If `g` fixes `C` pointwise, then `g' = h^{-1}gh` fixes `T(x_m)`
     pointwise.
   - **Two points in `T(x_m)`.** Pick `a ∈ Fin(x_m)`, and `b` with `m_{ab} ≥ 3`, which
     exists because `A` is irreducible.
     - `a^∞ ∈ T(x_m)`.
     - The only positive word for `a b^n` is itself, since it has no alternating factor
       of length `m_{ab}`. So its normal form is `(ab) b^{n-1}`, and
       `a·b^∞ = (ab) b^∞`.
     - `Start(ab) = {a} ⊆ Fin(x_m)`, so `a·b^∞ ∈ T(x_m)`.
   - Then `a^{-1} g' a` fixes `a^∞` and `b^∞`, so it is `1` by item 1, and `g = 1`.
3. **The quotient.**
   - `∂L ∖ {Δ^{±∞}} = {Δ^j q}` is homeomorphic to `Z × Q`, where
     `Q = {q : q_1 ≠ Δ}`. Here `z_c` acts freely by `j ↦ j + c`.
   - The map `(j, q) ↦ (j mod c, q)` is an `A`-equivariant covering onto `∂L̄`. This
     holds because a generator acting on `Δ^p x_1 x_2 ⋯` gives the `∂L`-point
     `Δ^{p'} x'`, reduced mod `z_c`.
   - Suppose `ḡ` fixes a nonempty open `V ⊆ ∂L̄` pointwise.
     - On the preimage of `V`, `g ω = z_c^{k(ω)} ω` with `k` locally constant.
     - On a nonempty open set where `k ≡ k_0`, the element `z_c^{-k_0} g` fixes points,
       so it is `1` by item 2. Hence `ḡ = 1`.
   - Faithfulness is the case `V = ∂L̄`. ∎

## Consequences (lane)

- **The quotient node.** In `artin-groups-mod-central-garside-power-are-continuous-automatic`,
  `Ā` is a continuous automatic group whose action on its normal-form boundary is
  faithful. That is BBCMP's embedding hypothesis, reached without passing through
  `Ā ∗ Z`.
- **Germs.** Topological freeness makes the transformation groupoids `A ⋉ ∂L` and
  `Ā ⋉ ∂L̄` coincide with the groupoids of germs of these actions.
  - If `g` and `h` have the same germ at a point, then `g^{-1}h` fixes a neighbourhood,
    so `g = h`.
  - In particular these groupoids are effective, which is one of Matui's standing
    hypotheses.

## Lesson for general BH

- **Chain points pin the action.** In a Garside-type lattice monoid, a point `a^∞` whose
  divisors form a chain pins the action down. Two chain points already have trivial
  pointwise stabilizer, because gcd distributes and two chains have gcd `1`.
  Irreducibility puts two chain points into every cylinder, and that gives topological
  freeness.
- **Effectiveness is free here.** Matui's effectiveness hypothesis costs nothing for
  Garside boundary groupoids. So is the removal of the two global fixed points
  `Δ^{±∞}`: pass to `Ā = A/⟨Δ^c⟩` on the compact `∂L̄`, and use `A ≤ Ā × Z`.
- **What remains.** Boone--Higman for finite-type Artin groups by boundary hosts
  therefore reduces to `Ā ↷ ∂L̄`. The only remaining gates are the singular germs and
  finiteness. `b3-deligne-boundary-is-nonsingular-rank-three-is-not` shows that the
  singular germs come exactly from commuting atoms.
