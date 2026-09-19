---
rg: 2
id: full-shift-topological-full-group-is-a-t-menable
kind: claim
title: "The topological full group of the two-sided binary full shift has the Haagerup property"
distinct_from:
  sft-topological-full-groups-have-the-haagerup-property: that is Matui's theorem for one-sided shifts of finite type, where the groupoid is expansive in one direction and zipper actions exist; this is the two-sided full shift, whose full group sits inside 2V, which embeds in no zipper group
  full-shift-full-group-kazhdan-subgroups-are-finite: that proves the weaker consequence that Kazhdan subgroups are finite; this asks for a proper cnd function
  brin-thompson-groups-nv-are-a-t-menable: that is the goal for nV; this is a necessary prerequisite of it that lives in the measure-preserving subgroup M_2 of 2V and can fail on its own
---

**OPEN.** `X = {0,1}^Z`, `σ` the shift, and `[[X]]` is the group of homeomorphisms
`f(x) = σ^{k_f(x)} x` with `k_f: X → Z` continuous. The claim: `[[X]]` has a proper
conditionally negative definite function.

## Role

This claim is necessary for `brin-thompson-groups-nv-are-a-t-menable`, by the route
`full-shift-full-group-a-t-menable-from-nv`: `[[X]] ≤ 2V ≤ nV`. By
`nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal`, item 3(c), the copy of `[[X]]` lies in the
Jacobian subgroup `M_2`. So it is invisible to the half (Q_J) of the goal, and it tests only the
part of the goal that is "proper on `M_n`". A refutation here refutes the Haagerup property of every
`nV` with `n ≥ 2`.

## Known

- **Kazhdan subgroups are finite** (`full-shift-full-group-kazhdan-subgroups-are-finite`).
- **Residually finite** (`full-shift-topological-full-group-is-residually-finite`).
- **Contains every right-angled Artin group** (`every-raag-embeds-in-full-shift-topological-full-group`).
  So it contains `F_2 × F_2` and is not amenable.
- **It is a subgroup of the wobbling group of `Z`.** Let `x*` have a dense `σ`-orbit, and identify
  the orbit with `Z` through `j ↦ σ^j x*`. Each `f ∈ [[X]]` acts on it with displacement at most
  `max|k_f|`, and the action is faithful because the orbit is dense. So `[[X]] ↪ W(Z)`, the group
  of bijections of `Z` with bounded displacement. Haagerup for `W(Z)` would imply this claim.
- **No relative-(T) pair built from exponential distortion.** Every orbit ball satisfies
  `|B_S(x, R)| ≤ 2rR + 1`, where `r` bounds the displacement of the generators. By the orbit
  pigeonhole of `subexponential-schreier-growth-excludes-sl3z-and-bs1k` (item 1), no element of
  infinite order is exponentially distorted in a finitely generated subgroup. So `Z^2 ⋊ SL_2(Z)`,
  whose `Z^2` is exponentially distorted, does not embed, and the standard relative-(T) witness to
  non-Haagerup is not available inside `[[X]]`.

## Attempts

- **2026-09-19 (swarm-0917-w16-w16-nv-last1): invariant-measure walls (die; class-kill).**
  - *Class.* `ψ = Σ_k w_k ψ_{ν_k}` with `w_k ≥ 0`, each `ν_k` a `σ`-invariant σ-finite Borel measure,
    and `ψ_ν(g) = ∫ |k_g| dν`. Each `ψ_ν` is cnd. On `X × Z` with `ν ⊗ counting`, let `g` act by
    `(x, t) ↦ (gx, t − k_g(x))`. Every `g ∈ [[X]]` preserves every `σ`-invariant measure, being `σ^k`
    on the pieces of a clopen partition with disjoint images. So `ψ_ν(g)` is the measure of
    `g A Δ A` for the half-space `A = {t ≥ 0}`. The class includes the Maharam wall `ψ_M` of
    `nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal`, item 6(c), restricted to `[[X]]`: under
    `Φ`, Lebesgue measure `λ` becomes the Bernoulli(1/2, 1/2) measure, and `c_1 = −k`.
  - **Reduction.** `k_σ ≡ 1`, so `ψ(σ) = Σ_k w_k ν_k(X)` must be finite. So `ψ = ψ_ν` for the single
    finite invariant measure `ν = Σ_k w_k ν_k`.
  - **Where every member dies.** Choose an aperiodic `x*` with `x*_0 ≠ x*_1`, and let
    `E_m = {x : x_{[−m,m]} = x*_{[−m,m]}}`. Then `E_m ∩ σE_m = ∅`, since a point of both has
    `x_0 = x*_0` and `x_0 = x*_1`. Let `g_m` be `σ` on `E_m`, `σ^{-1}` on `σE_m` and the identity
    elsewhere. This is an involution in `[[X]]`, and the `g_m` are pairwise distinct. Then
    `ψ(g_m) = ν(E_m) + ν(σE_m) = 2ν(E_m) → 2ν({x*}) = 0`: a finite invariant measure has no atom at
    an aperiodic point, because the infinitely many points of its orbit would carry equal mass. So
    `{ψ ≤ δ}` is infinite for every `δ > 0`, and `ψ` is not proper.
  - **Invariant:** invariant measures do not see deep cylinders around aperiodic points.
  - **Surviving:** cnd functions that are not integrals of `|k_g|` against invariant measures, for
    example measured walls over non-invariant but quasi-invariant data, or walls on the orbit space
    `Z` that weight boundary points by local pattern complexity.
- **2026-09-19 (swarm-0917-w16-w16-nv-last1): periodic-point sums (die).** `ψ = Σ_p w_p ψ_p`, where
  `ψ_p(g) = Σ_{x ∈ Per_p} |k_g(x)|` sums over the finite set `Per_p` of points of least period `p`.
  Then `ψ_p = ψ_{ν_p}` for the counting measure `ν_p` on `Per_p`, which is finite and invariant. So
  this is in the class above, and it dies by the same involutions `g_m`. (Finiteness of `ψ(σ)` forces
  `Σ_p w_p |Per_p| < ∞`.)
