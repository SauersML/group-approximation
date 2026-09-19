---
rg: 2
id: busemann-frontiers-separate-the-boundary
kind: claim
title: For every element g of a non-elementary hyperbolic group, the set of boundary points over which the Busemann difference h(g) - h(1) takes two values separates the Gromov boundary; when countable closed sets do not separate it (spheres of dimension at least 2, and expectedly the Menger curve), this frontier is uncountable, so random groups, the Menger-boundary Kazhdan case, are expected to have unbounded BBMZ hosts as well
requires:
  - bbmz-hosts-with-higher-dimensional-boundary-are-unbounded
  - horofunction-boundary-homology-reduces-to-the-branch-locus
distinct_from:
  bbmz-hosts-with-higher-dimensional-boundary-are-unbounded: that proves uncountable singular sets for reflection groups of dimension at least 3 and leaves Menger-boundary Kazhdan groups as the decisive open case; this gives a general separation theorem for the shear frontier and shows that boundary dimension is not the issue; separation by countable sets is.
---

**Status.**
- **Theorem 1: ESTABLISHED** (lane proof, bh-finf-hyp, 2026-09-19; elementary; not reviewed).
- **Theorem 2** uses one topological input, stated below: proved for spheres, recalled and unverified for the
  Menger curve.
- **The persistence step** linking the frontier to singular points is proved for reflections only.

## Setting

- `Γ` is non-elementary hyperbolic, `φ : ∂_h Γ → ∂Γ` is the finite-to-one quotient map, and `g ∈ Γ` is
  loxodromic.
- `β(η) = η(g^k) − η(1)` for a horofunction `η`, with `k` large (fixed below). It is locally constant on
  `∂_h Γ`, since it depends on two values.
- **Sign regions.** `R_σ = φ({β σ 0})` for `σ ∈ {<, =, >}`. Each is closed, and together they cover `∂Γ`.
- **The shear frontier.** `F = ⋃_{σ≠σ'} R_σ ∩ R_{σ'}`: the points whose fibre carries two signs of `β`.

## Theorem 1 (the frontier separates)

For `k ≥ k_0(g, δ)`, `∂Γ ∖ F` is the disjoint union of the open sets `U_σ = R_σ ∖ ⋃_{σ'≠σ} R_{σ'}`, with `U_<`
and `U_>` nonempty. So `F` separates `∂Γ`.

*Proof.*
- **Openness.** Each `U_σ` is the complement of a finite union of closed sets. The `U_σ` are disjoint and cover
  `∂Γ ∖ F`.
- **`U_<` is nonempty.** For `η` over `ξ`,
  `η(g^k) − η(1) = |g^k| − 2(ξ|g^k)_1 + O(δ)`.
  - For `ξ` in a small neighbourhood of `g^{+∞}`, `(ξ|g^k)_1 ≥ |g^k| − C(g, δ)`.
  - So `β ≤ −|g^k| + 2C + O(δ) < 0` for every horofunction over every such `ξ`, once `k` is large. That
    neighbourhood lies in `U_<`.
- **`U_>` is nonempty.** The same argument near `g^{−∞}` gives `β > 0`. ∎

`sing(g^k) ⊆ ⋃_{i<k} g^{-i} sing(g)`, so a bound on `sing(g^k)` is a bound on `sing(g)` up to translates. This
is why the statement uses powers.

## Theorem 2 (uncountable frontiers)

**Topological input (T0).** No countable closed subset separates `∂Γ`.
- True for `∂Γ ≅ S^m` with `m ≥ 2` (a closed separating set of `S^m` has dimension `≥ m − 1 ≥ 1`).
- Expected for the Menger curve and the Sierpiński carpet (locally connected, no local cut points). This is
  recalled, not checked. Its failure would itself be informative.

Under (T0), `F` is uncountable for every loxodromic `g` and every large `k`. ∎

## What this says about boundedness

- **The persistence step (proved for reflections).** Suppose `ζ = gξ ∈ F_{g}'`, where `F_g'` is the frontier of
  `z ↦ d(g,z) − d(1,z)` (the function that compares `B_n(g)` with `B_m(1)` near `gξ`). One wants `g` singular
  at every horofunction over `ξ`: the fronts toward `ζ` meet both shear regions at every depth.
  - For a reflection this holds, because rays to an endpoint of the wall are asymptotic to the wall
    (`bbmz-hosts-with-higher-dimensional-boundary-are-unbounded`).
  - In general it needs rays to frontier points to stay within bounded distance of the bisector, e.g. conical
    approach. That is open.
- **Conditional consequence.** Given persistence, `sing(g)` contains the fibres over `g^{-1}F_g'`. Under (T0) this
  is uncountable, so the host is **not bounded**.
- **Bounded hosts need countably separable boundaries (expected).** Boundaries that countable closed sets can separate
  are expected to have local cut points (the converse direction of (T0)). By Bowditch, a one-ended `Γ` has local cut points in `∂Γ` exactly when it splits over a
  two-ended subgroup or is virtually Fuchsian.
- **Random groups.** Random groups at any density `< 1/2` do not split, and have Menger-curve boundary
  (Dahmani–Guirardel–Przytycki; recalled). So given (T0) for the Menger curve and persistence, **their BBMZ hosts
  are unbounded**, at low density (cubulated) and in the Kazhdan range `(1/3, 1/2)` alike.

## Consequence for the Kazhdan program

- The Menger regime is expected to fail for the same reason as the sphere regime: countable closed sets do not
  separate the boundary. It is not rescued by being 1-dimensional.
- So `F_∞` simple hosts for Kazhdan hyperbolic groups, through BBMZ-type full groups, need a finiteness theorem for
  **uncountable singular sets**. For those hosts the bounded germ-extension theory (BHM, the level-set lemmas)
  cannot reach any one-ended group without local cut points in its boundary.
- **Cheapest decisive test.** Compute the singular chains of a generator for a small random group at low density
  (C'(1/6), cubulated, with `F_∞` hosts through 2V, so it is only a test).
  - Branching chains would confirm unboundedness.
  - Four clean chains, as for the pentagon, would refute the heuristic.

## Lesson for general BH

- **Singular sets are shear frontiers, and shear frontiers separate.** An element's non-canonical points lie where
  the Busemann difference jumps across a fibre.
- **Those jump sets separate the boundary.** So their size is controlled by the separation topology of `∂Γ`, not by
  its dimension.
- **Consequence.** Finite germ extensions, and with them the whole bounded theory, live exactly on boundaries with
  local cut points, i.e. groups that split over two-ended subgroups or are Fuchsian-like.
