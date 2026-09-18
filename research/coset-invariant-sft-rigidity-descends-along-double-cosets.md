---
rg: 2
id: coset-invariant-sft-rigidity-descends-along-double-cosets
kind: claim
title: For a subshift of right-Δ-invariant configurations, quantum rigidity is commutation propagated across the double-coset space Δ\Λ/Δ, and follows from any determinism descent over it
distinct_from:
  permutive-triangle-sfts-are-quantum-rigid: that is one Z^2 mechanism (triangle permutivity) with trivial Δ; this is a general criterion over any group in which the pair types of the Λ-set Λ/Δ index the induction, and a large Δ collapses most pair types for free.
  quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products: that turns quantum rigidity into finite presentation of the crossed product; this is a sufficient condition for quantum rigidity itself.
  fp-v-times-subshift-full-groups-force-quantum-rigidity: that defines D-quantum families and derives rigidity from finite presentation of a full group; this gives a direct combinatorial proof of rigidity for coset-invariant subshifts.
artifacts:
  - research/artifacts/gq-bh-g2-f2f2-coset-rigidity.md
---

**ESTABLISHED (lane proof, elementary, unreviewed; no priority claimed).** Route:
`coset-invariant-sft-rigidity-descent-proof`.

## Setting

- `Λ` is a group with finite symmetric generating set `S`, word length `|.|` and balls `B_D`.
- `Δ ≤ Λ` is a subgroup with finite generating set `Σ_Δ`. Put `D_0 = max |δ|` over `δ ∈ Σ_Δ`.
- `Ω = Λ/Δ` and `π : Λ -> Ω` is the quotient map. `Λ` acts on `Ω` on the left.
- `X ⊆ A^Λ` is a subshift, with `(g.x)(h) = x(g^(-1)h)`, whose points are **right-Δ-invariant**:
  `x(λδ) = x(λ)` for all `λ ∈ Λ` and `δ ∈ Δ`.
  - Equivalently `X ≅ Z = {z ∈ A^Ω : z∘π ∈ X}` as Λ-spaces. `X` is a *coset shift*.
  - If `Z` is cut out by finitely many forbidden patterns on Λ-balls, `X` is an SFT. The
    Δ-invariance itself is the finite rule `x(λ) = x(λδ)`, `δ ∈ Σ_Δ`.
- **Pair types.** Λ-orbits of pairs `(ω, ω')` in `Ω × Ω` correspond to double cosets
  `θ ∈ Δ\Λ/Δ` via `(λΔ, λ'Δ) -> Δλ^(-1)λ'Δ`. The **span** of `θ` is `s(θ) = min |r|`, `r ∈ θ`.
  Every pair of type `θ` has lifts at distance exactly `s(θ)` in `Λ`.
- `D`-quantum families (Q1)–(Q3) and `D`-quantum rigidity are as in
  `fp-v-times-subshift-full-groups-force-quantum-rigidity`.

## Theorem

Let `D ≥ D_0` and let `E` be a `D`-quantum family for `X` over any field `k`.

1. **E lives on Ω.** `E_a(λδ) = E_a(λ)` for all `δ ∈ Δ`. So `F_a(λΔ) := E_a(λ)` is well defined.
2. **Short types commute for free.** `[F(ω), F(ω')] = 0` whenever the type of `(ω, ω')` has span
   `≤ 2D`.
3. **Descent.** Let `c : Δ\Λ/Δ -> N` and `c_0 ∈ N` satisfy the following.
   - (base) `c(θ) ≤ c_0` implies `s(θ) ≤ 2D`.
   - (step) For every pair `(ω, ω')` of a type `θ` with `c(θ) > c_0`, there are a lift `λ'` of `ω'`
     and a finite set `T ⊆ B_D` with two properties.
     - *determinism*: for every `x ∈ X`, `x(λ')` is a function of `x|_(λ'T)`;
     - *descent*: every pair `(ω, π(λ't))`, `t ∈ T`, has type of `c`-value `< c(θ)`.

   Then all `F_a(ω)` commute, so `X` is `D`-quantum rigid over `k`.

The roles of `ω` and `ω'` may be exchanged at each step, and both sides may be expanded at once,
provided every resulting pair has smaller `c`. This two-sided form contains the row induction of
`permutive-triangle-sfts-are-quantum-rigid` (take `Δ = 1`).

## Two regimes

- **Cornulier regime.** If `Δ\Λ/Δ` is finite, take `c ≡ 0`. Every coset shift is quantum rigid,
  with no determinism at all: `cornulier-regime-coset-sfts-are-quantum-rigid`. The price is paid on
  the dynamical side: `set-transitive-coset-shifts-have-only-constant-minimal-sets`.
- **Descent regime.** If `Δ\Λ/Δ` is infinite, rigidity needs determinism that lowers a complexity of
  pair types.
  - For `Λ = F_2 × F_2` with diagonal `Δ`, the types are the conjugacy classes of `F_2` and the natural
    complexity is cyclic length.
  - That instance collapses: any local cyclic descent forces a finite subshift
    (`two-sided-free-group-coset-sfts-collapse-under-cyclic-descent`). The stabilizer `Δ` rotates
    every determinism rule into every frame.

## Calibration

- `Δ = 1`: the types are the elements of `Λ`, and the theorem is the operator form of "commutation
  spreads through deterministic windows", as in the permutive-triangle and Ledrappier proofs.
- Coset shifts never have homoclinic pairs: two points differ on a union of Δ-cosets, which are
  infinite when `Δ` is infinite. This matches
  `fp-minimal-crossed-products-have-no-homoclinic-pairs`.

## Lesson for general BH

Quantum rigidity, the crux gate G2 of the master route, is a statement about **pair types**, not
about configurations. Commutation is free on pairs whose types are short, and must be carried to all
other types. A large subgroup `Δ` of symmetries of the coding collapses pair types (the double-coset
space), and determinism supplies descent between the remaining ones. Both sources fight freeness:
- **Too few pair types.** Homogeneity (IS) puts constant points into every orbit closure.
- **Rotation by stabilizers.** A large stabilizer rotates determinism into every frame, and descent
  then collapses the subshift to finitely many points.

A rigid free minimal SFT needs stabilizers that merge many pair types but fix a direction, so that its
determinism stays one-sided, as the rows of Ledrappier's shift are.
