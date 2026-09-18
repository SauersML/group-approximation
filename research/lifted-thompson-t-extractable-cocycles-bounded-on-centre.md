---
rg: 2
id: lifted-thompson-t-extractable-cocycles-bounded-on-centre
kind: claim
title: "Class-kill for T-bar: every 1-cocycle of the lifted Thompson group T-bar into a representation with a measure extraction on the circle (Koopman on any space over S^1, l2 of orbits in R, Bloch/quasi-periodic families, circle-groupoid representations) is bounded on the centre <z>, by 400 times its values on three fixed elements; so none gives a proper cnd function, and a witness must have almost invariant vectors in a non-extractable part with no z-invariant vectors"
distinct_from:
  nv-extractable-cocycles-bounded-on-centralizers: that is the nV analogue on the Cantor set, with the commuting coordinate copies of V playing the role of the centre; this uses the paradoxical action of T on S^1 against the central translation z of T-bar
  extractable-character-spectra-carry-no-almost-invariant-vectors: that bounds the 1_C-growth for representations of the whole group C(C,Z) ⋊ V; this concerns representations of the subgroup T-bar only, which need not extend
  thompson-t-orbits-carry-no-invariant-means: that is the finite-set Følner obstruction (TC1) for T-orbits, which killed l2 of T-bar-orbits in the w8 attempt; this is the measure-level version, which also covers Koopman, quasi-periodic and groupoid representations
  lifted-thompson-t-center-has-relative-t: that is relative (T) against all cocycles; this is relative (T) only against the extractable class
  lifted-thompson-t-perfect-centre-cubically-elliptic: that bounds z in commensurating actions (discrete walls); this bounds z for Hilbert-space cocycles into extractable representations, including measured walls indexed over S^1
---

**ESTABLISHED** by `lifted-thompson-t-extractable-cocycles-bounded-on-centre-proof`.

**Setting.** `S^1 = R/Z`. `T̄` is the group of lifts of Thompson's `T` to `R`, `g ↦ ḡ` the
projection to `T`, and `z(x) = x + 1`. Fix `h_1, h_2, h_3 ∈ T`, dyadic PL with the listed pieces
(each maps the listed arcs affinely onto the images):
- `h_1`: `[0,1/2) → [0,1/4)`, `[1/2,3/4) → [1/4,1/2)`, `[3/4,1) → [1/2,1)`;
- `h_2`: `[0,1/2) → [1/4,1/2)`, `[1/2,3/4) → [1/2,1)`, `[3/4,1) → [0,1/4)`;
- `h_3`: `x ↦ x + 1/2`.

Fix lifts `ĥ_i ∈ T̄`. For a unitary representation `ρ` of `T̄` put
`c(ρ) = inf_{ξ ≠ 0} Σ_i ‖ρ(ĥ_i)ξ − ξ‖² / ‖ξ‖²`.

**Definition (extraction).** A *circle extraction* for `ρ` on `H` is a map `E` from `H` to finite
positive Borel measures on `S^1` with, for all `ξ, η ∈ H`, `g ∈ T̄` and Borel `B`:
- `E(ξ)(S^1) = ‖ξ‖²`;
- `E(ρ(g)ξ) = ḡ_* E(ξ)`;
- `|E(ξ)(B) − E(η)(B)| ≤ ‖ξ − η‖(‖ξ‖ + ‖η‖)`.

**Theorem.**
1. *(Gap.)* If `ρ` has a circle extraction, then `max_i ‖ρ(ĥ_i)ξ − ξ‖ ≥ ‖ξ‖/10` for all `ξ`, so
   `c(ρ) ≥ 1/100`.
2. *(Centre bound.)* For every `ρ` and every 1-cocycle `b` into `ρ`, with `ψ = ‖b‖²`,
   `c(ρ) · sup_M ψ(z^M) ≤ 4 Σ_i ψ(ĥ_i)`. So if `c(ρ) ≥ 1/100` then
   `sup_M ψ(z^M) ≤ 400 Σ_i ψ(ĥ_i)`.
3. *(Closure.)* `{ρ : c(ρ) ≥ 1/100}` is closed under direct sums, subrepresentations and weak
   containment. If `ρ = ⊕_α ρ_α` and `b = ⊕_α b_α`, the parts with `c(ρ_α) ≥ 1/100` contribute at
   most `400 Σ_i ψ(ĥ_i)` to `sup_M ψ(z^M)` in total.
4. *(Centre-fixed part.)* Let `H^z` be the `z`-fixed vectors (a subrepresentation, since `z` is
   central) and `b_0` the component of `b` in it. Then `b_0(z^M) = 0` for every `M`.

**Examples of extractable representations.**
- *(a) Covariant projection-valued measures.* Any `ρ` with a PVM `P` on `S^1` satisfying
  `ρ(g)P(B)ρ(g)^{-1} = P(ḡB)`, via `E(ξ)(B) = ⟨P(B)ξ, ξ⟩`. This is every representation of the
  crossed product `C(S^1) ⋊ T̄` restricted to `T̄`, equivalently every unitary representation of
  the transformation groupoid `T̄ ⋉ S^1` integrated against a quasi-invariant measure.
- *(b) Koopman over the circle.* `L²(Y, m)` with the unitary Koopman action (Radon-Nikodym
  twist), for any `T̄`-space `Y` with quasi-invariant `m` and a measurable equivariant map
  `Y → S^1`, tensored with any measurable unitary cocycle. Instances: `Y = R` (Lebesgue),
  `Y = S^1`, pair spaces `R × R` or `S^1 × S^1` (first coordinate), the countable orbits
  `Y = T̄·x ⊂ R` (so this subsumes the w8 kill), and measured wall spaces whose walls carry an
  equivariant label in `S^1`. These are cases of (a).
- *(c) Bloch / quasi-periodic families.* For `θ ∈ [0,1)`, `H_θ` is the space of locally `L²`
  functions on `R` with `f(x+1) = e^{2πiθ} f(x)`, normed on `[0,1)`, with
  `(ρ_θ(g)f)(x) = (g^{-1})'(x)^{1/2} f(g^{-1}x)`. Here `z` acts by the scalar `e^{−2πiθ}`, and
  multiplication by `1_{B + Z}` is a covariant PVM. The gap `c(ρ_θ) ≥ 1/100` is uniform in `θ`.
  This is the `s = 0` (unitary) member of the family proposed in step (b) of the w8 attempt on
  `lifted-thompson-t-is-a-t-menable`.
- *(d) Quasi-regular over measure-fixing subgroups.* `ℓ²(T̄/L)` whenever the image of `L` in `T`
  fixes a Borel probability `ν` on `S^1` (for example `L` amenable), via
  `E(Σ c_x δ_x) = Σ |c_x|² x_*ν`. For amenable `L` this is also excluded, more cheaply, by
  non-amenability of `T̄`.

**Corollary (forced shape of a witness).** Suppose `ψ = ‖b‖²` is a cnd function on `T̄` unbounded
on `⟨z⟩`, with cocycle `b` into `ρ`. Write `ρ = ρ_0 ⊕ ρ_1` with `ρ_0` on `H^z`. Then:
- `c(ρ_1) = 0`, so `ρ_1` has almost invariant vectors for `{ĥ_1, ĥ_2, ĥ_3}`;
- `ρ_1` is weakly contained in no representation with a circle extraction, so it is none of
  (a)-(d), nor a direct sum or weak limit of them;
- `ρ_1` has no nonzero `z`-invariant vector.

**Remark (groupoid transfer).** The transformation groupoid splits,
`T̄ ⋉ S^1 ≅ (T ⋉ S^1) × Z`, via the section `σ(g, x)` = the lift of `g` taking the representative
of `x` in `[0,1)` into `[0,1)`, which is multiplicative on composable pairs. So `z` is "free" at
the groupoid level. But every representation of `T̄` obtained by integrating a representation of
this groupoid is of type (a), so this transfer produces no witness.

**Novelty.** The gap is the standard paradoxical argument; the conclusion for the centre uses
only that `z` is central. Not independently reviewed.
