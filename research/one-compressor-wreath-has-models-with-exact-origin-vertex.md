---
rg: 2
id: one-compressor-wreath-has-models-with-exact-origin-vertex
kind: claim
title: The one-compressor Kun--Thom wreath has trace-preserving models whose polynomial vertex is exactly genuine at every coordinate
distinct_from:
  kt-wreath-models-never-round-on-the-vertex: that proves no trace-preserving model of the wreath over the full actor G rounds on the vertex; this proves the one-compressor analogue is false, with zero rounding defect.
  kt-single-compressor-canonical-lamps-do-not-exactify-actor: that proves canonical one-compressor wreath microstates stay far from genuine on the actor V; this builds one-compressor wreath models that are genuine on the vertex, with the actor left non-genuine.
  kun-thom-single-compressor-sofic-joint-nonsofic: that proves the one-compressor coset action is sofic through GKP permanence, with no control of the vertex; this gives explicit monomial wreath models with an exact origin-type vertex.
  one-compressor-actor-models-with-exact-origin-vertex: that builds the layered actor models without lamps; this adds Bernoulli lamps to them, so the exact vertex survives wreath extension.
artifacts:
  - research/artifacts/hs-extension-one-compressor-wreath-exact-vertex-2026-09-13.md
  - research/artifacts/hs-extension-one-compressor-origin-layers-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Take the setting and the layered models `σ_N` of
`one-compressor-actor-models-with-exact-origin-vertex`:
- `Γ = EL_r(F_q[x_1..x_d])`, `r >= 3`, `d >= 2`;
- one positive compressor `A`, and `V = <Γ, A>`;
- vertex `π_N = ⊕_(j=0)^N λ∘ψ_j` on `ℓ²({0..N} × Q_0)`, with `A` acting as the layer shift.

Let `W_A = (⊕_(V/Γ) Z/2) ⋊ V`.

**Claim.** Choose a sign `F_N` on the set of `Γ`-orbits `{j} × ψ_j(Γ)g`, and take the root lamp to be
multiplication by `F_N`. For a suitable choice of `F_N`, the maps

```text
ρ_N(ω v)  =  Π_(x ∈ ω) σ_N(v_x) M_(F_N) σ_N(v_x)^*  ·  σ_N(v)
```

define a trace-preserving homomorphism `ρ : W_A -> U(prod_U M_(n_N))`. Every operator is a signed permutation
matrix, and `ρ_N|Γ = π_N` is a genuine representation of `Γ` of pure origin type at every coordinate.

**Key steps** (artifact §§1–4):
- **Separability at the origin level.** If `φ^i(δ)` has entries of degree `< k` and
  `ψ_i(δ) ∈ ψ_i(φ^b Γ)`, then `δ ∈ φ^b Γ`. This is the truncation argument of
  `monomial-ascending-hnn-coset-action-sofic`, with Suslin stability.
- **Distinct orbits.** Distinct cosets in a fixed ball are sent to distinct `Γ`-orbits at every point outside a
  wrap window of density `O(R/N)`.
- **Random lamp.** A uniformly random `F_N` gives products of distinct lamps mean `O(R/N)` and variance
  `O((m+R)/N)`. Chebyshev and a union bound over a slowly growing ball fix one good `F_N`.
- **Group elements.** A nontrivial element of `V` acts without fixed points on `Y` for large `N`. So a lamp product
  times it has trace exactly `0`.

**Consequences.**
- **(H1) at a wreath-extendable model.** For one compressor, (H1) holds with zero defect at a trace-preserving
  wreath model, and every rounding has non-unit mass `-> 1`. The theorem `kt-wreath-models-never-round-on-the-vertex`
  therefore genuinely consumes the second compressor and the torus through the unit-type chain. Wreath extension by
  itself does not obstruct an exact vertex.
- **Non-normalization.** `σ(A)` does not normalize `σ(Γ)' ∩ M`: the lamp at `AΓ` has `||[e_(AΓ), σ(e_12(x_1))]||_2 -> √2`.
  This is the commutant excess of an exact origin vertex, with the actor left non-genuine, as
  `kt-single-compressor-canonical-lamps-do-not-exactify-actor` requires.
- **Reading, not proved.** The construction spends only a Følner set of the compressor shift. An exact vertex at
  wreath models is excluded at `G` only through the two-attractor dynamics, which make the compressor semigroup on
  origin depth profiles non-amenable. See artifact §5.

Derivation: `one-compressor-wreath-exact-vertex-proof`.
