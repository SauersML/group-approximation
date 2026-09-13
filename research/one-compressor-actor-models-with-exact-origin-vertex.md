---
rg: 2
id: one-compressor-actor-models-with-exact-origin-vertex
kind: claim
title: A one-compressor Kun--Thom actor has trace-preserving models that are exact on the polynomial vertex, of pure origin type, and do not normalize the vertex commutant
distinct_from:
  kt-single-compressor-canonical-lamps-do-not-exactify-actor: that proves canonical one-compressor wreath microstates stay far from genuine on the actor; this builds one-compressor actor models whose vertex is exactly genuine and of non-unit type, with a non-normalized commutant.
  theorem-e-vertex-rounds-to-unit-type-representations: that is the open unit-type rounding claim for models of the full actor G; this shows its one-compressor analogue fails at an explicit model and realizes its surviving regime (i).
  vertex-rounding-non-unit-mass-at-origin: that confines the non-unit mass of G-model roundings to the origin, spread over many depth scales; this realizes exactly that shape for one compressor, with the vertex exact.
  nonunit-component-root-mass-is-log-scale-folner: that bounds non-unit mass per d-adic scale by the transport defect; this model attains the bound up to constants.
  kt-wreath-models-never-round-on-the-vertex: that proves no wreath-extendable G-model rounds on the vertex; this shows that for one compressor, rounding and a non-normalized commutant coexist, so that theorem rests on the second compressor and the torus.
artifacts:
  - research/artifacts/hs-extension-one-compressor-origin-layers-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Setting:
- `q` a prime power, `d >= 2`, `r >= 3`, `R_+ = F_q[x_1..x_d]`, `m_0 = (x_1..x_d)`, `Γ = EL_r(R_+)`;
- `A ∈ SL_d(Z)` with every entry `>= 1`, `φ = φ_A` the monomial substitution, and `c_A` the largest column sum
  of `A`;
- `V = <Γ, A> ≤ EL_r(F_q[x^(±1)]) ⋊ SL_d(Z)`, with `AγA^(-1) = φ(γ)`. It is the ascending HNN extension `Γ *_φ`.

**Construction.** For `N >= 1` put `k = N c_A^N`, `Q_0 = EL_r(R_+/m_0^k)`, and `ψ_j = (mod m_0^k)∘φ^j : Γ -> Q_0`.
On `⊕_(j=0)^N ℓ²(Q_0)` let

```text
π_N(γ) = ⊕_j λ(ψ_j(γ)),        σ_N(A) = S,   the cyclic layer shift (S ξ)_j = ξ_(j+1 mod N+1).
```

**Claim.** Let `σ = (σ_N)_U : V -> U(prod_U M_(n_N))` be defined on normal forms `A^(-a)γA^b` by
`S^(-a)π_N(γ)S^b`.
1. **A trace-preserving model.** `σ` is a homomorphism: `||Sπ_N(γ)S^* - π_N(φ(γ))||_2 <= 2/√(N+1)`, with all
   the error on one layer. It is trace-preserving: `τ∘σ = δ_e`.
2. **An exact vertex.** Each `π_N` is a genuine representation of `Γ`. So (H1) holds at `σ` with zero defect.
3. **Pure origin type.** Every constituent of `π_N` factors through `EL_r(R_+/m_0^k)`, a local ring in which every
   `x_i` is nilpotent. The unit-type projection `P_n` of
   `unit-type-vertex-rounding-forces-compressor-commutant-rigidity` has `τ(P_n) -> 0`.
   - By property (T) of `Γ`, any two roundings agree off vanishing trace. So *every* (H1) rounding of `σ|Γ` has
     non-unit mass tending to `1`.
4. **No normalization.** `σ(A)(σ(Γ)' ∩ M)σ(A)^* = σ(φ(Γ))' ∩ M` strictly contains `σ(Γ)' ∩ M`. A symmetry
   `z ∈ σ(φ(Γ))' ∩ M` has `||[z, σ(e_12(x_1))]||_2 >= √2`: on layer `j` it multiplies by a sign that is constant
   on right cosets of `ψ_(j+1)(Γ)`.

**Reading for extension to the actor.**
- **Regime (i) exists.** The one counterexample shape the chain had left open (pure non-unit mass spread over
  `>= 1/η_n` d-adic depth scales) occurs at a model of one compressor.
  - The transport defect is `δ_N <= 2/√(N+1)`, and the `N+1` layers occupy distinct depth scales.
  - So the per-scale bound of `nonunit-component-root-mass-is-log-scale-folner` is sharp up to constants.
- **One compressor forces nothing.** Covariance under a single positive compressor, even exact covariance under
  the whole ascending HNN group, gives neither unit type nor normalization.
  - The torus step (`shallow-nonunit-root-mass-vanishes-under-vertex-rounding`) and the second attractor
    (`vertex-rounding-deep-nonunit-root-mass-vanishes`) are where extension to `G` acts.
  - They act only through an assumed rounding, and they exclude these origin layers.
- **Obstruction to extension.** By that chain, `σ|Γ` is not within `o_2(1)` on `F_Γ` of the vertex restriction of
  any trace-preserving `G`-model.
- **Open.** Whether lamps can be added so that some trace-preserving model of the one-compressor wreath
  `(⊕_(V/Γ) Z/2) ⋊ V` has an exact vertex. Item 4 finds room for the lamp at `AΓ`. What is missing is Bernoulli
  independence of its `Γ`-translates. See artifact §5.4.

Derivation: `one-compressor-actor-models-with-exact-origin-vertex-proof`.
