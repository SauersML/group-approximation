---
rg: 2
id: theorem-e-vertex-rounds-to-unit-type-representations
kind: claim
title: Every tracial ultraproduct representation of the Theorem E actor rounds on the vertex to unit-type congruence representations
distinct_from:
  hs-normalization-needs-coarse-actor-scale-pinning: that is the conditional assembly from (H1) and the coarse actor gap (H2'); this is (H1) strengthened by an arithmetic unit-type condition, which gives (CCR) with no actor gap.
  approximate-collapse-for-kt-compressor: that asks whether the congruence collapse survives approximate representations against a given commutant; this asks for genuine unit-type rounding on the vertex, after which the collapse is exact on the rounded representations.
  kt-wreath-relative-canonical-actor-exactification: that rounds the actor restriction of canonical wreath microstates to genuine G-representations; this rounds only the vertex, to genuine Gamma-representations of unit type, for every trace-preserving representation of G.
  el-r-polynomial-robust-spectral-gap: that is a uniform spectral gap for almost representations of the vertex; this is a flexible stability statement, strictly stronger.
artifacts:
  - research/artifacts/nh-h1-rounding-2026-09-12.md
---

**OPEN.** Let `Γ = EL_r(F_q[x_1..x_d]) < G = EL_r(F_q[x^(±1)]) ⋊ SL_d(Z)`, with `r, d >= 3`, be the
explicit Theorem E pair, and `F_Γ` a finite generating set of `Γ`. For every trace-preserving
`σ : G -> U(prod_U M_n)`, with coordinates `σ_n`, the following should hold after `o(n)` padding:
- there are genuine representations `π_n : Γ -> U(n')`, with `n'/n -> 1`, such that
  `max_(s ∈ F_Γ) ||σ_n(s) - π_n(s)||_2 -> 0` along `U`;
- each `π_n` factors through `St_r(R_+/I_n)` for a finite-index ideal `I_n` in which every `x_i`
  is a unit.

Equivalently, (H1) of `hs-normalization-needs-coarse-actor-scale-pinning` holds, and the rounding can
be chosen with `tau(1 - P_n) -> 0` in the notation of
`unit-type-vertex-rounding-forces-compressor-commutant-rigidity`. To see this, replace the non-unit
constituents by the trivial representation.

**Payoff.** By that established claim, `σ(G)` normalizes `σ(Γ)' ∩ M`. The Theorem A endgame then
makes the explicit Kun–Thom wreath non-hyperlinear (route
`kt-wreath-nonhyperlinear-via-unit-type-vertex-rounding`).

## Attempts

- **Strict stability.** Impossible. Becker–Lubotzky (arXiv:1809.00632, abstract) prove that infinite
  hyperlinear Kazhdan groups are not strictly HS-stable. This claim is flexible. Flexible HS stability
  of higher-rank Kazhdan groups is open; compare Dogon arXiv:2211.10492 for `Sp_2g(Z)`.
- **Robust spectral gap.** Insufficient. `el-r-polynomial-robust-spectral-gap` gives `(T;FD)_rob`
  for `Γ`, which is strictly weaker than stability and supplies no genuine representation.
- **Characters.** Dead as an obstruction in either direction. Characters of `(R_+, +)` that factor
  through unit-type finite quotients are weak*-dense in the dual. No trace computation separates
  unit-type from non-unit mass.
- **Torus invariance.** Partial at best. Conjugation by `diag(x_i^(±1)) ∈ G` rescales root
  coordinates, and the ultralimit trace is exactly invariant.
  - This kills non-unit congruence factors of bounded nilpotency order.
  - Factors whose nilpotency order grows along `U` pass every fixed test word. That is the ungapped
    valuation-level regime of the cascades in `hs-normalization-needs-coarse-actor-scale-pinning` §5.
- **Genuine actor models.** Consistent. A coordinatewise genuine `G`-representation restricts to a
  unit-type factorization: the kernel ideal of the Laurent ring inverts every `x_i`
  (`char-p-root-torsion-collapse`). So `P_n = 1` there, and a counterexample must be far from
  genuine on the actor.
- **One-compressor groups.** The analogous statement for `<Γ, t>` must fail on the sofic wreath
  models of `kt-single-compressor-canonical-lamps-do-not-exactify-actor`, since nothing in `<Γ, t>`
  inverts the `x_i`. So any proof must use the Laurent torus of `G`.
- **(T)-exact compressor transport (lane nh-unit-type-rounding, 2eda8abf6).** Partial: three
  established lemmas cut the non-unit mass that can survive (H1).
  - **Transport.** `compressor-transport-exactifies-under-vertex-rounding`: property (T) of `Γ`
    makes `π_n` and `π_n ∘ Ad A` exactly equivalent off trace `η_n = 4δ_n^2/κ^2`. Root spectra
    are then total-variation invariant under `χ -> χ ∘ φ_A` at every finite stage.
  - **Projection bound.** `nonunit-projection-bounded-by-root-spectral-mass`:
    `τ(1 - P_n) <= r(r-1)·μ_n(χ|A_nu ≠ 1)`.
  - **Depth profile.** `pure-nonunit-root-mass-is-log-scale-folner`: with
    `depth(χ) = min{k : χ trivial on z^k R_+}` and `z = x_1⋯x_d`, the compressor divides depth by
    `d`. So pure non-unit mass above depth one is at most `η_n(1 + log_d(r(r-1)n'))`.
  - **What survives.** Only three regimes:
    - (i) pure non-unit mass spread over `>= 1/η_n` d-adic depth scales, possible only when
      `δ_n^2 log n` does not tend to 0; this is the Følner escape along the cyclic compressor;
    - (ii) shallow mass, characters of `R_+/(z)`, killed in the ultralimit by torus invariance but
      only weak*;
    - (iii) mixed constituents, nontrivial on both `A_u` and `A_nu`, which depth cannot see.
  - **Not done.** No model realizes (i)–(iii), and nothing here is reviewed. See
    `research/artifacts/nh-unit-type-rounding-2026-09-12.md`.
- **Mixed constituents merge into (i) and (ii) (lane nh-mixed-constituents).** Regime (iii) is gone.
  - **The claim.** `nonunit-component-root-mass-is-log-scale-folner` uses the depth of the non-unit component
    `χ_nu(f) = χ(e_nu f)`. That depth is finite for every character.
  - **Why the old depth missed them.** Whole-character depth is infinite on mixed characters.
  - **The transport step.** The compressor transport acts componentwise: `φ_A^(-1)` preserves the type of every
    maximal ideal, because all entries of `A` are `>= 1`. It also divides non-unit depth by `d`.
  - **The bound.** Pure and mixed non-unit mass above non-unit depth one is at most
    `η_n(1 + log_d(r(r-1)n'))`.
  - **No entanglement.** Mixed irreducibles are tensor products `τ_u ⊗ τ_nu` of the two Steinberg factors.
  - **What remains.** Only (i), the slow-rate spread, and (ii), shallow non-unit mass
    `μ_n(depth_nu = 1)`, which now includes mixed characters whose non-unit component is killed by `zR_+`.
- **Local types under compression (lane nh-unit-type-counterexample, 61450aafd).** Partial: the
  survivors are confined to the origin. `vertex-rounding-non-unit-mass-at-origin`.
  - **Method.** Match two roundings of `Λ = AΓA^(-1)`: the restriction and the transport. Every
    local factor at a maximal ideal `m` has a type `S(m) = {i : x_i ∈ m}`.
  - **Restriction saturates types.** For an all-positive `A`, restriction sends every nonempty type
    to the full type. Transport keeps types.
  - **Intermediate places.** Mass on constituents with an intermediate factor (`∅ ≠ S(m) ≠ {1..d}`)
    is at most `12η_n`. This cuts regimes (ii) and (iii) down to factors at the origin
    `m_0 = (x_1..x_d)`.
  - **Depth.** If `A_jj >= 2`, the origin depth `o_j` of each variable obeys
    `P_n(o_j >= t) <= P_n(o_j >= 2t-1) + 24η_n`.
  - **Fixed quotients.** Constituents factoring through a fixed finite quotient carry mass tending
    to 0 (Kazhdan projection of the finite-index congruence kernel).
  - **What survives, all at the origin:**
    - deep origin mass spread over `>= 1/η_n` dyadic depth scales in every direction;
    - evaluation-at-origin factors;
    - origin factors tensored with unit-type factors at growing levels.
  - **Counterexample shapes killed:** truncations in some but not all variables, and single-scale
    `R_+/m_0^n`. No counterexample model was built. See
    `research/artifacts/nh-unit-type-counterexample-2026-09-12.md`.
