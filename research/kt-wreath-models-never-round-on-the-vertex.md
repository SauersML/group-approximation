---
rg: 2
id: kt-wreath-models-never-round-on-the-vertex
kind: claim
title: No trace-preserving model of the Kun--Thom wreath rounds on the Kazhdan vertex
distinct_from:
  hs-stable-vertex-rounding-for-every-model: that is (H1) for every actor model, open; this proves (H1) fails at every actor model that extends to a wreath model, which is the converse that node records as not on main
  theorem-e-vertex-rounds-to-unit-type-representations: that asks every actor model to round to unit-type representations, open; this shows an actor model that extends to the wreath has no rounding of any type
  unit-type-vertex-rounding-forces-compressor-commutant-rigidity: that derives normalization of the vertex commutant from one unit-type rounding; this composes it with the root-mass bounds and the rigid defect into a no-go for wreath models
  leavitt-pair-vertex-rounding-is-nonhyperlinearity: that is the nine-leaf Leavitt pair, whose vertex has no finite images; this is the Theorem E pair, where the equivalence needs the unit-type root-mass bounds
  ccr-holds-for-all-genuine-fd-coordinate-models: that proves (CCR) when the whole actor is coordinatewise genuine; this assumes only that the vertex rounds and concludes that no such model extends to the wreath
  theorem-e-congruence-projections-vanish-at-regular-trace: that limits what congruence-kernel projections can capture in a proof of (H1); this proves no (H1) rounding exists at wreath-extendable models
  laurent-vertex-rounds-for-every-model: that asks every actor model to round on the Laurent vertex, open; this shows wreath-extendable models fail even the polynomial-vertex rounding that a Laurent rounding restricts to
artifacts:
  - research/artifacts/q34-bc-witness-hyperlinear-2026-09-12.md
---

**ESTABLISHED.** Setting:
- `Γ = EL_r(F_q[x_1..x_d]) < G = EL_r(F_q[x^(±1)]) ⋊ SL_d(Z)`, with `q` a prime power and `r, d >= 3`,
  is the explicit Theorem E pair, and `F_Γ` is a finite generating set of `Γ`.
- `W = (⊕_(G/Γ) Z/2) ⋊ G` is the Kun--Thom wreath, with lamp `e_x` at the coset `x`.
- `σ : W -> U(∏_U (M_n, tr_n))` is *trace-preserving*: `τ(σ(w)) = 0` for every `w ≠ 1`.
  Its actor coordinates are `σ_n(g)`, unitary representatives of `σ(g)`.

**Claim.** The actor restriction `σ|G` has no (H1) rounding on `Γ`. That is, there are no genuine
representations `π_n : Γ -> U(n')` with `n'/n -> 1` along `U` such that, after `o(n)` padding,
`max_(s ∈ F_Γ) ||σ_n(s) - π_n(s)||_2 -> 0` along `U`.

In diagonal form: there is `ε > 0` such that, for `U`-most `n`, no genuine representation of `Γ` on
`n' <= (1+ε)n` dimensions comes within `ε` of any padding of `σ_n` on `F_Γ`.

**Corollaries.**
1. **(H1) at wreath-extendable models is nonhyperlinearity.** Call an actor model *wreath-extendable* if it
   is the restriction of a trace-preserving model of `W`. The following are equivalent:
   - (H1) holds for every wreath-extendable trace-preserving `σ : G -> U(∏_U M_n)`;
   - no wreath-extendable actor model exists;
   - `W` is not hyperlinear.

   The claim gives the first equivalence. The second holds because a countable group is hyperlinear iff it
   has a trace-preserving model in a matrix ultraproduct. With route
   `kt-wreath-nonhyperlinear-via-unit-type-vertex-rounding`:

   ```text
   (H1) for every model  =>  (H1) at wreath-extendable models  <=>  W not hyperlinear.
   ```

   So `hs-stable-vertex-rounding-for-every-model` asks more than the target only through actor models that
   extend to no wreath model.
2. **What a hyperlinearity proof must build.**
   - A trace-preserving wreath model keeps the vertex uniformly far from every genuine representation, in the
     diagonal sense above.
   - This holds although `Γ` is residually finite and has many finite images.
   - Coordinatewise genuine actor models are the extreme case (`P_n = 1`, see the "Genuine actor models"
     attempt on `theorem-e-vertex-rounds-to-unit-type-representations`). They extend to no wreath model.
3. **The Laurent sibling.**
   - A rounding of `σ|Δ` on `Δ = EL_r(F_q[x^(±1)])` restricts to an (H1) rounding on `Γ` (route
     `unit-type-rounding-via-laurent-vertex-rounding`).
   - So wreath-extendable models also fail `laurent-vertex-rounds-for-every-model`. At those models that claim
     is again nonhyperlinearity of `W`.
4. **The Lean witness.** At `(q, r, d) = (2, 3, 3)` the same bit is hyperlinearity of the Bowen--Chapman Lean
   endpoint `SymmetricDouble Ambient Peripheral`; see `bowen-chapman-witness-is-kt-double-at-q2-r3-d3`.

**Scope.**
- The claim is about models of `W`. Models of the double `G *_Γ G` share the bit only through `RE/C`, and
  that equivalence rebuilds the model. So nothing is claimed about vertex restrictions of double models.
- Nothing is claimed for `R^ω`-valued models whose coordinates are not matrices (artifact §6).
- Every premise is used at one `σ` and one rounding. The unitaries the premises conjugate by (compressors,
  the torus element `diag(x_1, x_1, x_1^(-2), 1, …)`, attractor conjugates) are images of elements of `G`
  under the same `σ` (artifact §3).

Derivation: `kt-wreath-models-never-round-on-the-vertex-proof`.

## Attempts

- **Prove `W` hyperlinear outright.** Not attempted as a construction.
  - By `kt-wreath-hyperlinear-iff-double-hyperlinear` it is Connes embeddability of `L(G) *_(L(Γ)) L(G)`, an
    amalgamated free product over a nonamenable base.
  - That is an instance of Gao--Junge Problem 1, recorded on `positive-core-dilation-splice`.
  - The claim adds a necessary condition on any such construction.
- **Extend a coordinatewise-genuine actor model.** Dead.
  - `G` is residually finite, so trace-preserving actor models built from genuine finite-quotient representations
    exist.
  - Their vertex rounds exactly (`π_n = σ_n|Γ`), so by the claim none of them extends to a wreath model.
  - A construction that starts from genuine finite-quotient microstates of `Γ` and adds lamps must first move the
    vertex a uniform distance from every genuine representation.
- **Transfer to double models.** Not proved. The rigid defect uses a lamp that commutes with `Γ`, and the
  double has no such element. The `RE/C` equivalence does not keep the vertex restriction.
