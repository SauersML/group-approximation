# Commutative rigidity on the square: every function is Dirac on some atomless measure of a compact family (2026-09-13)

Lane `ex2-tw-hilbert-cube-boundary` (EX swarm). Not reviewed. Scope note for Corollary D.2 of
`research/artifacts/ex2-tw-atomless-element-division-2026-09-13.md`.

**Outcome.**
- **Proposition U.** Let `S = [0,1]²`. Some weak*-compact family `𝓜` of atomless probability measures
  on `S` has the following property. Every continuous `f: S → ℝ` has some `μ ∈ 𝓜` with `f_*μ` a Dirac
  measure.
- **Scope.** Corollary D.2 produced the element of Theorem D(ii) from an injective function on a
  zero-dimensional diagonal. A two-dimensional diagonal whose extreme traces restrict to such a family
  supplies no such element. The obstruction is Lebesgue's covering theorem. Commutative tracial
  rigidity is forced by dimension theory already in dimension 2. In the Pauli tower rigidity is
  cohomological.

## Proposition U

**Step 1 (a large level-set component).** For continuous `f: S → ℝ`, some component of some level set
`f^{−1}(c)` has diameter at least 1.
- **Factorization.** The components of the fibres of `f` form an upper semicontinuous decomposition of
  `S`. Let `q: S → Γ` be the quotient, so `Γ` is compact metrizable, and `f = g ∘ q` with `g: Γ → ℝ`
  light (monotone–light factorization).
- **`dim Γ ≤ 1`.** `g` is closed with zero-dimensional fibres, so Hurewicz's formula for closed maps
  gives `dim Γ ≤ dim ℝ + 0 = 1`.
- **Suppose every component has diameter `< 1`.** By upper semicontinuity and compactness the maximum
  `d_0` is attained, so `d_0 < 1`. Put `η = (1 − d_0)/3`. Compactness gives `δ > 0` with
  `q^{−1}(B(γ, δ)) ⊆ N_η(q^{−1}(γ))` for all `γ`.
- **Pull back a cover.** Take a finite open cover of `Γ` of mesh `< δ` and order `≤ 2`. Its preimage is
  a finite open cover of `S` of order `≤ 2`, and its members have diameter `≤ d_0 + 2η < 1`.
- **Contradiction.** No member meets two opposite sides, which are at distance 1. Lebesgue's covering
  theorem then forces a point in 3 members. ∎

**Step 2 (a measure on that component).**
- Let `C ⊆ f^{−1}(c)` be a component with `diam C ≥ 1`. Its coordinate projections `p_1(C)`, `p_2(C)` are
  intervals. Since `diam C² ≤ |p_1(C)|² + |p_2(C)|²`, one of them, say `J = p_i(C)`, has length at least
  `1/√2`.
- The multifunction `x ↦ C ∩ p_i^{−1}(x)` on `J` has nonempty compact values and closed graph, so it
  has a Borel selection `s: J → C` (Kuratowski–Ryll-Nardzewski).
- Let `μ = s_*(Leb_J)`, where `Leb_J` is normalized Lebesgue measure on `J`. Then `μ` is supported
  on `C`, so `f_*μ = δ_c`, and `(p_i)_*μ = Leb_J`.

**Step 3 (the family).** Let `𝓜` be the set of `μ ∈ Prob(S)` such that, for some `i ∈ {1,2}` and some
closed interval `J ⊆ [0,1]` with `|J| ≥ 1/√2`, `(p_i)_*μ = Leb_J`.
- **Closed.** Let `μ_n → μ` with witnesses `(i_n, J_n)`. Pass to a subsequence with `i_n = i` and
  `J_n → J` in the Hausdorff metric, so `|J| ≥ 1/√2`. Then `Leb_{J_n} → Leb_J` weak*, and
  `(p_i)_*μ = Leb_J`.
- **Compact.** It is a closed subset of the compact space `Prob(S)`.
- **Atomless.** An atom of `μ` would give an atom of `(p_i)_*μ = Leb_J`.

By Step 2, every continuous `f` has some `μ ∈ 𝓜` with `f_*μ` a Dirac measure. ∎

## Remarks

- **Contrast with Corollary D.2.** On a zero-dimensional `Y` there is an injective `h ∈ C(Y)`, and
  injectivity alone makes every pushforward of an atomless measure atomless. On `[0,1]` the identity
  works. From dimension 2 on, injective functions do not exist, and Proposition U shows that no choice
  of function survives every compact atomless family.
- **Not claimed.** No C*-algebra with strict comparison whose extreme traces restrict to `𝓜` on a
  diagonal `C(S)` was built. Even if one were, the elements outside the diagonal would still have to
  be rigid for Theorem D to give an indivisible unit.
- **The same shape as the staircase charges.** There Lebesgue's covering theorem forces `D + 1`
  overlapping division sets on a `D`-dimensional face. Here it forces a level-set component of full
  diameter. Both are dimension-theoretic forcing. The Pauli mechanism is cohomological: a top
  Stiefel–Whitney class forces zeros of sections.
