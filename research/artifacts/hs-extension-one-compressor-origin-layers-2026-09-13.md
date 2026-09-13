# One-compressor origin layers: exact-vertex actor models of pure non-unit type

Lane `ex-hs-instability-extension`, 2026-09-13. Unreviewed.

The question of the lane is flexible HS rounding of the polynomial vertex at models that extend to the
Kun--Thom actor `G`. The per-model chain on main shows that under (H1) any rounding at a `G`-model is of
unit type and normalizes the commutant. This artifact builds, for a single compressor, explicit models at
which (H1) holds *exactly* while the rounding is of pure non-unit type and the commutant is not normalized.
So covariance under one compressor forces neither conclusion, and the torus and second attractor used by
the chain are needed.

## 0. Setting

- `q` a prime power, `d >= 2`, `r >= 3`. `R_+ = F_q[x_1..x_d]`, `m_0 = (x_1, ..., x_d)`, `Γ = EL_r(R_+)`.
- `A ∈ SL_d(Z)` with every entry `>= 1`, and `c_A` its largest column sum. `φ = φ_A : R_+ -> R_+`,
  `x^a -> x^(Aa)`, is an injective ring endomorphism that maps distinct monomials to distinct monomials.
  The same letter denotes `EL_r(φ) : Γ -> Γ`.
- `V = <Γ, A> ≤ G = EL_r(F_q[x^(±1)]) ⋊ SL_d(Z)`, with `A γ A^(-1) = φ(γ)` (the convention of
  `unit-type-vertex-rounding-forces-compressor-commutant-rigidity`, where `AΓA^(-1) = EL_r(φ(R_+))`).
- **`V` is the ascending HNN extension `Γ *_φ`.** Every element of the abstract HNN group has a normal form
  `t^(-a) γ t^b` with `a, b >= 0`. Its image `A^(-a) γ A^b` has `SL_d(Z)`-component `A^(b-a)`, which is
  trivial only when `a = b`, since `A` has infinite order. If `a = b`, the image is the substitution of `γ` by
  the automorphism `A^(-a)` of `EL_r(F_q[x^(±1)])`, trivial only when `γ = e`. So the map is injective.
- A *model* is a homomorphism `σ : V -> U(M)`, `M = prod_U M_(n_N)`, given by coordinates `σ_N`. It is
  trace-preserving if `τ∘σ = δ_e`.

## 1. Origin ideals along the compressor

For `k >= 1` put `J_j = φ^(-j)(m_0^k)` for `j >= 0`, `B_0 = R_+/m_0^k`, `Q_0 = EL_r(B_0)`, and let
`p_0 : Γ -> Q_0` be reduction.

1. **`ψ_j = p_0∘φ^j : Γ -> Q_0` is a homomorphism with image `Q'_j = EL_r(S_j)`.** Here `S_j` is the image of
   the subring `φ^j(R_+)` in `B_0`. `S_j` is spanned by the images of the monomials `x^(A^j b)`, `b ∈ N^d`, and
   only those of degree `< k` survive. Since `φ(R_+) ⊆ R_+`, `S_(j+1) ⊆ S_j` and `Q'_(j+1) ≤ Q'_j`.
2. **Origin type.** `ψ_j` kills `Γ(m_0^k)`, because `φ^j(m_0^k) ⊆ m_0^k`, as each `φ(x_i)` has degree `>= 1`.
   So every `ψ_j` factors through `EL_r(R_+/m_0^k)`. That ring is local with maximal ideal `m_0/m_0^k`, and
   every `x_i` is nilpotent in it.
3. **Kernels escape.** Let `γ ≠ e`. Some entry `f` of `γ - 1` has a monomial `x^a` with nonzero coefficient;
   put `e(γ) = |a|`. The polynomial `φ^j(f)` contains `x^(A^j a)` with the same coefficient, since distinct
   monomials have distinct images. Also `|A b| <= c_A |b|` for `b ∈ N^d`, so `|A^j a| <= c_A^j e(γ)`.
   If `c_A^j e(γ) < k`, then `φ^j(f) ∉ m_0^k` and `ψ_j(γ) ≠ 1`.
4. **Strictness.** If `c_A^j < k`, then `g_j := ψ_j(e_12(x_1)) = e_12(x^(A^j e_1))` lies in `Q'_j \ Q'_(j+1)`.
   - `e_12(s) ∈ EL_r(S)` forces `s ∈ S`, because `EL_r(S) ⊆ M_r(S)`.
   - Monomials of degree `< k` are linearly independent in `B_0`. So `x^(A^j e_1)`, of degree `<= c_A^j < k`,
     lies in `S_(j+1)` only if `A^j e_1 = A^(j+1) b` for some `b ∈ N^d`, i.e. `e_1 = A b`.
   - That is impossible: `A b = 0` if `b = 0`, and otherwise every coordinate of `A b` is `>= 1`, while `d >= 2`.

## 2. The layered model

Fix `N >= 1` and put `k = k_N = N·c_A^N`. Let `H_N = ⊕_(j=0)^N ℓ²(Q_0)`, so `n_N = (N+1)|Q_0|`, and let
`λ` be the left regular representation of `Q_0`.

```text
π_N(γ) = ⊕_(j=0)^N  λ(ψ_j(γ)),        (S ξ)_j = ξ_(j+1 mod N+1).                         (OL1)
```

- **Genuine vertex.** `π_N` is a genuine representation of `Γ`.
- **Covariance off one layer.** `(S π_N(γ) S^* ξ)_j = λ(ψ_(j+1)(γ)) ξ_j` for every `j`, and
  `ψ_(j+1) = ψ_j∘φ`. So `S π_N(γ) S^*` and `π_N(φ(γ))` agree on the layers `0..N-1`, and on layer `N` they are
  two unitaries. Hence

  ```text
  || S π_N(γ) S^* - π_N(φ(γ)) ||_2  <=  2/√(N+1)      for every γ ∈ Γ.                    (OL2)
  ```

- **The model.** Fix a normal form `t^(-a) γ t^b` for each `v ∈ V` and set `σ_N(v) = S^(-a) π_N(γ) S^b`.
  - For fixed `v, w`, move the `S`-powers of `σ_N(v)σ_N(w)` past the middle `π_N` factor. This uses (OL2)
    iterated, through unitarily invariant norms, a number of times bounded independently of `N`.
  - That produces `σ_N(vw)` up to one more change of normal form, which (OL2) also controls.
  - So `||σ_N(v)σ_N(w) - σ_N(vw)||_2 <= C(v,w)/√(N+1)`, and `σ = (σ_N)_U` is a homomorphism `V -> U(M)`.
- **Trace.** Let `v = t^(-a) γ t^b ≠ e`.
  - If `a ≠ b` and `N + 1 > |a - b|`, then `σ_N(v)` shifts the layers by a nonzero amount, so its trace is `0`.
  - If `a = b`, then `γ ≠ e` and `σ_N(v)` is block diagonal, with the blocks `λ(ψ_j(γ))` permuted. So
    `tr σ_N(v) = #{j <= N : ψ_j(γ) = 1}/(N+1)`. By §1.3 this is `0` once `N > e(γ)`, because
    `c_A^j e(γ) <= c_A^N e(γ) < N c_A^N`.
  - Hence `τ∘σ = δ_e`, and `σ` is trace-preserving.

## 3. The vertex rounds exactly, and every rounding has pure non-unit type

Take the decomposition `R_+/I_n = A_u × A_nu` and the projection `P_n` of
`unit-type-vertex-rounding-forces-compressor-commutant-rigidity`.

- **This rounding.** `π_N` factors through `EL_r(R_+/m_0^k)` (§1.2). There `A_u = 0`, so `P_n` projects onto
  the trivial constituents. Their trace is `(N+1)^(-1) Σ_j |Q'_j|^(-1) <= |Q'_N|^(-1)`.
  - `Q'_N` contains `e_12(x^(m A^N e_1))` for `0 <= m < N`, since `m c_A^N < k`. Distinct `m` give distinct
    elements, so `|Q'_N| >= N`. Hence `τ(P_n) -> 0`.
- **Lemma (T-uniqueness of roundings).** Let `κ` be a Kazhdan constant for `(Γ, F_Γ)`. Let `π, π'` be
  genuine representations on `C^D` with `max_(s ∈ F_Γ) ||π(s) - π'(s)||_2 <= ε`. Then there are projections
  `Q ∈ π(Γ)'` and `Q' ∈ π'(Γ)'`, with `τ(1-Q) = τ(1-Q') <= ε²/κ²`, and a partial isometry `W` with
  `W^*W = Q`, `WW^* = Q'` and `W π(g) = π'(g) W`.
  - *Proof.* On `(M_D, ||·||_2)` let `ρ(g)X = π'(g) X π(g)^*`. Then `||ρ(s)1 - 1||_2 <= ε`.
  - Write `P` for the projection onto `Fix ρ`. The vector `1 - P1` is orthogonal to `Fix ρ`, and
    `ρ(s)(1 - P1) - (1 - P1) = ρ(s)1 - 1`. So Kazhdan gives `||1 - X_0||_2 <= ε/κ`, where `X_0 = P1`
    intertwines `π` with `π'`.
  - Let `X_0 = W|X_0|` be the polar decomposition. `W` intertwines, and `1 - Q = 1 - W^*W` is the kernel
    projection of `X_0`.
  - On that kernel `1 - X_0` acts as the identity, so `τ(1-Q) <= ||1 - X_0||_2^2`. Traces of `W^*W` and
    `WW^*` agree.
- **Consequence.** Suppose `π'_n` is any (H1) rounding of `σ|Γ`, on `n' = n + o(n)` dimensions. Pad `π_N`
  by the trivial representation, a unit-type summand of trace `o(1)`.
  - The lemma matches the two roundings off trace `o(1)`, isomorphism class by isomorphism class.
  - Whether a constituent has unit type depends only on its isomorphism class.
  - So `τ(P'_n) -> 0` as well: *every* rounding of this vertex has non-unit mass tending to `1`.

## 4. The compressor does not normalize the commutant

Let `R = σ(Γ)' ∩ M`. In `M`, `σ(A) σ(γ) σ(A)^* = σ(φ(γ))`, so

```text
σ(A) R σ(A)^*  =  σ(φ(Γ))' ∩ M  ⊇  R.                                                  (OL3)
```

This inclusion is strict here.
- On layer `j` let `H_j = Q'_(j+1)`. Choose signs `ε^(j)_c`, one for each right coset `c ∈ H_j\Q_0`. Let `z_j`
  be multiplication on `ℓ²(Q_0)` by `f_j(y) = ε^(j)_(H_j y)`, and put `z_N = ⊕_j z_j`, a symmetry.
- **`z_N` commutes exactly with `π_N(φ(Γ))`.** On layer `j`, `π_N(φ(γ)) = λ(ψ_(j+1)(γ)) ∈ λ(H_j)`. Also
  `λ(h)^* z_j λ(h)` is multiplication by `y -> f_j(hy)`, and `H_j h y = H_j y` for `h ∈ H_j`.
- **`z_N` does not commute with `σ(e_12(x_1))`.** With `g_j = ψ_j(e_12(x_1))`,

  ```text
  || [z_N, π_N(e_12(x_1))] ||_2^2  =  2 - 2 (N+1)^(-1) Σ_j avg_(y ∈ Q_0) f_j(g_j y) f_j(y).
  ```

  - `H_j g_j y = H_j y` iff `g_j ∈ H_j`, and that is false by §1.4, because `c_A^j <= c_A^N < k`.
  - So for independent uniform signs each average has expectation `0`. Fix signs with every average `<= 0`.
  - Then the commutator has `||·||_2^2 >= 2` for every `N`.
- **Conclusion.** `z = (z_N)_U ∈ σ(φ(Γ))' ∩ M` but `z ∉ R`, so `σ(A)Rσ(A)^* ≠ R`, and `σ(V)` does not
  normalize `R`. No property (T) is used in this section.

## 5. What this calibrates

1. **Regime (i) is realized.** `theorem-e-vertex-rounds-to-unit-type-representations` lists "pure non-unit mass
   spread over `>= 1/η_n` d-adic depth scales" as the one surviving counterexample shape before the two-attractor
   theorem, and records that no model realized it.
   - Here the transport defect is `δ_N <= 2/√(N+1)`, so `η_N = 4δ_N^2/κ^2 <= 16/(κ^2 (N+1))`.
   - The root spectrum of layer `j` is uniform on the characters of `R_+/J_j`. Their typical `z`-depth is about
     `k/|A^j 1|`, so the `N+1` layers sit at `N+1` distinct scales, spaced by about `log_d` of the Perron
     root of `A`.
   - So the per-scale bound of `nonunit-component-root-mass-is-log-scale-folner` is attained up to constants.
2. **The chain needs more than one compressor.** For one positive compressor, even with exact covariance under
   the whole ascending HNN group, (H1) holds and still gives neither unit type nor normalization. So the torus
   step of `shallow-nonunit-root-mass-vanishes-under-vertex-rounding` and the second attractor of
   `vertex-rounding-deep-nonunit-root-mass-vanishes` are not removable in general.
   - This complements `kt-single-compressor-canonical-lamps-do-not-exactify-actor`. There the canonical
     one-compressor *wreath* microstates stay far from genuine on the actor. Here the vertex is genuine and
     only the commutant grows.
3. **Extension obstruction.** By the established chain, `σ|Γ` is not close to the vertex restriction of any
   trace-preserving `G`-model, since any rounding at such a model has non-unit mass `-> 0`.
   - So these one-compressor models do not extend to `G`, and they cannot be perturbed by `o_2(1)` on `F_Γ` into
     models that do.
   - What extension to `G` buys, beyond one compressor, is exactly the exclusion of these origin layers.
4. **Not settled here.** Can lamps be added, giving a trace-preserving model of
   `W_A = (⊕_(V/Γ) Z/2) ⋊ V` whose vertex is still exact? The lamp at `AΓ` would have to live in the
   commutant excess `π(φ(Γ))' ⊖ π(Γ)'`, where §4 finds room. Its `Γ`-translates would then have to be
   Bernoulli independent. If such a model exists, the one-compressor analogue of
   `kt-wreath-models-never-round-on-the-vertex` fails.
