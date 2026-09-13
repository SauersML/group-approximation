# One-compressor wreath models with an exact origin vertex

Lane `ex-hs-instability-extension`, 2026-09-13. Unreviewed. This continues
`research/artifacts/hs-extension-one-compressor-origin-layers-2026-09-13.md`, cited below as [L]. Its §§0–2
notation is kept: `Γ`, `A`, `φ`, `c_A`, `V = Γ *_φ`, `k = N c_A^N`, `Q_0`, `ψ_j`, `Q'_j = ψ_j(Γ)`, `π_N`, `S`.

Question. `kt-wreath-models-never-round-on-the-vertex` proves that no trace-preserving model of the Kun--Thom
wreath over the full actor `G` rounds on the vertex. Does the same hold for the one-compressor wreath

```text
W_A = (⊕_(V/Γ) Z/2) ⋊ V ?
```

Answer: no. `W_A` has trace-preserving models whose vertex restriction is a genuine representation at every
coordinate.

## 0. Permutation picture

Let `Y = {0..N} × Q_0`, so `H_N = ℓ²(Y)`. The operators of [L] §2 are permutation matrices:

```text
γ ∈ Γ :  (j, g) -> (j, ψ_j(γ) g),              A :  (j, g) -> (j - 1 mod N+1, g).
```

These maps generate an action of the free product `Γ * Z` on `Y`. For a normal form `v = A^(-a) γ A^b`, let
`v̂ ∈ Γ * Z` be the same word. Then `σ_N(v)` is the permutation matrix `P_(v̂)`, where `P_f δ_y = δ_(f(y))`.

The `Γ`-orbits on `Y` are `O(j, g) = {j} × Q'_j g`, the right cosets of `Q'_j` in layer `j`.

## 1. Separability at the origin level

**Lemma 1.** Let `δ ∈ Γ` and `i, b >= 0`, and suppose every entry of `φ^i(δ)` has degree `< k`. If
`ψ_i(δ) ∈ ψ_i(φ^b(Γ))`, then `δ ∈ φ^b(Γ)`.

*Proof.* This is the truncation argument of `monomial-ascending-hnn-coset-action-sofic`, at the ideal `m_0^k`.
- **The image.** Put `S' = φ^(i+b)(R_+)`. It is spanned by monomials, and the ring isomorphism `φ^(i+b)` makes it a
  polynomial ring. `ψ_i(φ^b Γ)` is the reduction of `EL_r(S')`.
- **Lift.** So `φ^i(δ) ≡ s (mod m_0^k)` for some `s ∈ EL_r(S') ⊆ M_r(S')`.
- **Truncate.** Each entry of `φ^i(δ)` has degree `< k`, so it equals the degree-`<k` truncation of the matching
  entry of `s`. That truncation lies in `S'`. Hence `φ^i(δ) ∈ M_r(S')`, with determinant `1`, i.e.
  `φ^i(δ) ∈ SL_r(S')`.
- **Suslin stability.** `SL_r = EL_r` over polynomial rings over a field for `r >= 3`, as used in that node. So
  `φ^i(δ) ∈ EL_r(S') = φ^(i+b)(Γ)`, and injectivity of `φ^i` gives `δ ∈ φ^b(Γ)`. ∎

## 2. Distinct cosets give distinct orbits in the no-wrap window

**Lemma 2.** Let `x_1..x_m ∈ V/Γ` be distinct, with normal-form representatives `v_i = A^(-a_i) γ_i A^(b_i)`
and `a_i, b_i <= R`. There is `D` depending only on these representatives such that the following holds.
If `N > max(R, D)` and `y = (j, g)` with `R <= j <= N - R`, then the orbits `O_i(y) = Γ · v̂_i^(-1) y` are
pairwise distinct.

*Proof.*
- **The orbits.** In the window no layer index wraps, and `v̂_i^(-1) = A^(-b_i) γ_i^(-1) A^(a_i)` gives

  ```text
  v̂_i^(-1)(j, g) = (j - a_i + b_i,  ψ_(j - a_i)(γ_i)^(-1) g).
  ```

- **Normalize.** Suppose `O_i(y) = O_(i')(y)`. The layers agree, so `b_i - a_i = b_(i') - a_(i')`. Put
  `a = max(a_i, a_(i'))` and replace `γ_i` by `φ^(a - a_i)(γ_i)`. This changes neither the coset nor the map,
  because `ψ_(j-a)∘φ^(a-a_i) = ψ_(j-a_i)`. After this `a_i = a_(i') = a` and `b_i = b_(i') = b`.
- **The condition.** Equal right cosets of `Q'_(j-a+b) = ψ_(j-a)(φ^b Γ)` mean `ψ_(j-a)(δ) ∈ ψ_(j-a)(φ^b Γ)`, with
  `δ = γ_i^(-1) γ_(i')`.
- **Degrees.** The entries of `δ` have degree at most some `D`, fixed by the representatives. The entries of
  `φ^(j-a)(δ)` then have degree `<= c_A^N D < N c_A^N = k`.
- **Conclude.** Lemma 1 gives `δ ∈ φ^b(Γ)`, so `γ_i A^b Γ = γ_(i') A^b Γ` and `x_i = x_(i')`, a contradiction. ∎

## 3. Lamps from a random invariant sign

Let `F` be a function from the set of `Γ`-orbits of `Y` to `{±1}`. Put `e_N = M_F`, multiplication by
`y -> F(O(y))`.
- **A root lamp.** `e_N` is a symmetry commuting exactly with `π_N(Γ)`, since `F` is constant on orbits.
- **Its translates.** `σ_N(v) e_N σ_N(v)^* = P_(v̂) M_F P_(v̂)^* = M_(F∘v̂^(-1))`. Every translate is diagonal, so all
  translates commute exactly.
- **The model.** Fix representatives `v_x` for `x ∈ V/Γ`. For `ω` a finite set of cosets and `v ∈ V`, put
  `ρ_N(ω v) = Π_(x ∈ ω) σ_N(v_x) e_N σ_N(v_x)^* · σ_N(v)`.

**Lemma 3.** `ρ = (ρ_N)_U : W_A -> U(prod_U M_(n_N))` is a homomorphism.
- The defining relations of `W_A` are: those of `V`; `e^2 = 1`; `[e, γ] = 1` for `γ ∈ Γ`; and pairwise commutation
  of the translates `v e v^(-1)`.
- The first hold in `M` by [L] §2. The other three hold exactly at every coordinate.
- Representative independence of the lamp at `x` holds in `M`: `σ(vγ) = σ(v)σ(γ)` there, and `σ(γ)` commutes with
  `e`. ∎

**Lemma 4.** Some choice `F = F_N` makes `ρ` trace-preserving: `τ∘ρ = δ_e`.

*Proof.*
- **`v ≠ e`.** For `N` large, `P_(v̂)` has no fixed point on `Y`: it shifts layers, or acts in each layer by the
  nontrivial element `ψ_j(γ)` ([L] §2). `ρ_N(ω v)` is a diagonal matrix times `P_(v̂)`, so its trace is exactly `0`.
- **`ω ≠ ∅`, `v = e`.** Here `tr ρ_N(ω) = avg_(y ∈ Y) X_y`, with `X_y = Π_(i=1)^m F(O_i(y))`. Take `F` uniformly
  random, independent over orbits.
- **Mean.** In the window of Lemma 2 the orbits are distinct, so `E X_y = 0`. The complement of the window has
  density `<= 2R/(N+1)`. So `|E tr ρ_N(ω)| <= 2R/(N+1)`.
- **Variance.** Take `y` in the window. `E[X_y X_(y')] ≠ 0` forces `O_1(y') ∈ {O_1(y), ..., O_m(y)}`. That confines
  `v̂_1^(-1) y'` to `m` orbits of size `<= |Q_0|`, so there are at most `m|Q_0|` such `y'`. Out of `|Y| = (N+1)|Q_0|`,
  this gives

  ```text
  Var(tr ρ_N(ω))  <=  m|Q_0|/|Y| + 4R/(N+1)  <=  (m + 4R)/(N+1).
  ```

- **Choose `F_N`.** Let `𝒞_R` be the finite set of configurations with `m <= R` cosets, representatives
  `a, b <= R`, and `γ`-parts of word length `<= R` in `F_Γ`. Choose `R_N -> ∞` so slowly that
  `|𝒞_(R_N)| · 5R_N/((N+1) ε_N^2) < 1/2` for some `ε_N -> 0`.
  - Chebyshev and a union bound give `F_N` with `|tr ρ_N(ω)| <= ε_N + 2R_N/(N+1)` for every `ω ∈ 𝒞_(R_N)`.
  - Each fixed configuration lies in `𝒞_(R_N)` for large `N`. ∎

## 4. Theorem

**`W_A` has a trace-preserving model `ρ` whose restriction to `Γ` is, at every coordinate, the genuine
representation `π_N` of pure origin type.**

Consequences:
1. **The one-compressor analogue of `kt-wreath-models-never-round-on-the-vertex` is false.** At this wreath model
   (H1) holds with zero defect, and by [L] §3 every rounding has non-unit mass `-> 1`.
2. **The compressor does not normalize.** The root lamp lies in `σ(Γ)' ∩ M`, and the lamp at `AΓ` does not
   commute with `σ(e_12(x_1))`: its trace against its `e_12(x_1)`-conjugate is the product of two distinct lamps,
   which is `0`.
3. **Consistency with the actor no-go.** `kt-single-compressor-canonical-lamps-do-not-exactify-actor` excludes an
   exact actor. Here the actor is the layer shift, far from genuine on the one wrap layer. The rounded lamp at `AΓ`
   lies in `π_N(φΓ)' \ π_N(Γ)'`, the commutant excess that no exact `V`-representation has.
4. **The model is monomial.** Every operator is a signed permutation matrix, so these are sofic-type microstates.
   They are explicit and exact on `Γ`, whereas the general route through `monomial-ascending-hnn-coset-action-sofic`
   and GKP permanence gives no control of the vertex.

## 5. Reading for the actor problem

The no-rounding theorem at `G`-models needs two premises that this model lacks:
- the torus step, `shallow-nonunit-root-mass-vanishes-under-vertex-rounding`;
- the two attractors, `vertex-rounding-deep-nonunit-root-mass-vanishes`.

For one compressor, the layer indices `{0..N}` form a Følner set for the shift, and that is what the construction
spends. For a commuting telescope `Z^m` of positive compressors, the box `{0..N}^m`, together with the multi-iterate
separability of `multi-telescope-coset-action-and-double-proof`, should work the same way. That is not written out
here.

The two-attractor counting is a non-amenability statement for the compressor semigroup acting on origin depth
profiles. So, at the level of this construction, extension to `G` excludes an exact vertex at wreath models only
through non-amenable compressor dynamics. This is a heuristic reading, not a theorem.
