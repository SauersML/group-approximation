---
rg: 2
id: trace-class-conjugation-cup-products-exact-proof
kind: route
title: An invariant dual pair turns the cup product into the coboundary of the relative trace; the pair (B, S_1) under conjugation is one; the C^3 Hilbert-transform commutator has a C^1 kernel and so is trace class; the Navas-Liouville cocycle has L^1 values
target: trace-class-conjugation-cocycles-have-exact-cup-products
requires: []
artifacts: []
---

Notation is that of the target. The proof is self-contained. It uses only standard facts about
Schatten classes: `S_2 · S_2 ⊆ S_1`, Hölder `|tr(X^*Y)| ≤ ‖X‖_p ‖Y‖_{p'}`, unitary invariance and
cyclicity of the trace on `S_1`, and `S_p ⊆ S_q` for `p ≤ q`. It also uses the pairing lemma (A)
of `cup-products-of-integrably-paired-potential-cocycles-are-exact` (established) in Step 5.

## Step 0. Cup-product classes depend only on cohomology classes

Let `b, b'` be real 1-cocycles into `π`.
- `‖b(gh)‖² = ‖b(g) + π(g)b(h)‖² = ‖b(g)‖² + ‖b(h)‖² + 2⟨b(g), π(g)b(h)⟩`. So
  `b ∪ b = ½ d(‖b‖²)` is exact.
- By bilinearity, `b ∪ b' + b' ∪ b = (b+b') ∪ (b+b') − b ∪ b − b' ∪ b'` is exact. So
  `[b ∪ b'] = −[b' ∪ b]`.
- If `K ∈ H` and `(dK)(g) = π(g)K − K`, then (Step 1 with `E = W = H`, `P = ⟨·,·⟩`) `dK ∪ b` is
  exact. By antisymmetry, `b ∪ dK` is exact too.

So `[b_1 ∪ b_2]` depends only on the classes of `b_1, b_2` in `H¹(G; π)`.

## Step 1. The invariant dual pair, (A)

Let `E, ρ, W, P, f, b_1, b_2` be as in (A). Fix `g, h`. Then `π(g)b_2(h) ∈ W` because `W` is
invariant, and `π(g)b_2(h) = b_2(gh) − b_2(g)` by the cocycle identity. Since `b_1(g) ∈ H` and `P`
equals `⟨·,·⟩` on `H × W`, we have:

`⟨b_1(g), π(g)b_2(h)⟩ = P(ρ(g)f − f, π(g)b_2(h))`
`  = P(ρ(g)f, π(g)b_2(h)) − P(f, b_2(gh) − b_2(g))`
`  = P(f, b_2(h)) − P(f, b_2(gh)) + P(f, b_2(g))`,

using bilinearity and `ρ × π`-invariance. This is `(dN)(g,h)` with `N(k) = P(f, b_2(k))`.

For direct sums, take `E_1 ⊕ E_2`, `W_1 ⊕ W_2` and `P_1 + P_2`: invariance, bilinearity and the
restriction property hold summand by summand.

## Step 2. The Schatten dual pair, (B)

Let `2 ≤ p ≤ ∞`, `S_∞ = B`, `E = S_p ⊇ S_2 = H`, `ρ(g)X = U_g X U_g^*`, `W = S_{p'} ⊆ S_2` and
`P(X, Y) = Re tr(X^* Y)`.
- `P` is defined by Hölder and is bilinear over `R`.
- On `S_2 × S_{p'}` it is the real Hilbert–Schmidt inner product.
- Invariance: `(U X U^*)^*(U Y U^*) = U (X^*Y) U^*` with `X^*Y ∈ S_1`, and the trace is unitarily
  invariant.
- `W` is `π_U`-invariant, and `ρ` extends `π_U`.

So (A) applies to `b_1 = c_F` (potential `F ∈ S_p`) and any `S_{p'}`-valued `b_2`, giving
`N(g) = Re tr(F^* b_2(g))`. By Step 0 this extends to `b_2 ∪ c_F` and to cohomologous cocycles.
The complex area class `Im⟨b(g), π_U(g) b(h)⟩` is handled the same way with `Im tr`.

**The algebra `A_1(U)`.**
- `c_F(g) = (U_g F − F U_g)U_g^* = −[F, U_g] U_g^*`. So `F ∈ A_1(U)` iff every `c_F(g) ∈ S_1`.
- `[FF', U] = F[F', U] + [F, U]F'`, so `A_1(U)` is closed under products.
- `[F^*, U_g] = −[F, U_g^*]^* = [F, U_{g⁻¹}]^*`, so it is closed under adjoints.
- `S_1 ⊆ A_1(U)`, and `A_1(U)` is unital.

For `F, F' ∈ A_1(U)`, the cocycle `c_F` has a bounded potential and `c_{F'}` has `S_1` values, so
`c_F ∪ c_{F'}` is exact (`p = ∞`). Adding `K ∈ S_2` to a potential adds the coboundary `dK`, so by
Step 0 the same holds for potentials in `A_1(U) + S_2`.

## Step 3. The kernel of the conjugated Hilbert transform

Let `k(x,y) = (1/2π) cot((x−y)/2)`. Lengths on `S¹` are circle distances.

1. *Trigonometric polynomials.* For `n ≥ 1`,
   `sin(nt)cos(t/2) = ½[sin((n+½)t) + sin((n−½)t)]`. So
   `cot(t/2) sin(nt) = ½(D_n + D_{n−1})(t) = 1 + 2Σ_{j=1}^{n−1} cos(jt) + cos(nt)`, where
   `D_n(t) = sin((n+½)t)/sin(t/2) = 1 + 2Σ_{j≤n} cos(jt)`. Hence
   `(1/2π)∫ cot(t/2) sin(nt) dt = 1`. Also `cot(t/2)cos(nt)` is odd.
   With `t = x − y`, `lim_{ε→0} ∫_{|x−y|>ε} k(x,y) e^{iny} dy = −i sgn(n) e^{inx}`, which is `ℋe^{in·}`.
2. *`C¹` functions.* For `φ ∈ C¹` put
   `ℋ_0φ(x) = (1/2π)∫_{|t|≤π} cot(t/2)(φ(x−t) − φ(x)) dt`. This is absolutely convergent, and
   `|ℋ_0φ| ≤ C‖φ'‖_∞`.
   - By oddness of `cot`, `ℋ_0φ(x) = lim_ε ∫_{|x−y|>ε} k(x,y)φ(y) dy`.
   - By 1, `ℋ_0 = ℋ` on trigonometric polynomials.
   - The Fejér means `σ_Nφ` satisfy `(σ_Nφ)' = σ_N(φ') → φ'` uniformly. So `ℋ_0σ_Nφ → ℋ_0φ`
     uniformly, while `ℋσ_Nφ → ℋφ` in `L²`. Hence `ℋφ = ℋ_0φ` for `φ ∈ C¹`.
3. *Conjugation.* Let `g ∈ Diff³_+(S¹)`, `m = min g' > 0`, and `φ ∈ C¹`. Then `U_gφ ∈ C¹`, and
   `(U_g^*ψ)(x) = ψ(gx) g'(x)^{1/2}`. Substituting `w = gy` gives
   `(U_g^* ℋ U_g φ)(x) = lim_ε ∫_{A_ε} k_g(x,y) φ(y) dy`, where
   `k_g(x,y) = √(g'(x)g'(y)) k(gx, gy)` and `A_ε = {y : |gx − gy| > ε}`.
4. *The difference.* Put `D = k_g − k`. By Step 4, `D` is continuous on the torus.
   - `∫_{A_ε} k_g φ = ∫_{A_ε} Dφ + ∫_{A_ε} k(x,y)(φ(y) − φ(x)) dy + φ(x)∫_{A_ε} k(x,y) dy`.
   - The first two terms converge to the absolutely convergent integrals, by dominated
     convergence (`|k(x,y)(φ(y)−φ(x))| ≤ C‖φ'‖_∞`).
   - For the third, `S¹ ∖ A_ε = [x − a_ε, x + b_ε]` with `a_ε, b_ε = ε/g'(x) + O(ε²)`, since `g`
     is `C²`. So `|a_ε − b_ε| = O(ε²)`. By oddness,
     `|∫_{A_ε} k(x,y) dy| ≤ |a_ε − b_ε| · sup_{|t| ≥ min(a_ε,b_ε)} |cot(t/2)|/2π = O(ε²) · O(1/ε) → 0`.
   - Hence `(U_g^* ℋ U_g − ℋ)φ(x) = ∫ D(x,y)φ(y) dy` for `φ ∈ C¹`.
   - Both sides are bounded on `L²`: a bounded kernel is Hilbert–Schmidt. `C¹` is dense. So
     `U_g^* ℋ U_g − ℋ` is the integral operator with kernel `D`.

## Step 4. `D` is `C¹` on the torus, so `c_ℋ(g) ∈ S_1`

Fix a lift `g̃` of `g` with `g̃(x+2π) = g̃(x) + 2π` and `g̃' = g'`. On the strip
`Σ = {(x,y) ∈ R² : |x−y| < π}`, which covers the set of pairs at circle distance `< π`:
- `G(x,y) = ∫_0^1 g̃'(y + s(x−y)) ds` is `C²`, symmetric, `≥ m`, and `g̃x − g̃y = (x−y)G`, which lies
  in `(−2π, 2π)`. Also `cot((gx−gy)/2) = cot((g̃x−g̃y)/2)`.
- `a(w) = cot(w/2) − 2/w` extends to an odd real-analytic function on `(−2π, 2π)`.
- Put `S = √(g'(x)g'(y))/G − 1`. It is `C²`, symmetric, and `0` on the diagonal. Then off the
  diagonal
  `2π D = 2S(x,y)/(x−y) + √(g'(x)g'(y)) a((x−y)G) − a(x−y)`.
- Hadamard: `S(x,y)/(x−y) = ∫_0^1 ∂_1S(y + s(x−y), y) ds` is `C¹`, since `∂_1 S ∈ C¹`. The
  `a`-terms are `C²`. So `D` extends `C¹` across the diagonal.
- It vanishes there: `S/(x−y)` is antisymmetric, and the `a`-terms vanish at `x = y`.
- At circle distance `≥ π/2`, both cotangents are `C²`, since `gx ≠ gy`. So `D ∈ C¹(T²)`.

*A `C¹` kernel is trace class.* Let `e_n(y) = e^{iny}/√(2π)` and let `Λ` be the Fourier multiplier
`(1+n²)^{1/2}`. Let `A` be the operator with kernel `D`.
- By Parseval in `y` for each `x`, then integrating in `x`:
  `Σ_n (1+n²)‖A e_n‖² = ‖D‖²_{L²} + ‖∂_y D‖²_{L²} < ∞`.
- So `AΛ`, defined on trigonometric polynomials, extends to a Hilbert–Schmidt operator `B`.
- `Λ⁻¹` is Hilbert–Schmidt, since `Σ(1+n²)⁻¹ < ∞`.
- So `A = BΛ⁻¹ ∈ S_2 · S_2 ⊆ S_1`.

Hence `U_g^* ℋ U_g − ℋ ∈ S_1`, and `c_ℋ(g) = −U_g (U_g^* ℋ U_g − ℋ) U_g^* ∈ S_1` for all `g`.

The Szegő projection `(1 + iℋ)/2 + ½E_0` (with `E_0` the rank-one projection on constants) lies in
`A_1(U)` too. This proves (C)1. (C)2 follows from Step 2.

*Remark.* Under the unitary `S_2(L²(S¹)) ≅ L²(T², dx dy)`, `π_U` is the Koopman representation of
the diagonal action, and `c_ℋ` has the measurable potential `k`. Since `D` vanishes on the diagonal,
`k̄ · D` is bounded, so for `c_ℋ ∪ c_ℋ` the commutative lemma would also apply. For a general
`S_1`-valued partner, the kernel need not be bounded near the diagonal, and `k̄ · b_2(g)` need not
be absolutely integrable. The trace pairing `tr(ℋ^* b_2(g))` is still defined. This is where (B)
goes beyond the Koopman form.

Example: `b_2 = c_{E_0}` has kernel `(1/2π)[√((g⁻¹)'(x)(g⁻¹)'(y)) − 1]`. On the diagonal this equals
`((g⁻¹)'(x) − 1)/2π`, so `k̄ · b_2(g) ~ ((g⁻¹)'(x) − 1)/(2π²(x−y))`. That is not integrable
unless `g' ≡ 1`.

## Step 5. The Navas–Liouville cocycle, (C)3

Let `ρ(x,y) = 1/(4 sin²((x−y)/2))`, so `μ = ρ dx dy`, and let `κ = g⁻¹ ∈ Diff³_+`.
- The density of `g_*μ` at `(x,y)` is `ρ(κx, κy) κ'(x)κ'(y)`. So
  `J(x,y) := d(g_*μ)/dμ = κ'(x)κ'(y) sin²((x−y)/2) / sin²((κx−κy)/2)`, and `ν(g) = √J − 1`.
- `|√J − 1| ≤ |J − 1|` and `(√J − 1)² ≤ |J − 1|`, so it suffices that `J − 1 ∈ L¹(μ)`.
- *Near the diagonal.* Use the strip `Σ` and the divided difference `G_κ` of Step 4 (for `κ`),
  and put `σ(w) = (sin(w/2)/(w/2))²`. This `σ` is even, analytic, and positive on `(−2π, 2π)`.
  - On `Σ`, `J = [κ'(x)κ'(y)/G_κ²] · σ(x−y)/σ((x−y)G_κ)`.
  - This is `C²` (since `G_κ ∈ C²`), symmetric in `(x,y)`, invariant under
    `(x,y) ↦ (x+2π, y+2π)`, and `1` on the diagonal.
  - With `m = (x+y)/2`, `t = x−y`, the function `φ_m(t) = J − 1` is even and `C²` with
    `φ_m(0) = 0`. So `φ_m'(0) = 0` and `|J − 1| ≤ C t²`, with `C` uniform by periodicity.
  - Since `ρ ≤ C'/t²` for `|t| ≤ π`, `|J − 1| ρ` is bounded near the diagonal.
- *Away from it* (circle distance `≥ π/2`), `J` is continuous and `μ` is finite.
- Hence `J − 1 ∈ L¹(μ)`, and `ν(g) ∈ L¹(μ) ∩ L²(μ)` for every `g`.

`ν` has the bounded potential `1`. For any cocycle `b` of the same Koopman model with `L¹(μ)`
values, `1 · b(g) ∈ L¹`. The pairing lemma (A) of
`cup-products-of-integrably-paired-potential-cocycles-are-exact` gives `ν ∪ b = dN` with
`N(g) = ∫ b(g) dμ`. By Step 0, `b ∪ ν` is exact as well. This includes `b = ν` and every
Navas–Liouville cocycle of a `C³` action.

## Step 6. Scope, and what is not claimed

- (C) is stated for an arbitrary homomorphism `T → Diff³_+(S¹)`. Faithfulness and the existence of
  a smooth model are not used. Ghys–Sergiescu is recalled only to say that the statement is not
  vacuous. The same proof works verbatim for any group `G` acting by `C³` diffeomorphisms.
- Not claimed: that every `S_2`-valued conjugation cocycle for the half-density representation lies
  in `A_1(U) + S_2`. That would need pseudodifferential calculus, which is recalled in the target
  as a heuristic only.
- Not claimed: anything about potentials in `S_p ∖ S_2` with partners that are `S_2`-valued but not
  `S_{p'}`-valued, for `2 < p < ∞`. These are exactly the survivors named in the target.
