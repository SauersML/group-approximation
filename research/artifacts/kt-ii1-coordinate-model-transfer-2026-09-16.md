# II_1-coordinate models with genuine atomic vertex coordinates transfer to matrix models (2026-09-16)

- **Lane:** `swarm-kt-canonical-hs-normalization-`.
- **Hole worked:** `kt-canonical-hs-normalization-fails`.
- **Node proved here:** `kt-genuine-atomic-vertex-coordinate-models-normalize`, through the route
  `kt-genuine-atomic-vertex-coordinate-models-normalize-proof`.

## Summary

The attempt list of `kt-canonical-hs-normalization-fails` ends with an unchecked conditional under
**Popa's second independence case**:

> The rounding chain of the previous item is established for matrix ultraproducts. Whether its
> per-model claims transfer to II_1-coordinate ultraproducts, where multiplicities are continuous,
> was not checked. If they transfer, this lever is dead for the Theorem E pair.

This artifact settles that conditional. We do not transfer the four per-model claims. We transfer the
**model** instead.

1. **Theorem T (transfer, §2).** Let `G` be countable and residually finite, and `Γ <= G`. Suppose
   `σ : G -> U(prod_ω M_i)` has Connes-embeddable coordinates `M_i` and vertex coordinates that are
   genuine representations with atomic images. Then there is a **trace-preserving** matrix model
   `σ♭ : G -> U(prod_U M_n)`. Its vertex coordinates are genuine representations `Γ -> U(n)`, and
   its commutation stabilizer is contained in that of `σ`.
2. **Theorem N (§3).** At the Theorem E pair, `σ♭` satisfies (H1) with zero error and no padding. The
   established rounding chain therefore normalizes its vertex commutant, and the stabilizer
   inclusion carries normalization back to `σ`.
3. **Haagerup coordinates (§4).** Suppose every `M_i` is amenable, e.g. `M_i = R`, or is
   Connes-embeddable with separable predual and the Haagerup property. Then `ρ_i(Γ)''` is automatically atomic
   (`kazhdan-images-in-haagerup-algebras-are-atomic`). So the lever as recorded, with genuine vertex
   coordinates in `M_n = R`, produces no witness.
4. **Sharpness (§5).** Without atomicity, the statement of Theorem N is equivalent to the negation of
   `kt-canonical-hs-normalization-fails`. Constant coordinates realize every model.

Every step except the four chain premises is standard tracial-ultraproduct bookkeeping. §1 proves each
such step in full.

## §0 Conventions

- A **finite tracial algebra** `(M, τ)` is a von Neumann algebra with a faithful normal tracial state.
  - `||x||_2 = τ(x*x)^(1/2)`.
  - `tr` is the normalized trace on `M_d = M_d(C)`.
- For a countable set `X`, an ultrafilter `V` on `X`, and finite tracial algebras `(B_x, τ_x)`, the
  **tracial ultraproduct** `prod_V B_x` is the quotient of the uniformly bounded families by those
  with `lim_V ||b_x||_2 = 0`, with trace `τ_V((b_x)_V) = lim_V τ_x(b_x)`. It is a finite tracial
  algebra.
- **Connes-embeddable** means that every separable von Neumann subalgebra `N <= M`, with the
  restricted trace, has a trace-preserving embedding into `R^(ω_1)` for some free ultrafilter `ω_1`
  on `N`. Any stronger definition implies this one, and only this one is used.
- **Atomic** means `A = directSum_(l in L) M_(k_l)(C)` with `L` countable and every `k_l` finite. This
  is the form (KHA1) of `kazhdan-images-in-haagerup-algebras-are-atomic`.
- For a homomorphism `σ : G -> U(M)` and `Γ <= G`, put

  ```text
  R_σ = σ(Γ)' ∩ M,      K_σ = {g in G : [σ(g), R_σ] = 0},      N = <<Γ>>_G.
  ```

  `K_σ` depends on the ambient algebra `M`. We always write the ambient.
- **Trace-preserving** for `σ : G -> U(M)` means `τ(σ(g)) = δ_(g,e)`.

**Lemma 0.1 (normalization criterion).** `σ(G)` normalizes `R_σ` if and only if `N <= K_σ`.

*Proof.*
- (=>) Suppose `σ(g) R_σ σ(g)* = R_σ` for all `g`. Then `R_σ = σ(g)* R_σ σ(g)` commutes with
  `σ(g)* σ(Γ) σ(g) = σ(g^(-1) Γ g)`. These conjugates generate `N`, so `R_σ` commutes with
  `σ(N)`.
- (<=) Suppose `R_σ` commutes with `σ(N)`. Then `R_σ <= σ(N)' ∩ M <= σ(Γ)' ∩ M = R_σ`, so
  `R_σ = σ(N)' ∩ M`. Since `N` is normal, `σ(g)(σ(N)' ∩ M)σ(g)* = σ(gNg^(-1))' ∩ M = σ(N)' ∩ M`. ∎

**Lemma 0.2 (stabilizers only shrink under transport of witnesses).** Let `σ : G -> U(M)` and
`σ' : G -> U(M')` be homomorphisms. Let `Φ` be a map from `R_σ` into `M'` such that:
- `Φ(p)` commutes with `σ'(Γ)` for every `p in R_σ`;
- `[Φ(p), σ'(g)] != 0` whenever `[p, σ(g)] != 0`.

Then `K_(σ') <= K_σ`. The same conclusion holds when `Φ` is defined only on a family of witnesses
`{p_g : g notin K_σ}`, one for each `g`, with `[p_g, σ(g)] != 0`.

*Proof.* Take `g notin K_σ`. Then `Φ(p_g)` lies in `R_(σ')` and does not commute with `σ'(g)`, so
`g notin K_(σ')`. ∎

## §1 Standard lemmas on tracial ultraproducts

**Lemma 1.0 (bounded unitary and projection lifts).** Let `Q = prod_V B_x` be a tracial ultraproduct.
1. Every unitary of `Q` has a representative consisting of unitaries.
2. Every projection of `Q` has a representative consisting of projections.
3. Every `b in Q` with `||b|| <= C` has a representative with `sup_x ||b_x|| <= 2C`.

*Proof.*
1. Take any bounded representative `(v_x)` and write the polar decomposition `v_x = w_x |v_x|`, with
   `w_x` unitary (the `B_x` are finite). The inequality `|t - 1| <= |t^2 - 1|` for `t >= 0` gives
   `||v_x - w_x||_2 = || |v_x| - 1 ||_2 <= ||v_x* v_x - 1||_2`, and this tends to `0` along `V`.
2. Take a self-adjoint representative `(h_x)` and put `e_x = χ_([1/2, ∞))(h_x)`. For real `t`,
   `|χ_([1/2,∞))(t) - t| <= 2|t^2 - t|`. So `||e_x - h_x||_2 <= 2||h_x^2 - h_x||_2`, which tends to `0`.
3. Write `b = (C/2)(u_1 + u_1* + i u_2 + i u_2*)`, with `u_j = h_j + i(1 - h_j^2)^(1/2)` for the
   contractions `h_1 = Re(b)/C` and `h_2 = Im(b)/C`, and lift each `u_j` by item 1. ∎

**Lemma 1.1 (iterated ultraproducts).** Let `I` be countable and `ω` an ultrafilter on `I`. For each
`i in I`, let `X_i` be countable and `V_i` a free ultrafilter on `X_i`. Put `X = ⊔_i X_i` and

```text
W = { A ⊆ X : { i : A ∩ X_i in V_i } in ω }.
```

Then:
1. `W` is a free ultrafilter on `X`.
2. `lim_W f = lim_(i -> ω) lim_(V_i) f|X_i` for every bounded `f : X -> C`.
3. For finite tracial algebras `B_x`, the map

   ```text
   J : prod_ω ( prod_(V_i) B_x ) -> prod_W B_x,     J[ ((b_(i,x))_(V_i))_ω ] = [ (b_(i,x))_(x in X) ]_W
   ```

   is a well-defined, unital, trace-preserving `*`-homomorphism, hence injective.

*Proof.*
1. `W` is a filter because `ω` and each `V_i` are.
   - For any `A ⊆ X`, exactly one of `{i : A ∩ X_i in V_i}` and `{i : X_i \ A in V_i}` lies in `ω`,
     since these two sets partition `I`. So `W` is an ultrafilter.
   - A finite `A` meets each `X_i` in a finite, hence `V_i`-null, set. So `{i : A ∩ X_i in V_i}` is
     empty, and `A notin W`.
2. Let `c = lim_ω lim_(V_i) f|X_i` and `ε > 0`.
   - The set `S = {i : |lim_(V_i) f|X_i - c| < ε}` lies in `ω`.
   - For `i in S`, the set `A_i = {x in X_i : |f(x) - c| < 2ε}` lies in `V_i`.
   - Hence `A = ⊔_(i in S) A_i` lies in `W`, and `|f - c| < 2ε` on `A`.
3. By Lemma 1.0(3), elements of `prod_ω prod_(V_i) B_x` have representatives with
   `sup_(i,x) ||b_(i,x)|| < ∞`. The two kinds of representative change are killed:
   - If `(b_(i,x))_x` is `V_i`-null for every `i in S`, with `S in ω`, then item 2 gives
     `lim_W ||b_(i,x)||_2 = 0`.
   - If `(b_i)_i` is `ω`-null, item 2 again gives `lim_W ||b_(i,x)||_2 = lim_ω ||b_i||_2 = 0`.

   So `J` is well defined. It is coordinatewise a unital `*`-homomorphism, and item 2 applied to
   `f(i,x) = τ_x(b_(i,x))` shows it preserves the trace. A trace-preserving `*`-homomorphism between
   finite tracial algebras is `||·||_2`-isometric, hence injective. ∎

**Lemma 1.2 (Connes-embeddable separable algebras embed into a matrix ultraproduct).** Let `(N, τ)` be
separable and Connes-embeddable. Then there are a countable set `X`, a free ultrafilter `V` on `X`,
dimensions `d : X -> N` with `d(x) -> ∞` along `V`, and a unital trace-preserving `*`-homomorphism
`θ : N -> Q = prod_V M_(d(x))`.

*Proof.*
- Write `R = (∪_k M_(2^k))''` with trace-preserving conditional expectations `E_k` onto `M_(2^k)`.
- For `a in R`, `E_k(a) -> a` in `||·||_2`. So `Φ(a) = (E_k(a))_(ω_0)` is a trace-preserving
  `*`-homomorphism `R -> prod_(ω_0) M_(2^k)`, for any free ultrafilter `ω_0` on `N`.
  - Multiplicativity is the estimate
    `||E_k(ab) - E_k(a)E_k(b)||_2 <= ||E_k(ab) - ab||_2 + ||a||·||E_k(b) - b||_2 + ||E_k(a) - a||_2·||b||`.
- `Φ` is `||·||_2`-isometric and contractive, so it induces
  `R^(ω_1) -> prod_(ω_1) prod_(ω_0) M_(2^k)`.
- Lemma 1.1 maps this into `prod_V M_(2^k)` over `X = N × N`, with `V` the iterated ultrafilter and
  `d(j,k) = 2^k`. Here `d -> ∞` along `V`, because `{(j,k) : k > k_0}` lies in `V` for every `k_0`.
- Compose with a trace-preserving embedding `N -> R^(ω_1)`. ∎

**Lemma 1.3 (atomic embeddings are unitarily conjugate).** Let `Q = prod_V M_(d(x))` be any matrix
ultraproduct. Let `A = directSum_(l in L) M_(k_l)` be atomic, with faithful tracial state `τ_A`, and let
`α, β : A -> Q` be unital trace-preserving `*`-homomorphisms. Then `Ad(u) ∘ α = β` for some
`u in U(Q)`.

*Proof.*
1. **Equal-trace projections are equivalent in `Q`.** Let `p, q in Q` be projections with
   `τ(p) = τ(q)`.
   - Lift them to projections `p_x`, `q_x` of ranks `r_x`, `s_x` (Lemma 1.0(2)).
   - Choose partial isometries `v_x` with `v_x* v_x <= p_x`, `v_x v_x* <= q_x` and rank
     `min(r_x, s_x)`, and put `v = (v_x)_V`.
   - `v` is a partial isometry with `v*v <= p` and `vv* <= q`, since these inequalities hold
     coordinatewise.
   - `p - v*v` is a projection with trace
     `lim_V max(0, r_x - s_x)/d(x) = max(0, lim_V (r_x - s_x)/d(x)) = max(0, τ(p) - τ(q)) = 0`.
     The trace is faithful, so `v*v = p`. Symmetrically `vv* = q`.
2. **The intertwining unitary.** Let `e^l_(ab)` be matrix units of `M_(k_l)`.
   - `τ(α(e^l_11)) = τ_A(e^l_11) = τ(β(e^l_11))`, so step 1 gives `v_l` with
     `v_l* v_l = α(e^l_11)` and `v_l v_l* = β(e^l_11)`.
   - Put `u = Σ_(l, a) β(e^l_(a1)) v_l α(e^l_(1a))`.
   - The summands are partial isometries with initial projections `α(e^l_(aa))` and final projections
     `β(e^l_(aa))`. Each family is pairwise orthogonal.
   - `α` and `β` are trace-preserving, hence normal, so `Σ α(e^l_(aa)) = 1 = Σ β(e^l_(aa))`
     strongly. The sum therefore converges strongly to a unitary.
3. **It intertwines.** Only the `(l, a)` summand survives in
   `u α(e^l_(ab)) = β(e^l_(a1)) v_l α(e^l_(1b))`, and only the `(l, b)` summand in
   `β(e^l_(ab)) u = β(e^l_(a1)) v_l α(e^l_(1b))`.
   - So `u α(y) u* = β(y)` on the span of the matrix units.
   - That span is `||·||_2`-dense in `A`, and both sides are `||·||_2`-continuous. ∎

**Lemma 1.4 (genuine realization of an atomic representation).** Let `Γ` be a group, let
`(A, τ_A)` be atomic with faithful normal tracial state, `A = directSum_(l in L) M_(k_l)`, and let
`π : Γ -> U(A)` be a homomorphism. Let `Q = prod_V M_(d(x))` be a matrix ultraproduct with
`d(x) -> ∞` along `V`. Then there are a unital trace-preserving `*`-homomorphism `ι : A -> Q` and
**genuine** representations `π_x : Γ -> U(d(x))` such that

```text
ι(π(γ)) = [ (π_x(γ))_x ]_V      for every γ in Γ.
```

*Proof.*
1. **Weights.** Identify `L` with `{1, 2, ...}` (finite or not). Write `Tr` for the unnormalized trace
   on `M_(k_l)`.
   - The restriction of `τ_A` to the summand `M_(k_l)` is `w_l Tr`, with `w_l = τ_A(e^l_11) > 0` by
     faithfulness.
   - By normality `τ_A(a) = Σ_l w_l Tr(a_l)` for `a = (a_l)_l`, and in particular `Σ_l k_l w_l = 1`.
2. **Coordinates.** For `x in X` put:
   - `L(x)`, the largest `L' <= |L|` with `Σ_(l <= L') k_l <= d(x)^(1/2)`;
   - `m_(l,x) = floor(w_l d(x))` for `l <= L(x)`;
   - `r_x = d(x) - Σ_(l <= L(x)) k_l m_(l,x)`.

   Then `r_x >= 0`, because `Σ_l k_l w_l <= 1`. Also, since `m_(l,x) >= w_l d(x) - 1`,

   ```text
   r_x <= d(x) Σ_(l > L(x)) k_l w_l + Σ_(l <= L(x)) k_l <= d(x)·ε_x,
   ε_x = d(x)^(-1/2) + Σ_(l > L(x)) k_l w_l.
   ```

3. **`ε_x -> 0` along `V`.** Fix a finite `L_0 <= |L|`. Since `d(x) -> ∞` along `V`, eventually
   `Σ_(l <= L_0) k_l <= d(x)^(1/2)`, so `L(x) >= L_0` and `ε_x <= d(x)^(-1/2) + Σ_(l > L_0) k_l w_l`.
   The tail tends to `0` as `L_0 -> |L|`.
4. **The maps.** Put

   ```text
   ι_x(a) = ( directSum_(l <= L(x)) a_l (tensor) 1_(m_(l,x)) ) (+) 0_(r_x)      in M_(d(x)),
   π_x(γ) = ι_x(π(γ)) + (1 - ι_x(1)).
   ```

   - `ι_x` is a non-unital `*`-homomorphism with `||ι_x(a)|| <= ||a||`.
   - `1 - ι_x(1)` is a projection of rank `r_x`, orthogonal to the range of `ι_x`. So `π_x` is a
     genuine unitary representation of `Γ`.
5. **Trace estimate.** For `a in A`,

   ```text
   |tr ι_x(a) - τ_A(a)| = | Σ_(l <= L(x)) (m_(l,x)/d(x) - w_l) Tr(a_l) - Σ_(l > L(x)) w_l Tr(a_l) |
                        <= ||a|| ( Σ_(l <= L(x)) k_l / d(x) + Σ_(l > L(x)) k_l w_l ) <= ||a||·ε_x.
   ```

6. **Conclusion.** `ι(a) = [(ι_x(a))_x]_V` is a `*`-homomorphism `A -> Q`.
   - It preserves the trace by step 5 and step 3.
   - It is unital, because `||1 - ι_x(1)||_2^2 = r_x/d(x) <= ε_x -> 0`.
   - `||π_x(γ) - ι_x(π(γ))||_2 = ||1 - ι_x(1)||_2 -> 0`, so `ι(π(γ)) = [(π_x(γ))_x]_V`. ∎

Continuous multiplicities cause no difficulty: the real weights `w_l` are absorbed by the integer
parts `floor(w_l d(x))`, and the errors vanish along the ultrafilter.

**Lemma 1.5 (trace correction by finite quotients).** Let `G` be countable and residually finite, and
`Γ <= G`. Let `Y` be countable, `W` a free ultrafilter on `Y`, and `σ̃ : G -> U(Q)`, with
`Q = prod_W M_(D(y))`, a homomorphism with **genuine vertex coordinates**: there are genuine
representations `π_y : Γ -> U(D(y))` with `σ̃(γ) = [(π_y(γ))_y]_W` for all `γ in Γ`. Then there are
a countable set `Z`, a free ultrafilter `V` on `Z`, dimensions `D' : Z -> N`, and a homomorphism
`σ♯ : G -> U(prod_V M_(D'(z)))` such that:
1. `τ(σ♯(g)) = δ_(g,e)`;
2. `σ♯` has genuine vertex coordinates;
3. `K_(σ♯) <= K_(σ̃)`.

*Proof.*
1. **A trace-preserving finite model.**
   - Enumerate `G \ {e} = {g_1, g_2, ...}`. Choose finite-index normal subgroups `H_j` with
     `g_j notin H_j`, and put `G_j = H_1 ∩ ... ∩ H_j`. Then `G_j` has finite index, and
     `g notin G_j` for all large `j`, for every `g != e`.
   - Let `λ_j : G -> U(c_j)`, with `c_j = [G : G_j]`, be the regular representation of `G/G_j`
     composed with the quotient map. Then `tr λ_j(g) = 1` if `g in G_j`, and `0` otherwise.
   - Fix a free ultrafilter `ω'` on `N` and put `ψ(g) = [(λ_j(g))_j]_(ω')` in
     `P = prod_(ω') M_(c_j)`. Then `τ_P(ψ(g)) = lim_(ω') 1[g in G_j] = δ_(g,e)`.
2. **The tensor map.** Let `Z = Y × N`, and let `V` be the iterated ultrafilter of Lemma 1.1, with
   `I = Y`, the ultrafilter `W` on `I`, `X_y = {y} × N` and `V_y` the copy of `ω'`. Put
   `D'(y, j) = D(y) c_j`. Define, on bounded representatives (Lemma 1.0(3)),

   ```text
   T(a (tensor) b) = [ (a_y (tensor) b_j)_((y,j)) ]_V,       a = [(a_y)]_W in Q,  b = [(b_j)]_(ω') in P.
   ```

   - **Well defined.** `||a_y (tensor) b_j||_2 = ||a_y||_2 ||b_j||_2`. If `(a_y)` is `W`-null and
     `sup_j ||b_j|| <= C`, Lemma 1.1(2) gives `lim_V ||a_y (tensor) b_j||_2 <= C lim_W ||a_y||_2 = 0`.
     The case of an `ω'`-null `(b_j)` is symmetric.
   - `T` is bilinear, so it extends linearly to the algebraic tensor product `Q ⊙ P`. There it is
     a `*`-homomorphism, coordinatewise.
   - Lemma 1.1(2) gives `τ(T(a (tensor) b)) = lim_W lim_(ω') tr(a_y) tr(b_j) = τ_Q(a) τ_P(b)`.
3. **The model.** Put `σ♯(g) = T(σ̃(g) (tensor) ψ(g))`.
   - It is a homomorphism into the unitaries, since `T` is multiplicative and both factors are
     homomorphisms.
   - `τ(σ♯(g)) = τ_Q(σ̃(g)) δ_(g,e) = δ_(g,e)`.
   - `σ♯(γ) = [(π_y(γ) (tensor) λ_j(γ))_((y,j))]_V`, and the coordinates are genuine
     representations of `Γ`.
4. **Stabilizer.** Take `g notin K_(σ̃)` and `p in R_(σ̃)` with `c = [p, σ̃(g)] != 0`.
   - `T(p (tensor) 1)` commutes with `σ♯(γ) = T(σ̃(γ) (tensor) ψ(γ))`, because `p` commutes with
     `σ̃(γ)`.
   - `[T(p (tensor) 1), σ♯(g)] = T(c (tensor) ψ(g))`. Its squared 2-norm is
     `τ(T(c*c (tensor) ψ(g)*ψ(g))) = τ_Q(c*c) > 0`.
   - Lemma 0.2 gives `K_(σ♯) <= K_(σ̃)`. ∎

**Lemma 1.6 (re-indexing by dimension).** Let `Z` be countable, `V` a free ultrafilter on `Z`,
`D : Z -> N`, and `σ♯ : G -> U(prod_V M_(D(z)))` a homomorphism with genuine vertex coordinates
`π_z : Γ -> U(D(z))`. Then there are a free ultrafilter `U` on `N` and a homomorphism
`σ♭ : G -> U(prod_U M_n)` such that:
1. `τ ∘ σ♭ = τ ∘ σ♯`;
2. for **every** `n` there is a genuine representation `π'_n : Γ -> U(n)` with
   `σ♭(γ) = [(π'_n(γ))_n]_U`;
3. `K_(σ♭) <= K_(σ♯)`.

*Proof.*
1. **An injective dimension function.** `Z` is infinite, since it carries a free ultrafilter.
   Enumerate `Z = {z_1, z_2, ...}`.
   - Put `c(z_1) = 1` and `c(z_j) = floor(E(z_(j-1))/D(z_j)) + 1` for `j >= 2`, where
     `E(z) = D(z) c(z)`.
   - Then `E(z_j) > E(z_(j-1))`, so `E : Z -> N` is injective.
2. **Amplification.** `a -> a (tensor) 1_(c(z))` is a unital trace-preserving `*`-homomorphism
   `M_(D(z)) -> M_(E(z))`, isometric in both norms. Coordinatewise it induces a unital
   trace-preserving `*`-homomorphism `β : prod_V M_(D(z)) -> prod_V M_(E(z))`.
3. **Transport of the ultrafilter.** Put `U = E_* V = {B ⊆ N : E^(-1)(B) in V}`.
   - `U` is an ultrafilter, because `E^(-1)` preserves complements and intersections.
   - `U` is free, because `E^(-1)({n})` has at most one point.
   - `E(Z) in U`, and `lim_U f = lim_V (f ∘ E)` for every bounded `f : N -> C`.
4. **The isomorphism.** Define `κ : prod_V M_(E(z)) -> prod_U M_n` by
   `κ[(a_z)_z]_V = [(b_n)_n]_U`, with `b_(E(z)) = a_z` and `b_n = 1_n` for `n notin E(Z)`.
   - It is well defined, trace-preserving and injective, by the limit identity of step 3.
   - It is a unital `*`-homomorphism: `κ(ab)` and `κ(a)κ(b)` differ only at coordinates outside
     `E(Z)`, a `U`-null set.
5. **Conclusion.** Put `σ♭ = κ ∘ β ∘ σ♯`.
   - Item 1 holds because `κ ∘ β` preserves the trace.
   - For item 2, take `π'_(E(z)) = π_z (tensor) 1_(c(z))` and let `π'_n` be the trivial
     representation on `C^n` for `n notin E(Z)`.
   - For item 3, `κ ∘ β` is an injective unital `*`-homomorphism. It maps each witness
     `p in R_(σ♯)` to an element of `R_(σ♭)`, and `κβ([p, σ♯(g)]) != 0`. Lemma 0.2 applies. ∎

## §2 Theorem T

**Theorem T (transfer).** Let:
- `G` be a countable residually finite group and `Γ <= G` a subgroup;
- `ω` be an ultrafilter on `N`, free or not;
- `(M_i, τ_i)`, `i in N`, be Connes-embeddable finite tracial algebras, and `M = prod_ω M_i`;
- `σ : G -> U(M)` be a homomorphism, with **no condition** on `τ ∘ σ`.

Assume that there are homomorphisms `ρ_i : Γ -> U(M_i)` such that

```text
ρ_i(Γ)''  is atomic for every i,          σ(γ) = [ (ρ_i(γ))_i ]_ω  for every γ in Γ.        (GA)
```

Then there are a free ultrafilter `U` on `N` and a homomorphism `σ♭ : G -> U(prod_U M_n)` with:
- **(T1)** `τ(σ♭(g)) = δ_(g,e)` for all `g`;
- **(T2)** for every `n`, a genuine representation `π_n : Γ -> U(n)` with
  `σ♭(γ) = [(π_n(γ))_n]_U` for all `γ in Γ`;
- **(T3)** `K_(σ♭) <= K_σ`, the stabilizers being computed in `prod_U M_n` and in `M`.

*Proof.*

**Step 1 (separable coordinates carrying the witnesses).**
- For each `g notin K_σ`, fix `p_g in R_σ` with `[p_g, σ(g)] != 0`. There are countably many.
- Lift each `p_g` to a bounded family `(p_(g,i))_i` (Lemma 1.0(3)).
- For `g in G`, lift `σ(g)` to unitaries `σ_i(g) in M_i` (Lemma 1.0(1)). For `γ in Γ` take
  `σ_i(γ) = ρ_i(γ)`, which is allowed by (GA). The maps `σ_i` need not be homomorphisms.
- Let `N_i` be the von Neumann algebra generated by `σ_i(G)` and `{p_(g,i) : g notin K_σ}`.
  - `N_i` is countably generated, so it has separable predual, and with `τ_i|N_i` it is
    Connes-embeddable.
  - `N_i` contains `ρ_i(Γ)`, hence `A_i = ρ_i(Γ)''`.
- Coordinatewise inclusion identifies `M' = prod_ω N_i` with a von Neumann subalgebra of `M`, with the
  same trace. `σ(G)` and every `p_g` lie in `M'`. Write `σ'` for `σ` viewed in `M'`.
- For `g notin K_σ`, the witness `p_g` lies in `R_(σ') = σ(Γ)' ∩ M'` and does not commute with
  `σ(g)`. So `K_(σ') <= K_σ`.

**Step 2 (matrix coordinates, conjugated to be genuine on the vertex).** Fix `i`.
- Lemma 1.2 gives a unital trace-preserving `θ_i : N_i -> Q_i = prod_(V_i) M_(d_i(x))`, over a
  countable `X_i` with `d_i -> ∞` along the free ultrafilter `V_i`.
- Lemma 1.4, applied to `π = ρ_i : Γ -> U(A_i)`, gives a unital trace-preserving `ι_i : A_i -> Q_i`
  and genuine representations `π_(i,x) : Γ -> U(d_i(x))` with
  `ι_i(ρ_i(γ)) = [(π_(i,x)(γ))_x]_(V_i)`.
- `θ_i|A_i` and `ι_i` are unital trace-preserving `*`-homomorphisms of the atomic algebra `A_i` into
  `Q_i`. Lemma 1.3 gives `u_i in U(Q_i)` with `Ad(u_i) ∘ θ_i|A_i = ι_i`.
- Put `θ'_i = Ad(u_i) ∘ θ_i`. It is unital and trace-preserving, and

  ```text
  θ'_i(ρ_i(γ)) = [ (π_(i,x)(γ))_x ]_(V_i)       for every γ in Γ.
  ```

**Step 3 (one matrix ultraproduct).**
- `prod_ω θ'_i : M' -> prod_ω Q_i`, `[(b_i)]_ω -> [(θ'_i(b_i))]_ω`, is well defined. Each `θ'_i` is
  contractive and `||·||_2`-isometric, so bounded families stay bounded and `ω`-null families stay
  `ω`-null. It is a unital trace-preserving `*`-homomorphism.
- Lemma 1.1, with `I = N`, the ultrafilter `ω`, and the `(X_i, V_i)`, gives the free ultrafilter `W`
  on `Y = ⊔_i X_i` and `J : prod_ω Q_i -> Q = prod_W M_(d(y))`, with `d = d_i` on `X_i`.
- Put `Θ = J ∘ prod_ω θ'_i : M' -> Q` and `σ̃ = Θ ∘ σ'`.
  - `Θ` is a unital trace-preserving, hence injective, `*`-homomorphism, so `σ̃` is a homomorphism.
  - For `γ in Γ`: `σ̃(γ) = J[([(π_(i,x)(γ))_x]_(V_i))_ω] = [(π_(i,x)(γ))_(x in Y)]_W`. So `σ̃`
    has genuine vertex coordinates.
  - For `g notin K_(σ')`, `Θ(p_g)` commutes with `σ̃(Γ)`, and `[Θ(p_g), σ̃(g)] = Θ([p_g, σ(g)]) != 0`.
    Lemma 0.2 gives `K_(σ̃) <= K_(σ') <= K_σ`.

**Step 4 (trace and indexing).**
- `G` is countable and residually finite. Lemma 1.5 turns `σ̃` into a trace-preserving `σ♯` with
  genuine vertex coordinates and `K_(σ♯) <= K_(σ̃)`.
- Lemma 1.6 turns `σ♯` into `σ♭` on `prod_U M_n`, with (T1), (T2) and `K_(σ♭) <= K_(σ♯)`.
- Chaining the inclusions gives (T3). ∎

**Remarks.**
- (GA) may be checked on a generating set of `Γ`. If `σ(s) = [(ρ_i(s))_i]_ω` for every `s` in a
  generating set, it holds on words, because the `ρ_i` are homomorphisms and the coordinatewise map
  is a `*`-homomorphism.
- Connes-embeddability of the `M_i` is used only in Step 2, through Lemma 1.2.
- When `σ` is already trace-preserving, Lemma 1.5 is not needed. Residual finiteness of `G` is used
  only there.

## §3 Theorem N at the Theorem E pair

Fix the explicit Theorem E pair: `R_+ = F_q[x_1..x_d]`, `L = F_q[x_1^(±1)..x_d^(±1)] = F_q[Z^d]`,
`r, d >= 3`, and

```text
Γ = EL_r(R_+)  <  G = EL_r(L) ⋊ SL_d(Z),
```

where `SL_d(Z)` acts by the monomial substitutions `x^a -> x^(Aa)`. Put `N = <<Γ>>_G`.

**Lemma 3.1.** `G` is countable and residually finite.

*Proof.* Countability is clear. For `m >= 2` let `φ_m : F_q[Z^d] -> F_q[(Z/m)^d]` be reduction of
exponents.
- `φ_m(A·f) = (A mod m)·φ_m(f)`, so `Ψ_m(e, A) = (φ_m(e), A mod m)` is a homomorphism
  `G -> EL_r(F_q[(Z/m)^d]) ⋊ SL_d(Z/m)`, a finite group.
- Suppose `(e, A)` lies in every `ker Ψ_m`. Then `A ≡ I mod m` for all `m`, so `A = I`.
- Let `f` be an entry of `e - I`. Once `m` exceeds the diameter of the support of `f` in every
  coordinate, `φ_m` is injective on that support, so `φ_m(f) = 0` forces `f = 0`. Hence `e = I`. ∎

**Theorem N.** Let `Γ < G` be the explicit Theorem E pair, and let `ω`, `(M_i)`, `M = prod_ω M_i`,
`σ : G -> U(M)` and `ρ_i` be as in Theorem T, satisfying (GA). There is no trace condition on `σ`.
Then

```text
σ(G) normalizes σ(Γ)' ∩ M,      equivalently  N <= K_σ.
```

*Proof.*
1. By Lemma 3.1, Theorem T applies. It gives `σ♭ : G -> U(prod_U M_n)` with (T1), (T2) and (T3).
2. **(H1) at `σ♭`, in its strongest form.** Choose coordinates `σ_n : G -> U(n)` of `σ♭`, i.e.
   unitary representatives, with `σ_n(γ) = π_n(γ)` for `γ in Γ`. This is allowed by (T2).
   - For every finite `F_Γ ⊆ Γ`, `max_(s in F_Γ) ||σ_n(s) - π_n(s)||_2 = 0` for all `n`.
   - There is no padding: `n' = n`.
   - Any other choice of representatives changes the defect by a `U`-null sequence. So (H1) holds
     for every choice.
3. **The established chain.** `σ♭` is a trace-preserving homomorphism `G -> U(prod_U M_n)` over a
   free ultrafilter on `N`, satisfying (H1) with rounding representations `π_n`. These are exactly
   the hypotheses of the four established per-model claims used below, and of their input
   `compressor-transport-exactifies-under-vertex-rounding`.
   - `unit-type-vertex-rounding-forces-compressor-commutant-rigidity`, item 1: `π_n` factors
     through `St_r(R_+/I_n)`, with `R_+/I_n = A_u × A_nu`. This defines `P_n`.
   - `nonunit-projection-bounded-by-root-spectral-mass`:
     `τ(1 - P_n) <= r(r-1)·μ_n({χ : χ|A_nu != 1})`.
     - As recorded in the payoff of `vertex-rounding-deep-nonunit-root-mass-vanishes`, the right
       side equals `r(r-1)·[μ_n(depth_nu = 1) + μ_n(depth_nu > 1)]`.
   - `shallow-nonunit-root-mass-vanishes-under-vertex-rounding`, item 5:
     `μ_n(depth_nu = 1) <= q η_n + η_n^t`, which tends to `0` along `U`.
   - `vertex-rounding-deep-nonunit-root-mass-vanishes`: `μ_n(depth_nu > 1) -> 0` along `U`.
   - Hence `τ(1 - P_n) -> 0` along `U`. Item 4 of the rigidity claim then gives that `σ♭(G)`
     normalizes `σ♭(Γ)' ∩ prod_U M_n`.
4. **Back to `σ`.** Lemma 0.1 at `σ♭` gives `N <= K_(σ♭)`. By (T3), `N <= K_σ`. Lemma 0.1 at `σ`
   gives the conclusion. ∎

**What is black-boxed.** Only step 3.
- It is the assembly already recorded in the attempt "Genuine vertex coordinates" of
  `kt-canonical-hs-normalization-fails`, and in the route
  `theorem-e-vertex-unit-type-via-deep-root-mass`.
- That route's only premise not established is (H1) itself (`hs-stable-vertex-rounding-for-every-model`), which Theorem T
  verifies at `σ♭` with zero error.
- No per-model claim is re-proved for II_1 coordinates. The model is moved into their setting instead.

## §4 Haagerup and amenable coordinates

**Corollary H.** Theorem N holds with "atomic" in (GA) replaced by "`ρ_i(Γ)''` has the Haagerup
property". In particular it holds whenever each `M_i` is:
- amenable, e.g. `M_i = R` or `M_i` finite-dimensional (such `M_i` are Connes-embeddable); or
- Connes-embeddable, with separable predual and the Haagerup property, e.g. a free group factor.

*Proof.* `Γ = EL_r(F_q[x_1..x_d])`, `r >= 3`, has property (T). This is the Kazhdan vertex of the
repository. The attribution to Ershov--Jaikin-Zapirain (Invent. Math. 179, 2010) was not re-fetched
here.
- If `ρ_i(Γ)''` has the Haagerup property, `kazhdan-images-in-haagerup-algebras-are-atomic` makes it
  atomic, so (GA) holds and Theorem N applies.
- For both listed coordinate types, `ρ_i(Γ)''` has the Haagerup property, as recorded in that claim.
  An amenable `M_i` is Connes-embeddable: a separable von Neumann subalgebra is the range of a
  trace-preserving conditional expectation, hence injective, hence hyperfinite. ∎

Connes-embeddability stays a hypothesis in the second case, because the Haagerup property alone is
not known to imply it.

For images of a Kazhdan group, the following are equivalent: atomic; amenable; Haagerup. Atomic
implies amenable, amenable implies Haagerup, and Haagerup implies atomic by
`kazhdan-images-in-haagerup-algebras-are-atomic`. So (GA) says exactly that the vertex coordinates are
genuine with amenable images.

**Consequence for Popa's second independence case.** The lever recorded in the target uses
`M_n = R` and genuine vertex coordinates. Every model of that shape satisfies the hypotheses of
Corollary H, so it normalizes `R_σ` and is not a witness, whatever relative freeness it carries. This
settles the conditional "If they transfer, this lever is dead for the Theorem E pair", in the
positive. The mechanism is transfer of the model, not of the per-model claims.

## §5 Sharpness, scope and consistency

1. **Atomicity cannot be dropped without deciding the target.** Let `M_0` be Connes-embeddable and
   `σ_0 : G -> U(M_0)` any homomorphism.
   - Put `M_i = M_0`, `ρ_i = σ_0|Γ` (genuine), `ω` free, and `σ = Δ ∘ σ_0 : G -> U(M_0^ω)`, with `Δ`
     the diagonal embedding. Then (GA) holds except for atomicity.
   - `Δ` is an injective unital `*`-homomorphism, so Lemma 0.2 gives `K_σ <= K_(σ_0)`.
   - So if Theorem N held with atomicity removed, every `σ_0` would have `N <= K_(σ_0)`, and by
     Lemma 0.1 `kt-canonical-hs-normalization-fails` would be false.
   - Conversely, the negation of the target implies the strengthened statement, because
     `prod_ω M_i` is Connes-embeddable. A separable `B <= prod_ω M_i` lies in `prod_ω N_i` for
     separable `N_i <= M_i`, generated by lifts of a countable generating set of `B`.
     - Steps 2–3 of Theorem T, without the conjugation, embed `prod_ω N_i` into a matrix ultraproduct
       `prod_W M_(d(y))` over a countable `Y`.
     - Unital trace-preserving inclusions `M_(d(y)) <= R` embed that into `R^W`.
     - A bijection `Y ≅ N` identifies `R^W` with `R^(ω_1)` for a free ultrafilter `ω_1` on `N`.
2. **What is new relative to the graph.**
   - For principal `ω`, (GA) says that `σ(Γ)''` is atomic in `M`. That case is contained in
     `haagerup-targets-carry-no-relative-wall`, which is a consistency check.
   - For free `ω`, `prod_ω A_i` can be diffuse and non-Haagerup, e.g. `A_i = M_(k_i)` with
     `k_i -> ∞`. So `σ(Γ)''` need not be Haagerup, and that claim does not apply.
   - The `M_i` are arbitrary Connes-embeddable II_1 algebras, and `σ` is a homomorphism only in the
     ultraproduct. So `ccr-holds-for-all-genuine-fd-coordinate-models`,
     `kazhdan-cover-actor-models-normalize-vertex-commutants` and
     `steinberg-actor-models-carry-no-rigid-wall`, which need genuine finite-dimensional
     representations of all of `G` (or of a cover), do not apply either.
   - There is no trace condition. The reduction to trace-preserving models is Lemma 1.5, a
     self-contained ultraproduct version of the tensoring trick of
     `kt-regular-mask-removes-trace-faithfulness-from-commutant-wall`. The target's attempt cites
     that node under a slightly longer id. Lemma 1.5 tensors with regular representations of finite
     quotients, and also checks that genuine vertex coordinates stay genuine. Nothing here depends on
     that node.
3. **Not covered.**
   - **Approximate vertex coordinates.** Suppose the `ρ_i` are only asymptotic homomorphisms with
     atomic `W*(ρ_i(Γ))`. The conjugation of Step 2 still applies. But the coordinates
     `ι_x(ρ_i(γ)) + (1 - ι_x(1))` it produces are only asymptotically multiplicative. (H1) for them
     is flexible Hilbert--Schmidt stability of `Γ` at `G`-extendable models, i.e.
     `hs-stable-vertex-rounding-for-every-model`, which is open.
   - **Genuine vertex coordinates with non-amenable images.** For instance `M_i = L(Γ) (tensor) R`
     with `ρ_i = λ_Γ (tensor) 1`. Such coordinates can satisfy Popa's non-intertwining hypothesis.
     By item 1 this class is as hard as the target itself.
4. **Where the remaining lever sits.** Let `σ : G -> U(prod_ω M_i)` be a witness of
   `kt-canonical-hs-normalization-fails`, with Connes-embeddable `M_i`. By Theorem N it has one of
   two properties.
   - **(a)** No family of genuine representations `ρ_i : Γ -> U(M_i)` represents `σ|Γ`.
     - Coordinates on an `ω`-null set of indices can be replaced by `C`, so "along `ω`" suffices
       here.
     - The recorded matrix-coordinate obstruction concerns this case. It transfers only in a weaker
       form, because Lemmas 1.2, 1.5 and 1.6 without (GA) still give a trace-preserving
       matrix-ultraproduct witness, and the chain shows that witness fails (H1).
   - **(b)** Such families exist, and every one has non-amenable `ρ_i(Γ)''` along `ω`. Then the
     `M_i` are not Haagerup along `ω`.

   Alternative (b) is the form any construction with genuine vertex coordinates must take. It does
   not restrict whether witnesses exist: by item 1, a single-algebra witness `(M_0, σ_0)` yields a
   witness of type (b) with constant coordinates. What this artifact excludes are constructions whose
   genuine vertex coordinates have amenable images, such as the recorded lever with `M_n = R`.

   Parts (1) and (3) of Lemmas 1.5 and 1.6 do not use genuine vertex coordinates. Their proofs
   apply verbatim.
5. **Continuous multiplicities.** The concern in the target was that II_1 coordinates carry real
   multiplicities. Lemma 1.4 absorbs them through `floor(w_l d(x))`, with errors vanishing along the
   ultrafilter. The per-model claims only ever see integer dimensions.

## Literature and sources

- **Popa, arXiv:1308.3982.** The abstract page was fetched 2026-09-16. It confirms the second
  independence case in the form quoted by the target: `Q = prod_ω Q_n` with `Q_n` not intertwining
  into `Q_n' ∩ M_n`. Only the hypothesis shape is used here, to identify which models the lever
  concerns.
- **arXiv listing, sofic plus hyperlinear.** The arXiv API was queried 2026-09-16. No entry claims a
  hyperlinear non-sofic group, so the target is open as recorded. The newest relevant entry is
  Alekseev--Bradford, arXiv:2601.18742 (2026-01-26).
- **Kun--Thom.** The Theorem E pair and the wreath construction are taken from the repository node
  `kun-thom-nonsofic-wreath`. The primary source was not re-fetched here (API rate limit).
- **Dogon, arXiv:2211.10492, and Becker--Lubotzky, arXiv:1809.00632.** Consulted through repository
  nodes on flexible HS-instability of higher-rank Kazhdan groups. The primary sources were not
  re-fetched.
- **Standard facts used without citation.** Tracial ultraproducts and their unitary and projection
  lifts; martingale convergence of `E_k(a) -> a` in `R`; Connes's theorem that injective separable
  II_1 algebras are hyperfinite, used only inside the cited claim
  `kazhdan-images-in-haagerup-algebras-are-atomic`. Each ultraproduct step used in Theorem T is proved
  in §1.
