---
rg: 2
id: f-invariant-means-on-the-free-magma-are-never-products-proof
kind: route
title: Invariance of a product mean forces the right marginal of its left factor to be idempotent, and a self-referential set rules out idempotent and bookend means
target: f-invariant-means-on-the-free-magma-are-never-products
requires: []
artifacts:
  - experiments/free-magma-product-means-2026-09-17/check_product_mean_identities.py
  - experiments/free-magma-product-means-2026-09-17/output.txt
---

**Conventions.**
- `T` is the free magma on one generator `1`, with `#: T → N` the leaf count and `S_n = {#=n}`. Each `S_n` is finite.
- `*: T×T → T∖{1}` is a bijection. For `A, B ⊆ T` write `A*B = {a*b : a∈A, b∈B}`.
- Write `l(a*b) = a` and `r(a*b) = b` on `T∖{1}`.
- Means are finitely additive probability measures on all subsets. Integrals of bounded functions are the
  usual finitely additive integrals.
- For a map `φ` and a mean `μ`, the pushforward `φ_*μ(A) = μ(φ^{-1}A)` satisfies `∫ g∘φ dμ = ∫ g dφ_*μ` for
  bounded `g`. This holds for simple `g` and passes to the uniform limit.

**Fact 1 (rectangles).** `μ*β(A*B) = μ(A)β(B)`. For fixed `s`, freeness gives `χ_(A*B)(s*t) = χ_A(s)χ_B(t)`.

**Fact 2 (terms).** Let `w` be a binary term with leaves `y_1, …, y_k` in left-to-right order, and let
`w(μ_1, …, μ_k)` be the mean obtained by evaluating `w` with `*` on means. Then, for bounded `f`,
`w(μ_1,…,μ_k)(f) = ∫dμ_1(a_1) ∫dμ_2(a_2) ⋯ ∫dμ_k(a_k) f(w(a_1,…,a_k))`. The outermost integral is over the first
leaf.
- *Proof:* induction on `w = w_L * w_R`. By the definition of `*`,
  `w(μ⃗)(f) = ∫ d w_L(μ⃗_L)(u) ∫ d w_R(μ⃗_R)(v) f(u*v)`.
  Apply the hypothesis for `w_R` to the inner integral (with `u` fixed), then for `w_L` to the outer one.
- In particular, taking `w = (y_1*y_2)*y_3` and `w' = y_1*(y_2*y_3)` gives
  **Fact 3 (associator).** `x_1` is the bijection `(T*T)*T → T*(T*T)`, `(a*b)*c ↦ a*(b*c)`. For all means,
  `(x_1)_*((α*β)*γ) = α*(β*γ)`.
- By Fact 1 applied along `w`, `w(μ⃗)(w(A_1,…,A_k)) = ∏ μ_i(A_i)`, since the term map `T^k → T` is injective.

**Invariance, restated.** Let `ν` be F-invariant in the sense of the claim. Taking `Z = T` in `ν(x_1·Z) = ν(Z)`
gives `ν(ran x_1) = 1`. So for every `W ⊆ T` we have `ν(x_1^{-1}W) = ν(x_1·x_1^{-1}W) = ν(W ∩ ran x_1) = ν(W)`,
that is, `(x_1)_*ν = ν`, with `ν(dom x_1) = 1`. The same holds for `x_2`, whose domain is `T*dom(x_1)`.

**Lemma M (bookend kill, part (B)).** Fix a term `w` with `k ≥ 2` leaves and means `α_2, …, α_(k−1)`. Then no mean
`ν` satisfies `ν = w(ν, α_2, …, α_(k−1), ν)`. For `k = 2` this is Moore, arXiv:1807.05469, Section 2. The sets
below are his, with `w` in place of `*`.

*Construction.* Let `W = w(T, …, T)` be the set of elements whose top `k−1` products have the shape of `w`. Each
`s ∈ W` has unique coordinates `s = w(a_1(s), …, a_k(s))`, with `#a_i(s) < #s`. Define `Z ⊆ T` and `T_p ⊆ T` by
simultaneous recursion on `#`:
- `T_0 = T` and `T_(p+1) = w(T∖Z, T, …, T, T_p)`, where the first leaf carries `T∖Z` and the last carries `T_p`;
- `s ∈ Z` if and only if `s ∈ W` and `a_k(s) ∈ T_(#a_1(s))`.

Membership of `s` refers only to shorter elements, so the recursion is well founded.

*Proof.* Suppose `ν = w(ν, α⃗, ν)` and put `r = ν(Z)`.
1. **`ν` lives at infinity.** By Fact 2, `ν(W) = 1`, and `1 ∉ W`, so `ν(S_1) = 0`. For `n ≥ 2`, `S_n ∩ W` is the
   finite disjoint union of the sets `w(S_(n_1), …, S_(n_k))` with `∑ n_i = n` and all `n_i ≥ 1`. By the product
   rule, `ν(S_n) = ∑ ν(S_(n_1)) α_2(S_(n_2)) ⋯ ν(S_(n_k))`. Since `k ≥ 2`, every `n_1 < n`, so induction on `n` gives
   `ν(S_n) = 0` for all `n`.
2. **Geometric tails.** By the product rule, `ν(T_(p+1)) = ν(T∖Z)·1⋯1·ν(T_p) = (1−r)ν(T_p)`, so
   `ν(T_p) = (1−r)^p`. This is where both bookends are used: the first leaf carries `ν`, which gives the factor
   `1−r`, and the last leaf carries `ν`, which gives the recursion.
3. **The self-referential identity.** Fact 2 with `f = χ_Z` gives
   `r = ∫dν(a_1)∫dα_2(a_2)⋯∫dν(a_k) χ[a_k ∈ T_(#a_1)]`.
   The innermost integral is `ν(T_(#a_1)) = (1−r)^(#a_1)`, which depends on `a_1` alone. So
   `r = ∫ (1−r)^(#a) dν(a)`.
4. **No solution.**
   - If `r = 0`, the integrand is `1`, so `r = 1`, a contradiction.
   - If `r > 0`, fix `n`. The integrand is at most `(1−r)^n` off `⋃_(m<n) S_m`, which is `ν`-null by step 1. So
     `r ≤ (1−r)^n` for every `n`. Letting `n → ∞` gives `r ≤ 0`, a contradiction.  ∎

For `k = 2` this reproduces Moore's proof, verbatim in substance: "Fact 2 inductively implies that
μ(T_n) = (1-r)^n", and in the case `r = 0`, "μ(Z) = μ*μ(Z) = 1 ≠ 0 = μ(Z)" (arXiv:1807.05469, source
`no_idempotent.tex`, Section 2). Moore writes `r := μ(E)`, a typo for `μ(Z)`.

**Corollary M0.** No mean `ρ` on `T` satisfies `ρ*ρ = ρ`. This is the case `w = y_1*y_2`.

**Part (A) (product kill).** Suppose `ν = μ*β` is F-invariant, and put `ρ = r_*μ`. Since `ν(dom x_1) = 1` and
`dom x_1 = (T*T)*T`, Fact 1 gives `μ(T*T) = 1`, so `r` is defined `μ`-almost everywhere (set `r(1) = 1` on the
null set; this changes no integral).

1. **`x_2`-invariance makes `β` `x_1`-invariant.** For `B ⊆ T`, `x_2^{-1}(T*B) = T*(x_1^{-1}B)`, because
   `x_2(s*w) = s*x_1(w)`. By `(x_2)_*ν = ν` and Fact 1, `β(x_1^{-1}B) = μ(T)β(x_1^{-1}B) = μ(T)β(B) = β(B)`.
   Also `ν(dom x_2) = ν(T*dom x_1) = β(dom x_1)`, so `β(dom x_1) = 1`. Hence `(x_1)_*β = β`.
2. **`x_1`-invariance gives `β = ρ*β`.** The right marginal of `ν` is `ν(T*B) = β(B)`. On the other side,
   `x_1^{-1}(T*B) = {(a*b)*c : b*c ∈ B}`, so
   `ν(x_1^{-1}(T*B)) = ∫dμ(u) β({c : r(u)*c ∈ B}) = ∫dρ(b) β({c : b*c ∈ B}) = (ρ*β)(B)`.
   The middle equality is the pushforward rule for the bounded function `b ↦ β({c : b*c ∈ B})`. Now
   `(x_1)_*ν = ν` gives `β = ρ*β`.
3. **`ρ` is idempotent.** From step 1 and Fact 1, `1 = β((T*T)*T) = (ρ*β)((T*T)*T) = ρ(T*T)`. Fix `Y ⊆ T*T`, write
   `Y_a = {b : a*b ∈ Y}`, and put `Z = x_1(Y*T)`. Since `x_1` is injective, `x_1^{-1}Z = Y*T`.
   - By step 2 and Fact 1, `β(x_1^{-1}Z) = β(Y*T) = (ρ*β)(Y*T) = ρ(Y)`.
   - Also `{c : a*c ∈ Z} = Y_a*T`, so by step 2, `β(Z) = ∫dρ(a) β(Y_a*T) = ∫dρ(a) ρ(Y_a) = (ρ*ρ)(Y)`.
     Here `β(Y_a*T) = ρ(Y_a)` is again step 2 with Fact 1.
   - Step 1 says that these two numbers are equal, so `ρ*ρ(Y) = ρ(Y)` for every `Y ⊆ T*T`.

   Both `ρ` and `ρ*ρ` give `T*T` full mass, so `ρ*ρ = ρ` on all subsets. This contradicts Corollary M0.  ∎

The proof uses only `(x_1)_*ν = ν`, `(x_2)_*ν = ν` and the product form of `ν`. It never uses any property of `μ`
beyond its right marginal. In particular it covers the following:
- `ν = α*ν`, with `μ = α` and `β = ν`;
- `ν = ν*β`;
- idempotents, with `μ = β = ν`.

**Boundary (one-sided fixed points exist).** Fix `β`. For bounded `f`, `(μ*β)(f) = ∫ g dμ` with
`g(s) = ∫ f(s*t) dβ(t)` bounded. So `R_β : μ ↦ μ*β` is continuous for the weak* topology of `ℓ^∞(T)^*` and
affine on the weak*-compact convex set of means. By the Markov–Kakutani theorem (one map), `R_β` has a fixed point
`ν = ν*β`. So Lemma M needs `ν` at *both* bookends. By part (A), none of these fixed points is F-invariant.

**Sanity check.** The artifact script tests the finite identities used above with exact rational arithmetic on
random finitely supported means on trees with at most 6 leaves:
- Fact 1;
- Fact 3;
- `r_*((x_1)_*(μ*β)) = (r_*μ)*β` for `μ` on `T*T`;
- `x_2^{-1}(T*B) = T*x_1^{-1}B`;
- `(ρ*γ)(x_1(Y*T)) = ∫dρ(a) γ(Y_a*T)`;
- the product-rule instances of Lemma M, `(ν*ν)(T_(p+1)) = ν(T∖Z)ν(T_p)` and `(ν*ν)(Z) = ∫ ν(T_(#a)) dν(a)`.

Finitely supported means cannot be invariant, so the script checks the algebra only, not the contradiction.
