---
rg: 2
id: chain-group-germ-models-are-generically-faithful-proof
kind: route
title: Induct on amalgam length; a generic conjugator for the square-map factor makes the last evaluation point of every reduced word avoid the doubling orbits of the earlier ones, so perturbing the conjugator on one arc moves the endpoint, and Baire category gives a comeagre set of faithful, nowhere locally trivial models; Bass-Serre theory of the zoom's normal closure gives the splitting criterion
target: chain-group-germ-models-are-generically-faithful
requires: []
---

Notation as in the target. `H = C_{Homeo_+(R)}(δ)`, with `δ(x) = 2x`. `A_0 = ⟨δ, s_0⟩` with
`s_0(x) = x|x|`, and `B = ⟨δ, σ⟩` with `σ(x) = x+1`. `θ_ψ(s) = ψ s_0 ψ^-1`,
`θ_ψ(δ) = δ`, `θ_ψ(σ) = σ`. So `θ_ψ(a) = ψ θ_id(a) ψ^-1` for `a ∈ A`, and `θ_ψ(b) = θ_id(b)` for
`b ∈ B`.

## Step 0. Topology

`Homeo_+(R)` with the compact-open topology is a Polish topological group; a complete metric is
`Σ_n 2^-n min(1, sup_{|x| ≤ n} (|f(x) - g(x)| + |f^-1(x) - g^-1(x)|))`. `H` is a closed subgroup,
hence Polish, hence a Baire space. For fixed `u ∈ G_1`, the map
`H × R -> R, (ψ, x) ↦ θ_ψ(u)(x)` is continuous: it is a finite composition of evaluations of
`ψ^{±1}` and of fixed homeomorphisms, and evaluation and inversion are continuous. So for every
open interval `I`,

    O(u, I) = {ψ ∈ H : θ_ψ(u)(x) ≠ x for some x ∈ I}

is open in `H`.

## Step 1. The factors, and the base case

**Lemma 1.** Let `Γ = ⟨t, e | t e t^-1 = e^2⟩ ≅ BS(1,2)`, and let `π : Γ -> K` be a homomorphism
with `π(e)` of infinite order. Then `π` is injective.

*Proof.* `E = ⟨⟨e⟩⟩ ≅ Z[1/2]`, and every `1 ≠ y ∈ E` has `y^{2^j} = e^k` with `k ≠ 0`, so
`ker π ∩ E = 1`. Then `[ker π, E] ⊆ ker π ∩ E = 1`. But `C_Γ(E) = E`, since `t^m y` with `m ≠ 0`
conjugates `e` to `e^{2^m}`. So `ker π ⊆ E`, and `ker π = 1`. ∎

**Lemma 2 (base case).** For every `ψ ∈ H`, every `1 ≠ u ∈ A ∪ B` and every open interval `I`,
`θ_ψ(u)` is not the identity on `I`.

*Proof.* On `(0, ∞)` put `x = 2^τ`. Then `δ` becomes `τ ↦ τ + 1` and `s_0` becomes `τ ↦ 2τ`. On
`(-∞, 0)` put `x = -2^τ`; since `δ` and `s_0` are odd, the same formulas hold. So `θ_id(A)` acts on
each half-line as the affine group `⟨τ+1, 2τ⟩`, which is faithful by Lemma 1. A nontrivial affine
map is not the identity on any interval. Every open interval contains an interval inside one
half-line, so `θ_id(a)` is nowhere locally trivial for `a ≠ 1`, and so is its conjugate
`θ_ψ(a) = ψ θ_id(a) ψ^-1`. The group `θ_ψ(B) = {x ↦ 2^k x + q}` is faithful by Lemma 1, and its
nontrivial elements are affine maps other than the identity. ∎

## Step 2. Normal forms

Let `ℓ(u)` be the amalgam length: `ℓ = 0` on `C`, `ℓ = 1` on `(A ∪ B) \ C`, and otherwise the
length of a reduced alternating word in letters from `A \ C` and `B \ C`. By the normal form
theorem, such a word of length `≥ 1` is nontrivial, and `ℓ` is well defined.

**Reduction.** Let `ℓ(u) = m ≥ 2`, with reduced word `u = x_1 ⋯ x_m`.
- If `m` is odd, then `x_1` and `x_m` lie in the same factor, and `u' = x_m u x_m^-1` has
  `1 ≤ ℓ(u') < m`: either `x_m x_1 ∉ C`, giving length `m-1`, or `x_m x_1 ∈ C` is absorbed into
  `x_2`, giving length `m-2`.
- If `m = 2n` is even and `x_1 ∈ B`, then `u'' = x_1^-1 u x_1 = x_2 ⋯ x_m x_1` is reduced
  alternating of length `m`, with leftmost letter in `A \ C` and rightmost letter in `B \ C`.

Since `θ_ψ(g u g^-1) = θ_ψ(g) θ_ψ(u) θ_ψ(g)^-1`, the map `θ_ψ(u)` is trivial on `I` iff
`θ_ψ(u')` is trivial on `θ_ψ(g)^-1(I)`, which is again an open interval. In the even case the
conjugator is `x_1 ∈ B`, and `θ_ψ(x_1)` does not depend on `ψ`.

## Step 3. The trajectory and its coincidences

Fix `u = a_n b_n ⋯ a_1 b_1` with `n ≥ 1`, `a_i ∈ A \ C` and `b_i ∈ B \ C`. Put `α_i = θ_id(a_i)`
and `β_i = θ_id(b_i)`. For `ψ ∈ H` and `t_0 ∈ R` define, for `i = 1, …, n`,

    u_i = β_i(t_{i-1}),   v_i = ψ^-1(u_i),   z_i = α_i(v_i),   t_i = ψ(z_i),

so `t_i = θ_ψ(a_i b_i)(t_{i-1})` and `t_n = θ_ψ(u)(t_0)`. The points `v_i` and `z_i` are where
`ψ^-1` and `ψ` are evaluated. Each of them is a homeomorphism of `R` applied to `t_0`. Put

    E(t_0) = {z_1, …, z_{n-1}, v_1, …, v_n}.

**Lemma 3.** Let `ψ ∈ H` be such that every `1 ≠ u'` with `ℓ(u') < 2n` is nowhere locally trivial
under `θ_ψ`, and let `I` be an open interval. Then the set of `t_0 ∈ I` with
`z_n ∈ {0} ∪ ⋃_{k ∈ Z} 2^k E(t_0)` is meagre in `I`. So some `t_0 ∈ I` avoids it.

*Proof.* `z_n` is a homeomorphism of `t_0`, so `z_n = 0` at one point at most. It remains to treat
the sets `Z_{i,k} = {t_0 ∈ I : z_n = 2^k z_i}` for `1 ≤ i ≤ n-1` and
`V_{i,k} = {t_0 ∈ I : z_n = 2^k v_i}` for `1 ≤ i ≤ n`. There are countably many, and each is
closed in `I`. We show each has empty interior.

Suppose `Z_{i,k}` contains an open interval `U`. Let `W = a_n b_n ⋯ a_{i+1} b_{i+1}`, so that
`t_n = θ_ψ(W)(t_i)`. Then `ψ^-1 θ_ψ(W) ψ = δ^k` on the open interval `z_i(U)`. Since `ψ` commutes
with `δ`, this says `θ_ψ(δ^-k W)` is the identity on `ψ(z_i(U)) = t_i(U)`. But
`δ^-k W = (δ^-k a_n) b_n ⋯ a_{i+1} b_{i+1}` is reduced alternating with `δ^-k a_n ∈ A \ C`. Its
length is `2(n-i)`, with `2 ≤ 2(n-i) ≤ 2n-2`, so it is nontrivial with `ℓ < 2n`. This
contradicts the hypothesis.

Suppose `V_{i,k}` contains an open interval `U`. Let `W' = a_n b_n ⋯ b_{i+1} a_i`, so that
`t_n = θ_ψ(W')(u_i)`. Then `ψ^-1 θ_ψ(W') ψ = δ^k` on `v_i(U)`, so `θ_ψ(δ^-k W')` is the identity on
`u_i(U)`. The word `δ^-k W'` is:
- `(δ^-k a_n) b_n ⋯ b_{i+1} a_i` for `i < n`, reduced of length `2(n-i)+1 ≤ 2n-1`;
- `δ^-k a_n ∈ A \ C` for `i = n`, of length 1.

Either way it is nontrivial with `ℓ < 2n`, a contradiction.

`I` is a Baire space, so the countable union of these closed sets with empty interior, together
with at most one point, is meagre and has dense complement. ∎

## Step 4. One-arc perturbation

**Lemma 4.** Let `ψ`, `I` and `t_0 ∈ I` be as in Lemma 3, with `t_0` outside the meagre set, and
let `W ∋ ψ` be open in `H`. Then some `ψ' ∈ W` has `θ_{ψ'}(u)(t_0) ≠ t_0`.

*Proof.* If `θ_ψ(u)(t_0) ≠ t_0`, take `ψ' = ψ`. Otherwise `z_n = ψ^-1(t_0) ≠ 0`; say `z_n > 0`
(the case `z_n < 0` is symmetric). The images of the points of `E(t_0) \ {0}` in the two circles
`(R \ {0})/⟨δ⟩` form a finite set, and it misses the image of `z_n`. So for small `η ∈ (0, 1/4)`
the interval `J = (z_n(1-η), z_n(1+η))` has these properties:
- its translates `2^k J̄` are pairwise disjoint;
- `S = ⋃_k 2^k J̄` misses `E(t_0) ∪ {0}`.

Choose a homeomorphism `g` of `J̄` that fixes its endpoints and has `g(z_n) ≠ z_n`. Define
`ε ∈ H` by:
- `ε(2^k y) = 2^k g(y)` for `y ∈ J̄`;
- `ε = id` off `S`.

`ε^{±1}` moves a point `x ∈ 2^k J̄` by at most the length `2^{k+1} η z_n ≤ 4η|x|`. So on
`[-M, M]`, `|ε^{±1}(x) - x| ≤ 4ηM`, and `ε -> id` in `H` as `η -> 0`. Since `H` is a topological
group, `ψ' = ψ ε ∈ W` for small `η`.

Now run the trajectory for `ψ'` from the same `t_0`. We have `ψ'^-1 = ε^-1 ψ^-1`. Inductively
`u_i` is unchanged:
- `ψ'^-1(u_i) = ε^-1(v_i) = v_i`, since `v_i ∉ S`;
- so `z_i` is unchanged;
- for `i < n`, `ψ'(z_i) = ψ(ε(z_i)) = ψ(z_i) = t_i`, since `z_i ∉ S`.

At the last step, `ψ'(z_n) = ψ(g(z_n)) ≠ ψ(z_n) = t_0`, because `ψ` is injective. So
`θ_{ψ'}(u)(t_0) ≠ t_0`. ∎

## Step 5. Baire induction (Statement 1)

For `m ≥ 1` let `L_m` be the set of `ψ ∈ H` such that, for every `1 ≠ u` with `ℓ(u) ≤ m` and
every open interval `I`, `θ_ψ(u)|_I ≠ id`. By Lemma 2, `L_1 = H`. Every open interval contains
one with rational endpoints, so

    L_m = L_{m-1} ∩ ⋂ { O(u, I) : ℓ(u) = m, I rational }.

By induction on `m`, `L_m` is a countable intersection of dense open sets. For the step it is
enough to show that each such `O(u, I)` is dense; it is open by Step 0. Let `W ⊆ H` be nonempty
and open. `L_{m-1}` is comeagre, hence dense by Baire, so pick `ψ_1 ∈ W ∩ L_{m-1}`.
- **`m` odd.** By the Reduction, `u` is conjugate to some `u'` with `1 ≤ ℓ(u') < m`. Since
  `ψ_1 ∈ L_{m-1}`, `θ_{ψ_1}(u')` is nontrivial on every interval, so `ψ_1 ∈ O(u, I)`.
- **`m = 2n` even.** By the Reduction we may assume `u = a_n b_n ⋯ a_1 b_1` as in Step 3. This
  may need a conjugation by a letter of `B`, which replaces `I` by an open interval `I'` that does
  not depend on `ψ`. Lemma 3 applies to `ψ_1`, since `ψ_1 ∈ L_{m-1}`. Lemma 4 then gives
  `ψ' ∈ W ∩ O(u, I)`.

So `F = ⋂_m L_m` is comeagre. For `ψ ∈ F` and `1 ≠ u ∈ G_1`, `θ_ψ(u)` is nontrivial on every
interval `(T, ∞)`, so its germ at `+∞` is nontrivial. Hence `θ_ψ` and `θ_ψ^∞` are injective and
`Q_ψ ≅ G_1`. ∎

## Step 6. The smooth model is not in F (Statement 2)

For `ψ = id` and `x > 0`, `ρ(x) = s_0^-1(2 s_0(x)) = √(2x^2) = √2·x`, and likewise for `x < 0`. So
`ρσρ^-1(x) = x + √2`, which commutes with `σ`. In `G_1`, `ρ = s^-1 δ s` satisfies `ρ^2 = δ`, so
`ρ ∈ A \ C`. Hence

    [ρσρ^-1, σ] = ρ σ ρ^-1 σ ρ σ^-1 ρ^-1 σ^-1

is reduced alternating of length 8, and so nontrivial. ∎

## Step 7. Splitting criterion (Statement 3)

**Lemma 5.** Let `r : G_1 -> A` be the retraction with `s ↦ s`, `δ ↦ δ` and `σ ↦ 1`. (It is well
defined, since the relations are respected.) Then `N = ker r = ⟨⟨σ⟩⟩` and
`N = *_{a ∈ T} a N_B a^-1`, where `T` is a transversal of `A/C`.

*Proof.* `G_1/⟨⟨σ⟩⟩ = A`, so `ker r = ⟨⟨σ⟩⟩`. Let `N` act on the Bass-Serre tree of `A *_C B`.
- `r` is injective on every conjugate of `A`, so `N ∩ gAg^-1 = 1`, and likewise
  `N ∩ gCg^-1 = 1`.
- `N ∩ gBg^-1 = g(N ∩ B)g^-1 = g N_B g^-1`, because `r|_B` is the retraction `B -> C` killing `σ`.
- Since `NA = G_1`, the quotient `N \ T` has one `A`-vertex. Its `B`-vertices and its edges are
  indexed by `G_1/NB ≅ A/C` and `G_1/NC ≅ A/C`.

So `N \ T` is a star, hence a tree. It lifts to the star at the vertex `A`, whose edges are `aC`
and whose far endpoints are `aB`, for `a ∈ T`. A tree of groups with trivial edge groups has as
fundamental group the free product of its vertex groups, which here is
`1 * (*_{a ∈ T} a N_B a^-1)`. ∎

**Lemma 6 (topological linearization).** Let `D` be an increasing homeomorphism of `R` with
`D(x+1) = D(x) + 2`, and suppose some iterate satisfies `D^m(y) - D^m(x) ≥ λ(y - x)` for all
`x < y`, with `λ > 1`. Then there is an increasing homeomorphism `h` with `h(x+1) = h(x) + 1`,
`|h - id| ≤ P` and `h D h^-1 = (x ↦ 2x)`, where `P = max |D(x) - 2x|`.

*Proof.* Put `h_n = 2^-n D^n`. Then `h_n(x+1) = h_n(x) + 1`, and
`|h_{n+1} - h_n| = 2^{-n-1} |D(D^n x) - 2 D^n x| ≤ 2^{-n-1} P`. So `h_n -> h` uniformly, and
`h` is continuous and nondecreasing, with `h(x+1) = h(x) + 1`, `|h - id| ≤ P` and `h D = 2h`.
Suppose `h(x) = h(y)` with `x < y`. Then `h(D^{mj} y) = h(D^{mj} x)`, while
`D^{mj} y - D^{mj} x ≥ λ^j (y - x)`, and this exceeds `2P` for large `j`. That contradicts
`|h - id| ≤ P`. So `h` is injective, hence a homeomorphism. ∎

**Proof of Statement 3.** Let `θ : G_1 -> Germ_{+∞}` be a germ representation with:
- `θ(σ) = x+1`;
- `θ(δ)` the germ of a lift `D` as in Lemma 6;
- `θ(s)` any germ with `θ(s) θ(δ) θ(s)^-1 = θ(δ)^2`.

The models `θ_ψ^∞` are of this kind, with `D = 2x`. Conjugating by `h` from Lemma 6 fixes
`x+1`, so we may assume `θ(δ) = 2x`. By Lemma 1, `θ|_A` and `θ|_B` are injective, since the germs
of `2x` and `x+1` have infinite order.

Write `x = 2^τ` near `+∞`, and let `𝒟` be the group of germs `g` with `g(τ) - τ -> 0`. If `f` is
a germ that is uniformly continuous near `+∞` in `τ`, then `f 𝒟 f^-1 ⊆ 𝒟`: indeed
`f g f^-1(τ) - τ = f(g(r)) - f(r)` with `r = f^-1(τ) -> ∞`. The generators and their inverses are
uniformly continuous in `τ`:
- `σ^{±1}` is `τ ↦ log_2(2^τ ± 1)`;
- `δ^{±1}` is `τ ↦ τ ± 1`;
- `s^{±1}` has `S(τ + 1) = S(τ) + 2`, so `S(τ) - 2τ` is periodic, and similarly for `S^-1`.

`σ` lies in `𝒟`, so `θ(N) ⊆ 𝒟`. Now let `1 ≠ a = s^m y ∈ A`, with `y ∈ ⟨⟨δ⟩⟩_A`.
- If `m ≠ 0`, then `θ(a)(τ) - τ = (2^m - 1)τ + O(1)`, because `θ(y)` commutes with `τ + 1` and so
  has bounded displacement.
- If `m = 0`, then `θ(y)` commutes with `τ + 1` and has no fixed point, since `y^{2^j} = δ^k` with
  `k ≠ 0`. So its displacement is periodic and bounded away from 0.

Either way `θ(a) ∉ 𝒟`, so `θ(N) ∩ θ(A) = 1`. Since `G_1 = N ⋊ A`, `θ(na) = 1` forces
`θ(a) ∈ θ(N) ∩ θ(A)`. So `a = 1`, and then `θ(n) = 1`. Hence `θ` is injective iff `θ|_N` is.

By Lemma 5, `θ|_N` is a homomorphism out of `*_{a ∈ T} a N_B a^-1`. It is injective on each
factor, since the factors lie in conjugates of `B`. So it is injective iff the images generate
their free product. ∎

## Step 8. Where the PL realizations sit

Let `(δ, s)` be a realization with `σ = x+1`, where `δ` satisfies Lemma 6, conjugated by `h` so
that `δ = 2x`. In `τ = log_2 x`, `s` becomes a germ `S` with `S(τ+1) = S(τ) + 2`, which extends
uniquely to a lift on all of `R`. Suppose some iterate of `S` expands, as in Lemma 6.
- Lemma 6, applied to `D = S`, gives `Φ` with
  `Φ(τ+1) = Φ(τ) + 1` and `Φ S Φ^-1 = 2τ`.
- Put `ψ(x) = 2^{Φ^-1(log_2 x)}` for `x > 0`, and extend it oddly. Then `ψ ∈ H`, and the germ of
  `s` at `+∞` equals that of `ψ s_0 ψ^-1`.

So the realization is conjugate at `+∞` to `θ_ψ^∞`, and it is faithful iff
`ψ ∈ F^∞ = {ψ : θ_ψ^∞ injective}`. That set is comeagre and contains `F`. Dyadic PL data are
countable, so these `ψ` form a countable set. ∎

## Remarks

- The proof of Statement 1 uses only three facts:
  - both factors act nowhere locally trivially;
  - the amalgamated generator acts as `2x`;
  - the perturbations `ψ` range over its centralizer.

  So the same argument should give generic faithful models for other cyclic amalgams of groups
  acting on the line in this way. This is not written out here.
- For the smooth model `ψ = id`, `ρ = √2 x` sits in the affine group together with `σ`. That is
  the soluble zoom-root pair of the w17 firewall. The generic `ψ` destroys it, because
  `ρ = ψ(√2 ψ^-1(x))` is no longer affine.
