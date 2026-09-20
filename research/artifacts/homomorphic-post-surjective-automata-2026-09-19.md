# Post-surjective homomorphic automata over finite group alphabets (2026-09-19)

Author: swarm-0917-w20-w20-gs-last1. Proves `homomorphic-post-surjective-automata-are-automorphisms`.

## 0. Setting and conventions

- `G` is any group; `V` is a finite group with identity `e`. Configurations are `x : G -> V`, with the
  shift `(g.x)(h) = x(g^(-1) h)` and pointwise product. `e` also denotes the constant identity configuration.
- `V[G]` is the subgroup of finitely supported configurations (`x(g) = e` off a finite set). It is dense in `V^G`.
- A **homomorphic automaton** is a cellular automaton `L : V^G -> V^G`, `L(x)(g) = mu((g^(-1)x)|_M)`, with finite
  memory `M ∋ 1`, that is a group homomorphism for the pointwise product.
- For `W <= V` with `mu(W^M) <= W`, write `L|_W` for the restricted homomorphic automaton on `W^G`.
- Asymptotic, pre-injective and post-surjective are as in `linear-strict-pairs-are-transposes-of-post-surjective-automata`.

**Lemma 0.1 (local rule).** `mu : V^M -> V` is a group homomorphism. Put `mu_m(v) = mu(v at m, e elsewhere)`. Then
`mu(v) = prod_m mu_m(v_m)`, in any order, and the images `mu_m(V)` pairwise commute elementwise.

*Proof.* `x -> x|_M` is a surjective homomorphism `V^G -> V^M`, and `L(x)(1) = mu(x|_M)`, so `mu` is a homomorphism.
The coordinate subgroups of `V^M` commute pairwise and generate `V^M`, and their images under `mu` are the
`mu_m(V)`. □

**Lemma 0.2 (dictionary).**
- (a) `L` is post-surjective iff `L(V[G]) = V[G]`.
- (b) `L` is pre-injective iff `ker L ∩ V[G] = {e}`.
- (c) If `L` is bijective, its inverse is a homomorphic automaton.

*Proof.*
- `L(V[G]) <= V[G]` always, since `mu(e) = e`.
- (a) Post-surjectivity at `x = e` is `L(V[G]) = V[G]`. Conversely, let `y'` be asymptotic to `L(x)`. Then
  `u = L(x)^(-1) y'` lies in `V[G]`. Choose `w ∈ V[G]` with `L(w) = u`; then `x' = x w` is asymptotic to `x` and
  `L(x') = y'`.
- (b) Asymptotic `x != x'` with `L(x) = L(x')` give `x^(-1) x' ∈ ker L ∩ V[G] \ {e}`, and conversely.
- (c) By compactness of `V^G` the inverse is continuous. It is equivariant, and it is a homomorphism. Curtis–Hedlund
  holds for finite alphabets over any group, so it is an automaton. □

**Lemma 0.3 (sections).** Let `N <= W <= V` with `mu(W^M) <= W` and `mu(N^M) <= N`, and `N` normal in `W`. Then `L`
induces a homomorphic automaton `L_(W/N)` on `(W/N)^G`, and:
- (a) If `L|_W` maps `W[G]` onto `W[G]`, then `L_(W/N)` maps `(W/N)[G]` onto `(W/N)[G]`.
- (b) If `L_(W/N)` and `L|_N` are bijective, so is `L|_W`.

*Proof.* (a) holds because sitewise lifts of a finitely supported configuration can be chosen finitely supported.
(b) is the five lemma for the exact sequence `N^G -> W^G -> (W/N)^G`, whose maps commute with `L`.
- *Injectivity.* `L(x) = e` gives `L_(W/N)(xN) = e`, so `x ∈ N^G`, so `x = e`.
- *Surjectivity.* Given `y`, choose `x` with `L_(W/N)(xN) = yN`. Then `L(x)^(-1) y ∈ N^G` equals `L(n)`, and
  `y = L(x n)`. □

## 1. Linear base

Here `V = F_p^n` (column vectors), and `tau_alpha(x)(g) = sum_h alpha_h x(gh)` for `alpha ∈ M_n(F_p[G])`. We use
Lemma 1 of `research/artifacts/homomorphic-group-alphabet-surjunctivity-2026-09-16.md` (ESTABLISHED, with proof there):
every `F_p`-linear CA on `V^G` is some `tau_alpha`, `tau_alpha tau_beta = tau_(alpha beta)`, `tau_1 = id`, and
`alpha -> tau_alpha` is injective. An additive CA on `V^G` is `F_p`-linear, because `F_p`-scalars are integers.

**Lemma 1.1 (post-surjective linear automata are automorphisms under direct finiteness).** Suppose `tau_alpha` maps
`V[G]` onto `V[G]`, and `M_n(F_p[G])` is directly finite. Then `tau_alpha` is bijective.

*Proof.*
- Let `delta_j ∈ V[G]` be `e_j` at `1` and `0` elsewhere. Choose `w_j ∈ V[G]` with `tau_alpha(w_j) = delta_j`.
- Define `S(y)(h) = sum_(g ∈ G, j) y_j(g) w_j(g^(-1) h)`.
  - For fixed `h` only `g ∈ h supp(w_j)^(-1)` contribute, so the sum is finite and `S` reads `y` on a finite window.
  - It is `F_p`-linear and equivariant, so `S` is a linear CA, `S = tau_beta`.
- On `V[G]`, `y = sum_(g,j) y_j(g) (g.delta_j)` is a finite sum. So `tau_alpha S (y) = sum y_j(g) g.delta_j = y`.
- `tau_alpha S` and `id` are continuous and agree on the dense set `V[G]`, so `tau_(alpha beta) = id = tau_1`, and
  `alpha beta = 1`.
- Direct finiteness gives `beta alpha = 1`, so `tau_beta tau_alpha = id`. Hence `tau_alpha` is bijective with
  inverse `tau_beta`. □

**Lemma 1.2 (sharpness).** Suppose `alpha beta = 1 != beta alpha` in `M_n(F_p[G])`. Then `tau_alpha` is
post-surjective and not pre-injective.

*Proof.*
- `tau_alpha tau_beta = id`, and `tau_beta(V[G]) <= V[G]`, so `tau_alpha(V[G]) = V[G]`. Lemma 0.2(a) gives
  post-surjectivity.
- Put `gamma = beta alpha - 1 != 0`. Then `alpha gamma = alpha beta alpha - alpha = 0`, so `tau_alpha tau_gamma = 0`.
- `tau_gamma != 0` by injectivity of `alpha -> tau_alpha`.
  - It is nonzero on some `delta_j`: otherwise it vanishes on `V[G]` by linearity and equivariance, hence
    everywhere by density.
  - So `u = tau_gamma(delta_j)` is a nonzero element of `ker tau_alpha ∩ V[G]`.
- Lemma 0.2(b) says `tau_alpha` is not pre-injective. □

## 2. Abelian alphabets

**Proposition 2.1.** Let `V` be finite abelian. Suppose `M_n(F_p[G])` is directly finite for every prime `p` and
every `n` such that `F_p^n` is a subquotient of `V`. If a homomorphic `L` maps `V[G]` onto `V[G]`, then `L` is
bijective.

*Proof.*
- **Primary parts.** `V = prod_p V_p`. Each `V_p^G` is the set of `x` with `p^N x = 0` for `N` large, and `L` is
  additive, so `L(V_p^G) <= V_p^G`.
  - The projection of `V[G]` onto `V_p[G]` commutes with `L`, so `L|_(V_p)` maps `V_p[G]` onto `V_p[G]`.
  - `L = prod_p L|_(V_p)`. So we may assume `V` is a `p`-group.
- **Filtration.** `V_i = p^i V`, for `0 <= i <= s`, with `V_s = 0`. Each `mu_m` is additive, so `mu(V_i^M) <= V_i`.
- **Onto each layer.** `L|_(V_i)` maps `V_i[G]` onto `V_i[G]`.
  - Let `u ∈ V_i[G]`. Choose `u_0 ∈ V[G]` with `p^i u_0 = u`, sitewise, with `u_0(g) = 0` where `u(g) = 0`.
  - Choose `w_0 ∈ V[G]` with `L(w_0) = u_0`.
  - Then `p^i w_0 ∈ V_i[G]` and `L(p^i w_0) = p^i u_0 = u`.
- **Graded pieces.** By Lemma 0.3(a), the induced automaton on `(V_i / V_(i+1))^G` maps finitely supported onto
  finitely supported.
  - `V_i / V_(i+1) ≅ F_p^(d_i)` is a subquotient of `V`, and the induced automaton is `F_p`-linear.
  - Lemma 1.1 makes it bijective.
- **Assembly.** Lemma 0.3(b), by descending induction on `i`, makes `L|_(V_i)` bijective for every `i`. At `i = 0`
  this is `L`. □

*Remark.* The ranks that occur are `d_i = dim_(F_p)(p^i V / p^(i+1) V)`. So it suffices that `M_d(F_p[G])` be
directly finite for `p^d <= |V|`. Lemma 1.2 shows that the hypothesis cannot be dropped at `V = F_p^n`.

## 3. Centerless alphabets (no hypothesis on `G`)

**Lemma 3.1.** Let `D` be a finite group with `Z(D) = 1`, and let `K_1, ..., K_r <= D` commute pairwise
elementwise and generate `D`. Then `D` is the internal direct product of the `K_a`. If moreover `D` is directly
indecomposable and nontrivial, then exactly one `K_a` equals `D` and all others are trivial.

*Proof.*
- `K_a` is normalized by itself and centralized by every `K_b`, `b != a`. So it is normal, and `D = K_1 ... K_r`.
- Let `x ∈ K_a ∩ prod_(b != a) K_b`.
  - As an element of `prod_(b != a) K_b` it commutes with `K_a`.
  - As an element of `K_a` it commutes with every `K_b`, `b != a`.
  - So `x ∈ Z(D) = 1`, and the product is direct.
- Indecomposability then leaves one nontrivial factor, which is `D`. □

**Proposition 3.2.** Let `W` be a finite group with `Z(W) = 1`, and `L` a homomorphic automaton on `W^G` mapping
`W[G]` onto `W[G]`. Then `L` is bijective. More precisely, `L` permutes the "factor sites" defined below, up to
isomorphisms of the factors. No hypothesis on `G` is needed.

*Proof.*
- **Setup.** Assume `W != 1`.
  - Fix a decomposition `W = D_1 x ... x D_r` into nontrivial directly indecomposable factors, with projections
    `pi_i`.
  - Each `D_i` is centerless, since `Z(W) = prod Z(D_i)`.
  - Put `H_m = mu_m(W)`.
- **The local rule is onto.** Evaluating at `1`, the surjection `L : W[G] -> W[G]` shows that
  `mu : W^M -> W` is onto. So the `H_m` generate `W` and commute pairwise (Lemma 0.1).
- **Step 1 (each output factor reads one memory cell).** Fix `i`.
  - The groups `pi_i(H_m)`, `m ∈ M`, commute pairwise and generate `D_i`.
  - By Lemma 3.1 there is a unique `m(i)` with `pi_i(H_(m(i))) = D_i`, and `pi_i(H_m) = 1` for `m != m(i)`.
  - Hence `pi_i(L(x)(g)) = nu_i(x(g m(i)))`, where `nu_i = pi_i ∘ mu_(m(i)) : W -> D_i` is onto.
- **Step 2 (each output factor reads one input factor).**
  - The groups `nu_i(D_j)`, `j = 1..r`, commute pairwise and generate `D_i`.
  - By Lemma 3.1 there is a unique `phi(i)` with `nu_i(D_(phi(i))) = D_i`, and `nu_i(D_j) = 1` otherwise.
  - So `nu_i = theta_i ∘ pi_(phi(i))`, with `theta_i : D_(phi(i)) -> D_i` onto.
- **Step 3 (factor sites).** Identify `W^G` with `prod_((h, j) ∈ G x {1..r}) D_j`, the "input factor sites".
  - The output factor site `(g, i)` is `theta_i` applied to the input factor site `(g m(i), phi(i))`.
  - So the input site `(h, j)` is read exactly by the output sites `(h m(i)^(-1), i)` with `i ∈ phi^(-1)(j)`.
  - These output sites are pairwise distinct, and every output site reads exactly one input site.
  - Hence `L` is the product, over input sites `(h, j)`, of the maps
    `Theta_j = (theta_i)_(i ∈ phi^(-1)(j)) : D_j -> prod_(i ∈ phi^(-1)(j)) D_i`.
- **Step 4 (counting).**
  - Surjectivity of `L` onto `W[G]`, applied to configurations supported on the output sites reading one input
    site, shows every `Theta_j` is onto. So `prod_(i ∈ phi^(-1)(j)) |D_i| <= |D_j|`, with an empty product equal to 1.
  - Multiplying over `j` gives `prod_i |D_i| <= prod_j |D_j|`. Both sides equal `|W|`, so every inequality is an
    equality.
  - So every `Theta_j` is a bijection, and `L`, a product of bijections, is bijective.
  - (Indecomposability of `D_j` then forces `|phi^(-1)(j)| = 1`, so `phi` is a permutation and each `theta_i` is
    an isomorphism. This is not needed.) □

*Remark.* Step 4 is the only place where surjectivity is used beyond Step 1. This is the dual of the injective case
in the 2026-09-16 artifact, where the nonabelian socle layer of an injective automaton is shown to be a permuted
shift.

## 4. Arbitrary finite group alphabets

`P(V)` is the set of primes `p` such that `Z/p` is a composition factor of `V`.

**Lemma 4.1 (Grün).** If `P` is a finite perfect group, then `Z(P / Z(P)) = 1`.

*Proof.* Write `Z = Z(P)`, and let `xZ` be central in `P/Z`.
- Then `[x, p] = x^(-1) p^(-1) x p ∈ Z` for all `p`.
- `p -> [x, p]` is a homomorphism `P -> Z`, since `[x, pq] = [x, q] q^(-1) [x, p] q = [x, p][x, q]` with `[x, p]` central.
- `Z` is abelian and `P = P'`, so this homomorphism is trivial. Hence `x ∈ Z`. □

**Theorem 4.2.** Let `G` be any group and `V` any finite group. Suppose `M_n(F_p[G])` is directly finite for every
`p ∈ P(V)` and every `n >= 1` with `p^n <= |V|`. Then every homomorphic automaton `L : V^G -> V^G` that maps
`V[G]` onto `V[G]` is bijective. Equivalently, by Lemma 0.2, every post-surjective homomorphic automaton on `V^G`
is an automorphism, and in particular pre-injective. If `V` has no abelian composition factor, the hypothesis is
vacuous and the conclusion holds over every group.

*Proof.* Let `V = V^(0) > V^(1) > ... > V^(k) = P` be the derived series, with `P` perfect.
- **Invariance.** `(V^M)^(i) = (V^(i))^M` for the finite product `V^M`. So
  `mu((V^(i))^M) = mu((V^M)^(i)) <= V^(i)`.
- **Onto each term.** Suppose `L|_W` maps `W[G]` onto `W[G]`, where `W = V^(i)`. Then `L|_(W')` maps `W'[G]` onto
  `W'[G]`.
  - Every element of `W'` is a product of at most `c = |W|` commutators. So every `u ∈ W'[G]` is a product
    `prod_(j <= c) [a_j, b_j]`, with `a_j, b_j ∈ W[G]` (pad with trivial commutators sitewise).
  - Choose `a'_j, b'_j ∈ W[G]` with `L(a'_j) = a_j` and `L(b'_j) = b_j`.
  - Then `u = L(prod_j [a'_j, b'_j])`, and the argument lies in `W'[G]`.
- **Abelian layers.** By Lemma 0.3(a), `L` induces on `(V^(i) / V^(i+1))^G` an automaton mapping finitely supported
  onto finitely supported.
  - Every `F_p^n` that is a subquotient of this abelian group has `p ∈ P(V)` and `p^n <= |V|`.
  - So Proposition 2.1 makes the induced automaton bijective.
- **The perfect term.** Let `Z = Z(P)` and `H_m = mu_m(P)`.
  - `L|_P` is onto `P[G]`, so `mu : P^M -> P` is onto, and the `H_m` generate `P` and commute pairwise.
  - For `z ∈ Z`, the element `mu_m(z)` commutes with `H_m`, because `z` is central, and with `H_(m')` for
    `m' != m`, by Lemma 0.1. So `mu_m(z) ∈ Z`, and `mu(Z^M) <= Z`.
  - `P/Z` is centerless (Lemma 4.1). The induced automaton on `(P/Z)^G` maps `(P/Z)[G]` onto itself (Lemma
    0.3(a)), so it is bijective (Proposition 3.2).
  - **`L|_Z` is onto `Z[G]`.** Let `z ∈ Z[G]`, and choose `w ∈ P[G]` with `L(w) = z`. The image of `w` in
    `(P/Z)^G` is killed by a bijection, so `w ∈ Z^G ∩ P[G] = Z[G]`.
  - `Z` is abelian, and its subquotients `F_p^n` have `p ∈ P(V)` and `p^n <= |V|`. So Proposition 2.1 makes `L|_Z`
    bijective.
  - Lemma 0.3(b) then makes `L|_P` bijective.
- **Assembly.** Lemma 0.3(b), upward along the derived series, makes `L` bijective.
- **Unconditional case.** If `V` has no abelian composition factor, then `P(V)` is empty. □

## 5. Consequences

**Corollary 5.1 (homomorphic dual surjunctivity is stable finiteness).** For every group `G` the following are
equivalent.
- (a) Every post-surjective homomorphic automaton over every finite group alphabet is pre-injective.
- (b) Every post-surjective `F_p`-linear automaton on every `(F_p^n)^G` is pre-injective.
- (c) `F_p[G]` is stably finite for every prime `p`.

*Proof.* (a) ⇒ (b) is trivial. (b) ⇒ (c) is Lemma 1.2. (c) ⇒ (a) is Theorem 4.2. □

Together with part 3 of `homomorphic-group-alphabet-ca-reduce-to-stable-finiteness`, the homomorphic sector of
Gottschalk and the homomorphic sector of Capobianco–Kari–Taati dual surjunctivity hold at exactly the same groups.
Both are unconditional for alphabets with no abelian composition factor.

**Corollary 5.2 (affine covers with one-point lifts have full domain).** Give the finite alphabet `A` any group
structure `V`. Let `F(x) = L(x) c` be an affine automaton, with `L` homomorphic and `c ∈ V^G` constant.
- Every equivariant continuous map `V^G -> V^G` that preserves the heap operation `x y^(-1) z` has this form, with
  `c = F(e)` constant because `e` is shift-fixed.

Let `X ⊆ V^G` be any closed set, not necessarily shift-invariant or of finite type. Suppose some `x_0 ∈ X` has lifts
in `X`: every `y` asymptotic to `F(x_0)` equals `F(x)` for some `x ∈ X` asymptotic to `x_0`. Under the hypothesis of
Theorem 4.2 (vacuous if `V` has no abelian composition factor), `X = V^G` and `F` is bijective.

*Proof.*
- **`L` is onto `V[G]`.** Let `v ∈ V[G]`. Then `y = L(x_0) v c` agrees with `F(x_0)` wherever `v = e`, so it is
  asymptotic to `F(x_0)`.
  - Choose a lift `x ∈ X` asymptotic to `x_0`, and put `w = x_0^(-1) x ∈ V[G]`.
  - `F(x) = L(x_0) L(w) c = y` gives `L(w) = v`.
- **`L` is bijective** by Theorem 4.2.
- **`X` is full.** For each `w ∈ V[G]`, apply the lift to `v = L(w)`. The lift is `x_0 w'` with `L(w') = L(w)`,
  so `w' = w` and `x_0 w ∈ X`.
  - `x_0 V[G]` is dense in `V^G`, and `X` is closed, so `X = V^G`.
- `F = L(.) c` is then a composition of bijections. □

## 6. What this kills in the Gottschalk cone, and what it does not

- **`every-group-is-dual-surjunctive`.** A counterexample cannot be affine for any group structure on the alphabet
  at a group where the `F_p[G]` are stably finite. Over alphabets with no abelian composition factor it cannot be
  affine at any group. A counterexample at a group whose `F_p[G]` are stably finite must be nonaffine for every
  group structure on `A`.
- **`constant-point-sft-domains-admit-no-post-surjective-covers` (CP).** Corollary 5.2 settles its affine sector
  under the same hypothesis, and more: arbitrary closed domains, lifts required at one point only, and no constant
  point needed.
  - Conversely, the linear counterexample recorded under "How it can fail" in that claim shows the affine sector of
    CP at `G` forces stable finiteness of every `F_q[G]`.
  - So the affine sector of CP is exactly stable finiteness. This extends, from `R^k` over a finite commutative
    ring to every finite group alphabet, the affine-decoder statement of the bus lemma of `swarm-0917-w18-w18-gs-pull`,
    which is unlanded on main at the time of writing.
- **Strict pairs.** For a strict pair `(tau, sigma)` with `sigma ∘ tau = id`, take `X = tau(A^G)`, which is closed
  and proper.
  - If `sigma` is affine for some group structure on `A` and has lifts inside `X` at a single point, Corollary 5.2
    gives `X = A^G`, so `tau` is surjective, a contradiction.
  - So the decoders sought by `strict-pairs-admit-post-surjective-decoders` are never affine at such `G`.
- **The invariant and the dying step.**
  - The invariant is a group structure on the alphabet for which the decoder is a heap morphism.
  - The dying step is "lifts at one point ⇒ `L` onto `V[G]` ⇒ (Theorem 4.2) `L` bijective ⇒ domain dense".
  - Any approach producing covers from linear or homomorphic data dies at stable finiteness, and over alphabets
    without abelian composition factors it dies at every group.
- **Not covered.**
  - Decoders that are homomorphic only on a sub-alphabet, or only on a subshift.
  - Decoders affine for a quasigroup or loop structure.
  - Nonlinear decoders in general.
  - In the injective direction, Phung's weak surjunctivity plays the same role. No group is made surjunctive or
    dual surjunctive by this note.
- **Novelty.**
  - No novelty is claimed for Lemma 1.1, Lemma 1.2 or Proposition 2.1. The linear dual statement is elementary and
    is likely in the literature, e.g. in Phung's work on dual surjunctivity; that is not pinned here.
  - The nonabelian parts are the new content here: Proposition 3.2 and Theorem 4.2 with no hypothesis on `G` for
    alphabets without abelian composition factors, and Corollary 5.2 over group alphabets.
