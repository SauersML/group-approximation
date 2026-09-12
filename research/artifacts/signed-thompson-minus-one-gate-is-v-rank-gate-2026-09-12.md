# The minus-one gate of the signed Thompson group is the rank gate of V

Lane `w5-c3-signed-thompson`, 2026-09-12. Question: does the signed Thompson group
`H = E ⋊ V <= G_3 = L_(F_3)(1,2)^x` carry a characteristic-three rank function, or rank model, moving
`z = -1`? Answer: exactly when Thompson's group `V` itself carries a non-augmentation rank function.
So the `E ⋊ V` route to the characteristic-three gate is the rank gate of `V`, and an obstruction on
`E ⋊ V` would prove `V` nonsofic.

**Axioms used.** Everything in Sections 1–2 uses only the Sylvester matrix rank function axioms, the
simplicity of `V`, and the transitivity of `V` on proper nonempty clopens. There are no eigenvalues,
no rounding, no dimension counts and no ultraproducts. Section 3 flags the one extra step, compression
to the minus-one corner, which needs `char K != 2`.

## 0. Setup

- `X = {0,1}^N`. `V` acts on `X` by prefix replacements.
- `E = {tau_C = 1 - 2 P_C : C clopen} ~= C(X, F_2)`, with `tau_C tau_D = tau_(C triangle D)`,
  `tau_X = z` and `g tau_C g^-1 = tau_(gC)` for `g in V`. `E cap V = 1`, and `H = E ⋊ V`
  (`signed-thompson-algebra-is-odd-measure-crossed-product`).
- `w = s0 t1 + s1 t0 in V` swaps `[0]` and `[1]`, and `d = s0 t0 - s1 t1 = tau_[1] in E`. So `H`
  contains `z`, `w` and `d`.
- A **Sylvester matrix rank function** `rk` on a `K`-algebra `A` satisfies `rk(1) = 1`,
  `rk(X ⊕ Y) = rk X + rk Y`, `rk(XY) <= min(rk X, rk Y)` and `rk [[X, Z], [0, Y]] >= rk X + rk Y`.
  - **Consequences used:** `rk(a + b) <= rk a + rk b`; `rk(u a u') = rk a` for units `u, u'`;
    `rk(e + f) = rk e + rk f` for orthogonal idempotents.
  - **Pullback:** if `phi : A -> B` is a unital ring map and `rk` is a Sylvester matrix rank function
    on `B`, then `rk ∘ phi` (applied entrywise to matrices) is one on `A`.
- For a group `Γ` and `rk` on `K[Γ]`, put `N_rk = {x in Γ : rk(1 - [x]) = 0}`.
  - It is a normal subgroup: `1 - [xy] = (1 - [x]) + [x](1 - [y])` and
    `1 - [g x g^-1] = [g](1 - [x])[g^-1]`.
  - `rk` is the augmentation rank iff `N_rk = Γ` (`simple-group-rank-functions-are-augmentation-or-detecting`).

## 1. The signed group inside V

Write points of `X' = {0,1}^N` as `ε x` with `ε in {0,1}` and `x in X`. Let `V'` be Thompson's group
of `X'`, so `V' ~= V`. Let `σ_0 in V'` be the first-letter swap `ε x -> (1 - ε) x`, a fixed-point-free
involution.

Define `phi` on generators of `H`:
- `phi(tau_C)(ε x) = (ε + 1_C(x)) x`;
- `phi(g)(ε x) = ε (g x)` for `g in V`.

**Lemma 1.1.** `phi` extends to an injective homomorphism `H -> V'` with `phi(z) = σ_0`. Its image is
the centralizer `C_(V')(σ_0)`.

*Proof.*
1. **Prefix replacements.** Refine `C` into cylinders `[β]`. On `[ε β]`, `phi(tau_C)` is the prefix
   replacement `ε β y -> (ε + c) β y` with `c = 1_C` on `[β]`. If `g` sends `β_i y -> α_i y`, then
   `phi(g)` sends `ε β_i y -> ε α_i y`. So both land in `V'`.
2. **Relations.** `phi(tau_C) phi(tau_D) = phi(tau_(C triangle D))`, and `phi` is multiplicative on `V`.
   For the action, `phi(g) phi(tau_C) phi(g)^-1 (ε x) = (ε + 1_C(g^-1 x)) x = phi(tau_(gC))(ε x)`.
   `H` is the internal semidirect product of `E` by `V`, so these define a homomorphism.
3. **`z` and injectivity.** `phi(z) = phi(tau_X) = σ_0`. If `phi(tau_C g) = id`, the `x`-coordinate
   forces `g = 1`, and then `C = ∅`.
4. **Image.** Each `phi(h)` commutes with `σ_0`. Conversely, a prefix replacement commuting with `σ_0`
   sends `[ε β]` to `[ε' α]` with `ε' - ε` independent of `ε`. So it equals `phi(tau_C g)`, where `g`
   is `β -> α` and `C` collects the cylinders where the first letter flips. ∎

Only parts 1–3 are used below.

**Lemma 1.2 (transitivity).** For proper nonempty clopens `A, B <= X` there is `g in V` with `gA = B`.

*Proof.* Write `A`, `X \ A`, `B`, `X \ B` as disjoint unions of `a`, `a'`, `b`, `b'` cylinders.
Splitting one cylinder into its two children raises a count by one, so we may take `a = b` and
`a' = b'`. The prefix replacement matching cylinders of `A` to those of `B`, and of `X \ A` to those
of `X \ B`, lies in `V`. ∎

## 2. The theorem

**Theorem 2.1.** Let `K` be any field. The following are equivalent.
1. `K[H]` carries a Sylvester matrix rank function with `rk(1 - [z]) > 0`.
2. `K[V]` carries a Sylvester matrix rank function other than the augmentation rank.
3. `K[V]` carries a Sylvester matrix rank function with `rk(1 - [g]) > 0` for every `g != 1`.

(1) ⟹ (2) is restriction to the unsigned subgroup `V <= H`. (3) ⟹ (1) is pullback along `phi`.

*Proof.*
- **(2) ⟺ (3).** `N_rk cap V` is normal in `V`, and `V` is simple
  (`thompson-v-finitely-presented-infinite-simple`). So it is `V`, which is (2) failing, or `1`, which is (3).
- **(1) ⟹ (2).** Let `rk` on `K[H]` have `rk(1 - [z]) > 0`, and suppose its restriction to `K[V]` is the
  augmentation rank, that is `V <= N := N_rk`.
  - **Clopens collapse to one class.** For `g in V` and any `tau`, `g tau g^-1 tau^-1 = g · (tau g^-1 tau^-1)`
    lies in `N`, since `N` is normal and contains `g`. So `tau_(gA) ≡ tau_A mod N`. By Lemma 1.2,
    `tau_A ≡ tau_B mod N` for all proper nonempty clopens `A, B`. Call the common class `c`.
  - **The class is trivial.** Take `A = [00]` and `B = [01]`. Then `tau_[0] = tau_A tau_B`, so `c = c^2`, and
    `c = 1`. So every `tau_A` with `A` proper lies in `N`.
  - **Contradiction.** `z = tau_X = tau_[0] tau_[1] in N`, so `rk(1 - [z]) = 0`.
- **(3) ⟹ (1).** Carry `rk` to `K[V']` along `V ~= V'`. Since `σ_0 != 1`, `rk(1 - [σ_0]) > 0`. The algebra map
  `phi_K : K[H] -> K[V']` is unital, so `rk ∘ phi_K` is a Sylvester matrix rank function on `K[H]`, and
  `rk(phi_K(1 - [z])) = rk(1 - [σ_0]) > 0`. ∎

**Axiom audit.** The rank-function steps are subadditivity, the product bound, unit invariance and
pullback along a unital ring map. The group-theory inputs are simplicity of `V`, Lemma 1.2 and Lemma 1.1
parts 1–3. Nothing matricial is used, and `K` can be any field.

## 3. Matricial and anti-central forms

**Corollary 3.1 (models).** Let `𝒜` be any class of target algebras with Sylvester rank functions positive
on nonzero elements that is closed under renormalized corners. For example: rank ultraproducts of matrix
algebras over fields of characteristic three, or abstract rank algebras modulo their null ideal.
Then `H` has a homomorphism into the units of some `M in 𝒜` moving `z` iff `V` has a nontrivial one.

*Proof.* Restriction and pullback along `phi` preserve the class. For (1) ⟹ (2), apply the argument of
Theorem 2.1 to `rk ∘ σ`, which is positive on `1 - σ(x)` exactly when `σ(x) != 1`. ∎

**Anti-central form** (needs `char K != 2`). A model `σ` moving `z` has the central idempotent
`f = (1 - σ(z))/2` of its image, with `rk(f) = rk(1 - σ(z)) > 0` because `σ(z)^2 = 1`. The renormalized
corner `fMf` gives a model with `z -> -1`. This is the same step as `ternary-leavitt-rank-models-move-z-proof`.
It is algebraic, not an eigenvalue argument.

## 4. Consequences

**4.1. The `E ⋊ V` gate is the `V` gate.** "Every Sylvester matrix rank function on `F_3[H]` kills `1 - [z]`"
is equivalent to `thompson-v-ternary-rank-functions-are-augmentation`: every Sylvester matrix rank function on
`F_3[V]` is the augmentation rank.

**4.2. An obstruction on `H` proves `V` nonsofic.**
- **Sofic gives a detecting rank function.** Suppose `V` is sofic. Permutation matrices of a sofic
  approximation, read over `F_3` in a rank ultraproduct, give a rank function detecting `V`: a permutation
  moving `m` of `n` points has `rank(P - I) >= m/2`.
- **So an obstruction on `H` does three things at once.** It proves `F_3[V]` carries only the augmentation
  rank, which is stronger than `V` failing to be sofic or `F_3`-linear sofic. It makes `V` not sofic
  (`thompson-v-is-sofic`, OPEN). And it can use nothing beyond this.
- **The verified laws cannot decide it by themselves.** The Haar law, the lifted-trace law on finite subgroups,
  uniform displacement and the trivial-plus-regular torsion law are theorems about every model. A
  contradiction derived from them inside `H` is exactly a proof of this nonsoficity statement.

**4.3. For `G_3`.** Restricting from `F_3[G_3]` to `F_3[H]` keeps `rk(1 - [z]) > 0`.
- **One direction.** `thompson-v-ternary-rank-functions-are-augmentation` implies
  `sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one`, by route
  `ternary-units-kill-minus-one-via-thompson-v-augmentation`.
- **The converse is not known.** A rank function on `F_3[V]` need not extend to `F_3[G_3]`.
- **What a proof for `G_3` must use.** A "No" proof for `G_3` that does not settle `V` must use elements of
  `G_3` outside `H`: the Hadamard unit `h`, root elements `x_12(r)`, compressors, or the `SD16` and `GL_2(F_3)`
  blocks, which are not conjugate into `H` (`anti-central-k0-states-can-be-chosen-transpose-invariant`).

**4.4. Corner witnesses inside `H`.** Suppose `F_3[V]` carries a non-augmentation rank function, for example
because `V` is sofic. Let `rk' = rk ∘ phi` on `F_3[H]`, so `rk'(1 - [z]) > 0`.
- **No corner witness in `H`.** No `b, c in eps_- F_3[H]` satisfy `c e_- b = eps_-`. This is
  `anti-central-rank-models-kill-ternary-corner-witnesses` with `Γ = H`, which contains `z`, `w` and `d`. The
  model is `F_3[H]` modulo the null ideal of `rk'`, whose rank is positive on nonzero elements.
- **The crossed-product target fails.** `odd-measure-crossed-product-unit-below-cylinder-idempotent` is false.
  - On `B = F_3[H] eps_-`, put `N(X) = rk'(eps_- X)/rk'(eps_-)`.
  - The swap `w` conjugates `q_[0]` to `q_[1]`, and `q_[0] + q_[1] = eps_-` is an orthogonal sum, because odd
    measures give exactly one of `[0]`, `[1]` measure one. So `N(q_[0]) = 1/2`.
  - Then `c' q_[0] b' = eps_-` would force `1 = N(eps_-) <= N(q_[0]) = 1/2`. This is w3-corner-crossed's
    argument (4647e9e53f).
- **Conversely.** A solution of the crossed-product target, or any corner witness supported in `H`, proves
  that `F_3[V]` carries only the augmentation rank, so `V` is not sofic.

## 5. Where it stops

- **Task 1, an obstruction.** By 4.2, combining the Haar law with depth-changing elements of `V` can succeed
  only by proving that `F_3[V]` has no non-augmentation Sylvester rank function. That is at least as strong as
  `V` being nonsofic, which is open. I found no such argument.
- **Task 2, a construction.** It is equivalent to a non-augmentation Sylvester rank function on `F_3[V]`.
  - **What fails:** `V` has no nontrivial finite-dimensional representation. Permutation-type models are sofic
    approximations, which is open. `V` is not inside the level unit group `L`, since its depth-changing elements
    are not level elements.
  - **HNN models don't reach it:** single-letter HNN relations (`level-unit-hnn-extensions-have-anti-central-rank-models`)
    do not carry `V`'s multiplication table on depth-changing elements.
- **Scope of the V-gate tools on main (for `w4-upg-audit`; my reading, not re-derived):**
  - probably abstract, using only additivity of rank on orthogonal idempotents, subadditivity and conjugation
    invariance: the covariance obstruction, uniform displacement and the trivial-plus-regular torsion law;
  - matricial, because it works at finite symmetric-group stages: the symmetric-group stage theorem.
- **Characteristic.** Theorem 2.1 holds over every field. The anti-central compression needs `char K != 2`.
  In characteristic two the same argument relates `C(X,F_2) ⋊ V` to `thompson-v-has-no-nontrivial-f2-rank-model`.
