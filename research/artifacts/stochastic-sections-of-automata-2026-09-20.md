# Stochastic sections of cellular automata

Research audit dated **2026-09-20** (swarm wave 22, belief breaker for
`gottschalk-surjunctivity-conjecture`). Exact check script:
`experiments/markov-section-2026-09-17/check_markov_section.py`.

## 0. Setting and notation

`G` is a group, `A` a finite alphabet, `X = A^G` with the product topology,
and `G` acts by left shifts `(h.x)_g = x_{h^{-1} g}`. For a continuous map
`phi : X -> X` the Koopman operator is `phi^* f = f o phi` on `C(X)`.

A **Markov operator** on `C(X)` is a linear map `T` with `T 1 = 1` and
`T f >= 0` whenever `f >= 0`. It is **equivariant** when
`T(f o h^{-1}) = (T f) o h^{-1}` for all `h` in `G`. Equivalently (Riesz),
`T f (y) = int f d mu_y` for a weak-* continuous, shift-equivariant family
of probability measures `y -> mu_y`, a Feller kernel. `Mark(G, A)` is the
monoid of equivariant Markov operators under composition.

Koopman operators of cellular automata lie in `Mark(G, A)`. By Gelfand
duality and Curtis–Hedlund–Lyndon they are exactly the elements of
`Mark(G, A)` that are multiplicative.

A strict pair is `(tau, sigma)` with `sigma o tau = id` and `tau` not onto.
In Koopman form this is `tau^* sigma^* = 1` and `sigma^* tau^* != 1`. Here
`tau` is the *encoder* and `sigma` the *decoder*.

## 1. The counterexample on every group with an element of infinite order

Fix `s` in `G` of infinite order and `n >= 2`. Put `A = Z/n` and define

```text
sigma(x)_g = x_g - x_{g s}        (memory {1, s}).
```

Here `sigma` is a continuous group endomorphism of the compact group `X`. It
commutes with left shifts because the memory acts by right multiplication.

**(a) sigma is onto.** The left cosets `g<s>` partition `G`, and each is a
bi-infinite line `h s^k`, `k` in `Z`, because `s` has infinite order. Given
`y`, choose a representative `h` of each coset and put `x_h = 0`. Then solve
`x_{h s^{k+1}} = x_{h s^k} - y_{h s^k}` in both directions.

**(b) The fibres are cosets of an infinite compact kernel.** The kernel is

```text
K = { x : x_{g s} = x_g for all g },
```

the configurations that are constant on every left coset `g<s>`. It is a
closed subgroup, isomorphic to `(Z/n)^{G/<s>}` and nontrivial (it contains
the constants), so `sigma` is not injective. `K` is invariant under left
shifts, since `(h.x)_{gs} = x_{h^{-1} g s} = x_{h^{-1} g}`. Let `m` be
normalized Haar measure on `K`. Every shift acts on `K` as a topological
group automorphism, so it preserves `m` by uniqueness of Haar measure.

**(c) The fibre-averaging operator.** For `f` in `C(X)` and `y` in `X`, put

```text
(T f)(y) = int_K f(x_y + k) dm(k),       where sigma(x_y) = y.
```

This is well defined, because the fibre `sigma^{-1}(y)` is exactly the coset
`x_y + K` and `m` is translation invariant.

**(d) Window lemma: T is Feller and preserves locally constant functions.**
Let `f(x) = f_0(x|W)` for a finite `W` in `G`. The restriction `k -> k|W`
pushes `m` to Haar measure on the finite group `K_W = {k|W : k in K}`, so

```text
(T f)(y) = |K_W|^{-1} sum_{kappa in K_W} f_0(x_y|W + kappa).
```

`K_W` is the product, over the cosets `C = h<s>` meeting `W`, of the
diagonal constants on `W cap C`. So `x_y|W mod K_W` is determined by the
differences inside each `W cap C = {h s^{k_1}, ..., h s^{k_r}}`, where
`k_1 < ... < k_r`. These differences are

```text
x_{h s^{k_i}} - x_{h s^{k_{i+1}}} = sum_{j = k_i}^{k_{i+1} - 1} y_{h s^j}.
```

Hence `T f` depends only on `y` restricted to the finite set
`W' = union_C {h s^j : k_1 <= j < k_r}`, and it takes values in
`Z[1/n]`-combinations of the values of `f`. For general `f` in `C(X)`,
`|T f - T f_j| <= ||f - f_j||_inf` for locally constant `f_j -> f`, so
`T f` is a uniform limit of continuous functions and is continuous.

For `G = Z` and `s = 1`, `W = [a, b]` gives `W' contained in [a, b-1]`, so
`T` has finite propagation in the strongest (window-shrinking) sense. For a
general `G`, `W'` stays inside `W <s>`, but its size can depend on the
distortion of `<s>`.

**(e) T is an equivariant Markov operator.** `T 1 = 1` and positivity are
immediate from the formula. For equivariance, `sigma(h.x) = h.sigma(x)`
gives `sigma^{-1}(h.y) = h.x_y + K = h.(x_y + K)`, and the shift acts on `K`
preserving `m`, so `T(f o h^{-1})(h.y) = (T f)(y)`.

**(f) T sigma^* = 1.** `T(f o sigma)(y) = int_K f(sigma(x_y + k)) dm = f(y)`.

**(g) sigma^* T != 1.** `(sigma^* T f)(x) = int_K f(x + k) dm(k) =: (P f)(x)`
is the Haar average over `K`. For `f = [x_1 = 0]`, the coordinate `k_1` is
uniform on `Z/n` (`K` contains the constants), so `P f = 1/n`
identically and `P f != f`. So `P = sigma^* T` is a nontrivial idempotent
Markov operator. It is the conditional expectation onto the `K`-invariant
functions, which are exactly the image of `sigma^*`.

**(h) Haar preservation and faithfulness.** Let `lambda` be the uniform
Bernoulli (Haar) measure on `X`. `sigma` is a surjective continuous
homomorphism, so `sigma_* lambda = lambda`. Then

```text
int T f dlambda = int (T f) o sigma dlambda = int P f dlambda = int f dlambda,
```

by translation invariance of `lambda`. So `T` is doubly stochastic for the
uniform Bernoulli measure, as is `sigma^*`. `T` is also faithful on
positive functions: if `f >= 0` and `T f = 0`, then `f` vanishes on every
fibre, and the fibres cover `X` because `sigma` is onto.

**Theorem 1.** Let `G` contain an element of infinite order and `n >= 2`.
There are a surjective, non-injective linear cellular automaton `sigma` on
`(Z/n)^G` and an element `T` of `Mark(G, Z/n)` such that:

- `T sigma^* = 1` and `sigma^* T != 1`;
- `T` is faithful and preserves the uniform Bernoulli measure;
- `T` maps locally constant `Z[1/n]`-valued functions to such functions;
- for `G = Z`, `T` has window-shrinking finite propagation.

In particular `Mark(G, A)` is not directly finite for every `|A| >= 2`,
including on `G = Z`, where every cellular automaton monoid is directly
finite. For `|A| = n` the construction is used directly. The exact script
checks (c)–(h) on windows of length at most 5 for `n = 2, 3, 4` on `Z`, and
on a 2x2 window of `Z^2` with `s = (1, 0)`.

## 2. Which side may be relaxed

The Gottschalk identity `tau^* sigma^* = 1` has the encoder's Koopman
operator on the left. In Theorem 1 the Markov element `T` sits in the
encoder slot and the Koopman operator of the (surjective) decoder `sigma`
sits on the right. The two one-sided relaxations behave in opposite ways.

**Proposition 2 (decoder relaxation is equivalent to the goal).** For a group
`G` and an alphabet `A`, the following are equivalent.

1. `G` is surjunctive on `A`.
2. For every cellular automaton `tau` and every `T` in `Mark(G, A)`,
   `tau^* T = 1` implies `T tau^* = 1`.

*Proof.* (1 => 2) Suppose `tau^* T = 1`. Then `tau^*` is onto `C(X)`. If
`tau(x) = tau(x')`, every function `f o tau` agrees at `x` and `x'`. These
functions are all of `C(X)`, which separates points, so `x = x'` and `tau`
is injective. By (1) `tau` is a bijective automaton, hence a homeomorphism,
so `tau^*` is invertible and `T = (tau^*)^{-1}`.

(2 => 1) Let `tau` be injective. Node
`surjunctivity-iff-automaton-monoid-directly-finite` extends the continuous
inverse on the image to an automaton `sigma` with `sigma o tau = id`. Then
`T = sigma^*` is in `Mark(G, A)` and `tau^* T = (sigma o tau)^* = 1`, so (2)
gives `(tau o sigma)^* = 1`. Evaluating on point-separating functions gives
`tau o sigma = id`, so `tau` is onto. QED

**Proposition 3 (encoder relaxation is false on Z).** The statement "for
every automaton `sigma` and every `T` in `Mark(G, A)`, `T sigma^* = 1`
implies `sigma^* T = 1`" fails for every `G` with an element of infinite
order and every `|A| >= 2`, by Theorem 1. It fails even when `T` is faithful,
Bernoulli-preserving and of finite propagation (on `Z`).

In words: an automaton with a deterministic equivariant continuous section
is injective exactly when Gottschalk holds. An automaton with a *stochastic*
equivariant continuous section, even a faithful measure-preserving local
one, need not be injective, already on `Z`.

## 3. The class this kills

**Invariant.** Call a proof of surjunctivity *Markov-functorial* if every step
is valid for the pair `(phi, psi) = (tau^*, sigma^*)` as elements of
`Mark(G, A)`, that is, it uses only these properties:

- linearity, positivity, unitality and shift-equivariance;
- continuity, locality or finite propagation, and faithfulness;
- preservation of the uniform Bernoulli measure;
- multiplicativity of the decoder side `psi` only.

It must not use multiplicativity of the encoder side `phi`. Such a proof
would show `phi psi = 1 => psi phi = 1` in `Mark(Z, Z/2)` for the pair
`(T, xor^*)` of Theorem 1, which is false.

**Where every member dies.** It dies at the single step
`phi psi = 1 => psi phi = 1`, on `G = Z`, `A = Z/2`, `phi = T` (average over
the two preimages `x`, `x + 1^Z`) and `psi = xor^*`. Consequences:

1. **K_0 form.** In any ring `R` containing `Mark(G, A)` multiplicatively,
   `1 - P` with `P = xor^* T` is a nonzero idempotent. `P` is Murray–von
   Neumann equivalent to `1` (`P = psi phi`, `phi psi = 1`), so `[1 - P] = 0`
   in `K_0(R)`. So no faithful trace, rank function or dimension function on
   such an `R` exists. This sharpens node
   `directly-finite-ring-images-of-ca-monoids-kill-retracts`. There, the
   pullback representation on `C(A^G, k)` fails because its target is
   `End_k` of an infinite-dimensional space. Here the failure persists
   inside the smallest positive, equivariant, local, measure-preserving hull
   of the Koopman image, on `Z`.
2. **UCP recovery (quantum audit 2026-09-12, Section 5).** That audit derives,
   from UCP maps `phi psi = id`, that `psi(Q_G)` lies in the multiplicative
   domain of `phi`. It remarks that `psi` is not shown to be multiplicative,
   and that faithfulness of `phi` would remove the multiplicative defects.
   The diagonal commutative model `(T, xor^*)` has `psi` multiplicative and
   `phi` faithful, local, equivariant, unital and Bernoulli-preserving, and
   still `psi phi != id`. So no strengthening of the recovery data on the
   decoder side (multiplicativity of `psi`, faithfulness of `phi`) can yield
   surjectivity. The remaining input must be multiplicativity of the encoder
   side, which for Koopman operators is determinism of `tau`.
3. **Measure-lifting arguments.** The dual of `T` is a shift-equivariant,
   weak-* continuous, affine map `T'` on probability measures with
   `sigma_* T' = id`, `T' lambda = lambda`, and `T'` sending invariant
   measures to invariant measures. Any argument that deduces injectivity of
   a decoder from the existence of such an equivariant continuous measure
   lift is refuted on `Z`. This covers entropy bookkeeping along the lift:
   the lift has zero fibre entropy per site, since the fibre is one global
   `Z/n` coin.
4. **Local randomness does not rescue it on Z.** On `Z`, a lift
   produced by a probabilistic cellular automaton with independent local
   randomness is finitely dependent. For `xor` the two points of a fibre
   differ at every site, so the output bits at `0` and at a distant site `N`
   would be both independent and perfectly correlated given `y`. So the lift
   is deterministic and `sigma` has a CA section, which on `Z` forces
   bijectivity. The global coin is therefore essential. This separates
   *PCA-functorial* arguments, which are not killed here, from
   *Markov-functorial* ones.

   Precisely: if a PCA with independent local randomness gave a lift of
   `xor`, then for fixed `y` the bits `X_0` and `X_N`, for large `N`, would
   be independent, and `X_N = X_0 + sum_{0 <= j < N} y_j` would be a
   bijective function of `X_0`. So `X_0` would be almost surely constant.
   The lift would be a CA section `tau` with `xor o tau = id`, and `tau`
   would be injective, hence bijective on `Z`, so `xor` would be injective.
   It is not. This is a remark about this example only. Whether the
   monoid of PCA operators is directly finite on `Z` is not decided here.

## 4. Limits

- **Torsion groups.** The construction needs a surjective, non-injective
  automaton whose fibres carry an equivariant continuous choice of
  probability measure. On a locally finite group every surjective automaton
  is injective: with memory in a finite subgroup `H`, the map is a product
  over the cosets `gH` of one map `A^H -> A^H`. So no example of this shape
  exists there. For infinite finitely generated torsion groups the question
  is open here.
- **Integral coefficients.** `T` needs `1/n`. Whether the ring of
  equivariant `Z`-linear operators on `LC(X, Z)` admits a left inverse of
  `xor^*` is not decided. A left inverse that is itself a Koopman operator
  is impossible on `Z`, by the argument in item 4.
- **No new nonsurjunctive group.** Theorem 1 is a class-killing obstruction.
  It shows that a surjunctivity proof must use determinism (multiplicativity)
  of the encoder. It says nothing about the truth of the goal, which stays
  OPEN (its candidate refutations are OPEN claims).
