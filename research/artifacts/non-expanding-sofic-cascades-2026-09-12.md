# Cascades of sofic-window codes: measure rigidity, and why stages that never enlarge the alphabet never compress

Lane `w4-measurable-2`, 2026-09-12. Supports `injective-same-alphabet-sofic-codes-preserve-uniform-measure`
and records the multi-stage regime of `measurable-alphabet-compression-over-leavitt-units` left open by
`single-maximal-stage-routed-codes-cannot-compress` (artifact `defect-coupled-routed-codes-2026-09-12.md`,
Section 5).

## 0. Setting

Notation as in `research/artifacts/measurable-alphabet-compression-2026-09-12.md`, Section 0: left shift
`(h.x)(g) = x(h^-1 g)`, `mu_A` the uniform product measure on `A^G`. A *code* is a Borel `G`-equivariant map
between full shifts. It is *a.e.-injective* if it is injective on a conull Borel set. A code has *window in*
`K <= G` if `S(x)(g) = f((g^-1.x)|_K)` for a Borel `f`, so `S(x)(g)` reads `x` on the left coset `gK`.
Write `q = |A|`, `h_2` for the binary entropy function, and `H` for Shannon entropy.

The open regime (defect-coupled artifact, Section 5): a composite of several combining stages along different
sofic subgroups whose windows together generate a nonsofic group. After the first stage the measure is not
known to be Bernoulli, so descent cannot be applied stage by stage. Section 2 supplies the missing step for
stages that do not enlarge the alphabet: their output is again uniform Bernoulli.

## 1. Two counting inequalities

**Fano.** If `X` takes at most `q` values and `P(X != phi(Y)) <= eta`, then `H(X | Y) <= h_2(eta) + eta log q`.

**Shearer.** Let `(X_v)_(v in V)` be random variables on a finite set `V`, and let `S_1, ..., S_m` be subsets
of `V` covering every point at least `k` times. Then `H(X_V) <= (1/k) sum_i H(X_(S_i))`.

*Proof (standard, recorded for completeness).* Order `V`. For each `i`,
`H(X_(S_i)) = sum_(v in S_i) H(X_v | X_(S_i ∩ {<v})) >= sum_(v in S_i) H(X_v | X_({<v}))`, since conditioning
on more variables does not increase entropy. Sum over `i`. Each `v` occurs in at least `k` sums and every
term is nonnegative, so `sum_i H(X_(S_i)) >= k sum_v H(X_v | X_({<v})) = k H(X_V)`. QED

**Sofic models, as right actions.** Let `K` be countable and sofic, `Q ⊆ K` finite with `1 in Q`, and
`eta > 0`. Composing a sofic approximation with inversion gives a finite set `V` and permutations
`v -> v.q` of `V` for `q in Q`, such that at least `(1 - eta)|V|` points `v` are *good*: `q -> v.q` is
injective on `Q`, and `(v.q).q' = v.(qq')` whenever `q, q', qq'` lie in `Q`.

## 2. Lemma 1: measure rigidity for equal-alphabet codes over sofic groups

**Lemma 1.** Let `K` be a countable sofic group, `A, B` finite, and `S: A^K -> B^K` an a.e.-injective code.
Then

1. `|B| >= |A|`;
2. if `|B| = |A|`, then `S_* mu_A = mu_B`.

Part 1 is Rokhlin-maximality of sofic groups, already a consequence of
`sofic-radical-localizes-bernoulli-deficit-witnesses`. It is re-derived below along the way. Part 2 is the new
content. For a continuous injective automaton it follows from Gromov–Weiss bijectivity and
`bijective-ca-preserve-uniform-bernoulli-measure`. Here `S` is only Borel and injective on a conull set.

*Proof.*

**Step 1 (finite-window encoder and decoder).** Equivariance gives `S(x)(k) = s(k^-1.x)` with
`s(x) = S(x)(1)`. Let `X_0` be a conull Borel set on which `S` is injective. By Lusin–Souslin, `S(X_0)` is Borel
and the inverse on it is Borel, so there is a Borel `d: B^K -> A` with `x(1) = d(S(x))` for `mu_A`-almost
every `x`.

Fix `eps > 0`. Cylinder functions are dense in measure, so:

* there are a finite `D ⊆ K` and `d_eps: B^D -> A` with `mu_A(x(1) != d_eps(S(x)|_D)) < eps`;
* then there are a finite `W ⊆ K` and `s_eps: A^W -> B` with `mu_A(s(x) != s_eps(x|_W)) < eps/(|D| + 1)`.

Put `S_eps(x)(k) = s_eps((k^-1.x)|_W)`, which reads `x` on `kW`, since `(k^-1.x)(w) = x(kw)`. The measure is
invariant, so `mu_A(S(x)(k) != S_eps(x)(k)) < eps/(|D|+1)` for every `k`. Hence

    (1.1)  mu_A( x(1) != d_eps(S_eps(x)|_D) ) < 2 eps,
    (1.2)  mu_A( S(x)(k) != S_eps(x)(k) ) < eps   for every k in K.

**Step 2 (the deficit to contradict).** Suppose `|B| = |A| = q` and `S_* mu_A != mu_B`. Some cylinder marginal
differs, so there is a finite `F ⊆ K` with

    c := |F| log q - H(S(x)|_F) > 0,

because a law on `B^F` has entropy `|F| log q` exactly when it is uniform. Adding `1` to `F` does not decrease
`c`, since `H(y|_(F ∪ {1})) <= H(y|_F) + log q`. So take `1 in F`. `F` and `c` are fixed before `eps`.
Coordinatewise Fano with (1.2) gives

    (2.1)  H(S_eps(x)|_F) <= H(S(x)|_F) + sum_(f in F) H(S_eps(x)(f) | S(x)(f))
                          <= |F| log q - c + |F| delta'(eps),

with `delta'(eps) = h_2(eps) + eps log q`. Put `delta(eps) = h_2(2 eps) + 2 eps log |A|`. Both tend to `0`.

**Step 3 (count on a model).** Let `Q = {1} ∪ D ∪ W ∪ DW ∪ F ∪ FW`. Take a sofic model `(V, .)` for `Q` with good
fraction at least `1 - eta`. Let `x` be uniform on `A^V`, and define `y in B^V` at every point by

    y(v) = s_eps( (x(v.w))_(w in W) ).

*Laws at good points.* For good `v` and `d in D`, `y(v.d) = s_eps((x((v.d).w))_w) = s_eps((x(v.(dw)))_w)`. The
points `v.q` for `q in {1} ∪ DW` are distinct exactly when the corresponding elements of `K` are, and `x` is iid
uniform. So

    (3.1)  (x(v), (y(v.d))_(d in D))  has the law of  (x(1), (S_eps(x)(d))_(d in D))  in K,
    (3.2)  (y(v.f))_(f in F)          has the law of  S_eps(x)|_F                         in K.

*Lower bound.* `H(x) = |V| log |A|`, and `H(x) <= H(y) + sum_v H(x(v) | y)`. For good `v`, (1.1), (3.1) and Fano
give `H(x(v) | y) <= H(x(v) | (y(v.d))_d) <= delta(eps)`. For bad `v` the term is at most `log |A|`. So

    (3.3)  H(y) >= |V| ( log |A| - delta(eps) - eta log |A| ).

*Part 1.* `H(y) <= |V| log |B|`. Letting `eta -> 0`, then `eps -> 0`, gives `log |A| <= log |B|`.

*Upper bound for Part 2.* For `v in V` put `S_v = {v.f : f in F}`. Let `V'` be the set of points `u` such that,
for every `f in F`, the unique `v_f` with `v_f.f = u` is good. Each `v.f` is a permutation of `V`, so a bad
point spoils at most `|F|` points, and `|V \ V'| <= |F| eta |V|`.
For `u in V'` the points `v_f` are distinct: `v_f = v_(f')` would give `v.f = v.f'` at a good point, so `f = f'`.
So the sets `S_v ∩ V'` cover every point of `V'` at least `|F|` times. By Shearer and monotonicity,

    H(y|_(V')) <= (1/|F|) sum_(v in V) H(y|_(S_v)).

For good `v`, the chart is injective on `F`, and (3.2) with (2.1) gives
`H(y|_(S_v)) <= |F| log q - c + |F| delta'`. For bad `v` the bound is `|F| log q`. So

    H(y) <= H(y|_(V')) + |V \ V'| log q
         <= |V| ( log q - (1 - eta) c/|F| + delta'(eps) + |F| eta log q ).

*Conclusion.* Compare with (3.3), where `|A| = q`:

    (1 - eta) c/|F| <= delta(eps) + delta'(eps) + (|F| + 1) eta log q.

Let `eta -> 0` for fixed `eps`, then `eps -> 0`. This gives `c <= 0`, a contradiction. QED

**Remarks.**

* **What the proof uses.** Only good charts of the finite pattern `Q = {1} ∪ D ∪ W ∪ DW ∪ F ∪ FW` at most
  points of finite models, with the stated right-product consistency. Soficity of the whole of `K` is the
  convenient way to get them. This is the same locality as `sofic-radical-localizes-bernoulli-deficit-witnesses`,
  now also carrying the output law.
* **Rokhlin-maximality alone does not give Part 2 by this proof.** The Shearer step needs models on which the
  output law can be counted. Over a Rokhlin-maximal nonsofic window, Part 1 still holds by definition, and
  Part 2 is not claimed.
* **Coset lifting (used in Section 3).** Let `G` be countable, `K <= G` sofic, `|E'| = |E|`, and let
  `S(y)(g) = f((g^-1.y)|_K)` be a.e.-injective on `(E^G, mu_E)`. By `bernoulli-codes-descend-to-window-subgroup`,
  `S_K(z)(k) = f(k^-1.z)` is a.e.-injective on `E^K`, so `(S_K)_* mu_E = mu_(E')` by Part 2. The output on a left
  coset `gK` is `S_K` applied to `z_g(k) = y(gk)`, and inputs on distinct cosets are independent. So
  `S_* mu_E = mu_(E')` over `G`.

## 3. Theorem G: cascades that never enlarge the alphabet never compress

**Setting.** `G` is countable. A *cascade* is `tau = S_k o ... o S_1` with `S_i: E_(i-1)^G -> E_i^G`,
`E_0 = A` and `E_k = B`, where each stage has one of three types:

* **(R)** a routing code as in `measurable-certificate-routing-preserves-bernoulli-measure`, which keeps the
  alphabet;
* **(P)** a code with `|E_i| = |E_(i-1)|` that carries the uniform measure to the uniform measure, for example a
  bijective automaton (`bijective-ca-preserve-uniform-bernoulli-measure`);
* **(W)** a code whose window lies in a sofic subgroup `K_i <= G`.

The windows of different stages are arbitrary and may together generate any subgroup, including all of
`U = L_(F_2)(1,2)^x`. Every group is generated by its cyclic subgroups. Put `T_i = S_i o ... o S_1` and
`nu_i = (T_i)_* mu_A`.

**Theorem G.** Suppose `tau` is a.e.-injective. Then:

1. Let `j` be the first index with `|E_j| != |E_(j-1)|`. Then `nu_i = mu_(E_i)` for every `i < j`, `S_j` is a
   (W)-stage, and `|E_j| > |E_(j-1)|`.
2. If no stage enlarges the alphabet, then `|B| = |A|` and every `nu_i` is uniform. No such cascade compresses.
3. A (W)-stage that shrinks the alphabet never reads the uniform measure: if `|E_i| < |E_(i-1)|` at a (W)-stage,
   then `nu_(i-1) != mu_(E_(i-1))`.
4. The output of the first enlarging stage is not uniform on any left coset of its window `K_j`.
5. The last stage may instead have its window in any subgroup `K_k` that is Rokhlin-maximal at `E_(k-1)`. If
   `S_1, ..., S_(k-1)` never change the alphabet, then `|B| >= |A|`.

*Proof.*

**Step 0 (each stage is injective for its input).** Let `X_0` be a conull Borel set on which `tau` is
injective. `T_(i-1)` is injective on `X_0`, so `Y_(i-1) = T_(i-1)(X_0)` is Borel by Lusin–Souslin, and
`nu_(i-1)(Y_(i-1)) >= mu_A(X_0) = 1`. If `S_i(T_(i-1) x) = S_i(T_(i-1) x')` with `x, x'` in `X_0`, then
`tau(x) = tau(x')`, so `x = x'`. So `S_i` is injective on the `nu_(i-1)`-conull set `Y_(i-1)`.

**Step 1 (a stage with uniform input).** Suppose `nu_(i-1) = mu_(E_(i-1))`.

* **(R).** Theorem A gives `nu_i = mu_(E_i)`.
* **(P).** By definition.
* **(W).** `S_i` is a.e.-injective on `(E_(i-1)^G, mu)`. By `bernoulli-codes-descend-to-window-subgroup` its
  subgroup code over `K_i` is a.e.-injective, so `|E_i| >= |E_(i-1)|` by Lemma 1, Part 1. If equality holds,
  coset lifting (Section 2, Remarks) gives `nu_i = mu_(E_i)`.

Items 1 and 2 follow by induction on `i`. Item 3 is the (W) case read contrapositively.

**Item 4.** `S_j` descends to an a.e.-injective code `S_(K_j): E_(j-1)^(K_j) -> E_j^(K_j)` with uniform input.
Take its injectivity set to be invariant, by intersecting countably many translates. If the output were
`mu_(E_j)`, the Borel inverse on the image would be an a.e.-injective code from `(E_j^(K_j), mu)` into the
strictly smaller alphabet `E_(j-1)`. That contradicts Lemma 1, Part 1. The output on each coset `gK_j` is a copy
of this law.

**Item 5.** With uniform input, `S_k` descends to `K_k`. Proposition 1 of the compression artifact over `K_k`,
together with maximality, gives `|E_k| >= |E_(k-1)| = |A|`, exactly as in steps 3–4 of Theorem C. QED

**Reading for `U`.** A compression over `U` presented as a cascade of routing, measure-preserving and
sofic-window stages must:

* first change the alphabet by enlarging it at a sofic-window stage, producing a redundant intermediate measure
  that is not uniform on any coset of that window;
* shrink the alphabet only at stages that read a non-uniform measure, or at a last stage along a
  Rokhlin-maximal nonsofic window.

So the saving has the shape of an error-correcting code: redundancy is added along one sofic window, spent along
another, and recovered through relations between the windows. This extends Theorem C from one combining stage to
any number of stages that keep the alphabet, however the windows interact.

## 4. Sharpness: enlarging cascades contain every continuous code

**Proposition H.** Let `W = {w_1, ..., w_m}` in `G` be finite and `f: A^W -> B`. The continuous code
`tau(x)(g) = f((g^-1.x)|_W)` is a cascade of `m` (W)-stages along the cyclic subgroups `<w_1>, ..., <w_m>`, and
the first `m - 1` of them enlarge the alphabet.

*Proof.* Put `E_0 = A` and `S_i(y)(g) = (y(g), y(g w_i))`, the code with window `{1, w_i}` in `<w_i>` into
`E_i = E_(i-1)^2`. By induction, `T_i(x)(g) = (x(g u))_u`, indexed by the `2^i` formal products
`u = u_i ... u_1` with `u_l` in `{1, w_l}`. Each `w_l` occurs, as the product with `u_l = w_l` and every other
factor `1`. So applying `f` to the `W`-coordinates at the last stage realizes `tau`. QED

So non-enlargement is the only accounting the stage structure supports. Once enlarging stages are allowed,
cascades along cyclic windows include every continuous code, and a counting theorem for them would decide every
continuous compression. What remains is the composite window, the object of
`sofic-radical-localizes-bernoulli-deficit-witnesses`.

**Remark (continuous decoders give strict automata).** Suppose a compression `tau: A^G -> B^G` with
`|B| < |A|` is continuous and has a continuous decoder `sigma` with `sigma o tau = id` almost everywhere. Since
`mu_A` has full support, the conull set is dense, and both sides are continuous, so `sigma o tau = id`
everywhere. So `tau` is injective. Composing with an injection `B -> A` gives an injective, non-surjective
automaton on `A^G`, by Curtis–Hedlund–Lyndon. A compression with continuous encoder and decoder is therefore a
strict automaton. What the measurable target adds is freedom in the decoder.

## 5. Where it stops

* **Enlarging stages.** Item 4 of Theorem G shows Lemma 1's rigidity cannot hold for them. A later shrinking
  stage along `K_(j')` reads a measure that is not a product over the cosets of `K_(j')`, so descent is
  unavailable. Lemma 1's count still runs whenever the finite pattern of the composite encoder window and a
  decoder window has good charts at most points of finite models, and then it excludes compression. That is the
  localization theorem again. Beyond non-enlargement the stages add nothing, and the problem is the composite
  pattern.
* **What a construction must be.** An enlarging stage along a sofic window produces redundancy. Shrinking
  stages then decode through relations of `U` between the windows that no finite model realizes at most points.
  After the enlarging stage the measure is non-uniform on every coset of its window, and every shrinking
  (W)-stage reads a non-uniform measure.
* **Borel versus continuous.** Proposition H covers continuous codes. A Borel code is not a finite cascade, and
  injectivity almost everywhere does not pass to limits of approximating cascades.
* **Nonsofic windows in the middle.** Lemma 1, Part 2 is proved from models. For a window that is only known to
  be Rokhlin-maximal, Part 1 is available but Part 2 is not, so such a stage is allowed only last (item 5).
