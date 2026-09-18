---
rg: 2
id: hadamard-gadget-deletion-ratio-window-proof
kind: route
title: Minimax over folded random-on-primaries distributions, a decoded threshold adversary priced edge by edge, exact Reed-Muller mean distances for k <= 5, and Martinsson's relaxed-soundness cap
target: hadamard-gadget-deletion-ratio-window
requires: []
artifacts:
  - experiments/ugc-hadamard-gadget-window-2026-09-17/check_five_halves_adversary.py
  - experiments/ugc-hadamard-gadget-window-2026-09-17/check_decoder_adversary.py
  - experiments/ugc-hadamard-gadget-window-2026-09-17/rm1_mean_distance.c
  - experiments/ugc-hadamard-gadget-window-2026-09-17/minimax_gadget_value.py
  - experiments/ugc-hadamard-gadget-window-2026-09-17/results-2026-09-18.txt
---

Items 1 to 4 and 6 of `hadamard-gadget-deletion-ratio-window` are proved here
from definitions and one finite exact enumeration. Item 5 and the definitions
are literature imports, quoted below. The notation is that of the claim.

## Imports

**HHM+15.** J. Håstad, S. Huang, R. Manokaran, R. O'Donnell, J. Wright,
*Improved NP-inapproximability for 2-variable linear equations*. The version
used is the one dated December 23, 2015. Verified on 2026-09-18 against a
machine text extraction of that PDF. Symbols are normalized: `chi_S`,
`R(Had_k)`, `R_gen`.

* **Definition 2.16 (p. 6).** "A (c,s)-generic gadget reducing Max-phi to
  Max-psi is a gadget G satisfying the following properties: (Completeness):
  For every dictator assignment d_i, uval(d_i;G) <= c. (Soundness): For any
  A in R_gen(phi), uval(A;G) >= s."
* **Proposition 2.17 (p. 6).** "Suppose there exists a (c,s)-generic gadget
  reducing Max-phi to Max-psi, where Max-phi is any predicate containing a
  balanced pairwise-independent subgroup. Then for all eps > 0, given an
  instance I of Max-psi, it is NP-hard to distinguish between the following
  two cases: (Completeness): uval(I) <= c + eps. (Soundness):
  uval(I) >= s - eps."
* **Proposition 2.19.** "For some predicate phi, suppose G is a gadget
  reducing Max-phi to Max-2-Lin(2) which satisfies the following two
  conditions: (Completeness): For every dictator assignment d_i,
  uval(d_i;G) <= c. (Soundness): For any folded A in R_gen(phi),
  uval(A;G) >= s. Then there exists a (c,s)-generic gadget reducing Max-phi
  to Max-2-Lin(2)."
* **Definition 2.21.** "The primary variables of a Had_k-to-2-Lin(2) gadget
  are the functions +-chi_S, for any S ⊆ [k]. The remaining functions are
  auxiliary variables."
* **Definition 2.22.** "The Had_k predicate has 2^k input variables, one for
  each subset S ⊆ [k]. The input string {x_S}_(S ⊆ [k]) satisfies Had_k if
  for each S != ∅, x_S = x_∅ · prod_(i in S) (x_∅ · x_{i})."
* **Definition 2.23.** "Denote by R(Had_k) the set of folded distributions
  which are random on the primary variables."
* **Definition 2.24.** "A (c,s)-gadget reducing Max-Had_k to Max-2-Lin(2) is
  a gadget G satisfying the following properties: (Completeness): For every
  dictator assignment d_i, uval(d_i;G) <= c. (Soundness): For any
  A in R(Had_k), uval(A;G) >= s."
* **Proposition 2.25 (p. 9).** "The following two statements are equivalent:
  1. There exists a (c,s)-gadget reducing Max-Had_k to Max-2-Lin(2).
  2. There exists a (c,s)-generic gadget reducing Max-Had'_k to
  Max-2-Lin(2)." The proof of (1) => (2) begins: "consider the distribution
  A' in R(Had_k) which samples A ~ A and outputs either A or -A, each with
  half probability."
* **Corollary 2.26.** "Suppose there exists a (c,s)-gadget reducing
  Max-Had_k to Max-2-Lin(2). Then for all eps > 0, given an instance I of
  Max-2-Lin(2), it is NP-hard to distinguish between the following two
  cases: (Completeness): uval(I) <= c + eps. (Soundness): uval(I) >= s - eps."
* **Theorem 3.1.** "There is a (1/8, 11/64)-gadget reducing Had_3 to
  2-Lin(2)."
* **Theorem 4.1.** "[Theorem 1.8 restated] The value of the LP in
  Definition 2.28 is 11/64. As a result, for every (c,s)-gadget reducing
  Max-Had_3 to Max-2-Lin(2), s/c <= 11/8."
* **Theorem 6.1.** "Let G be a (c,s)-generic gadget reducing Max-phi to
  Max-2-Lin(2), where phi admits a balanced pairwise-independent set. Then
  s/c <= 1/(1-e^(-1/2)) ≈ 2.54."

**Martinsson.** Björn Martinsson, *On the NP-Hardness Approximation Curve for
Max-2Lin(2)*, arXiv:2408.04832, version dated 13 August 2024. Verified on
2026-09-18 against a machine text extraction of the arXiv PDF. His `s` is a
satisfied fraction, so his `1 - s` is our `s`.

* **Abstract.** "if c ⩾ 0.9232 then (1-s(c))/(1-c) > 1.48969".
* **Section 1.4.2.** "Two of the properties of lifting is that the
  completeness stays the same and the soundness does not decrease."
* **Corollary 2.** "It is NP-hard to approximate Min-2Lin(2)-deletion within
  a factor of 73139148/49096883 + ε ≈ 1.48969 + ε."
* **Section 1.6.** "any gadget reduction from a Hadamard CSP to Max-2Lin(2)
  that uses Wiman's soundness relaxation can never achieve an approximation
  ratio of Min-2Lin(2)-deletion better than 2."
* **Proposition 49.** "For any Had_k-to-2Lin(2) gadget (G, X_k, Y_k)
  (a) s(G) ⩽ rs(G). (b) There exists a Had_k-to-2Lin(2) gadget
  (~G, X_k, Y_k) with completeness 1 - 2^(-k) such that
  (1 - rs(G))/(1 - c(G)) ⩽ (1 - rs(~G))/(1 - c(~G)), (c) and for any
  Had_k-to-2Lin(2) gadget (~G, X_k, Y_k) with completeness 1 - 2^(-k)
  (1 - rs(~G))/(1 - c(~G)) ⩽ 2."

## Proof of item 1 (minimax identity)

Let `F(P)` be the set of distributions over folded `A : Q -> {-1,1}` that are
random on `P`. It is a nonempty polytope: it is cut out by finitely many
linear equations in the probability vector. It contains the uniformly random
folded function, because neither `P` nor `P'` contains an antipodal pair
(`chi_a != -chi_b` for all `a, b`). For `P`, `F(P)` is `R(Had_k)`. For `P'`,
`F(P')` is the set of folded members of `R_gen(Had'_k)`. Write `h(x, y)` for
Hamming distance.

**Step 1: equality edges.** For folded `A`, the constraint `x != y` is
violated exactly when `A(x) = A(y)`, that is, when `A(x) != A(-y)`. The same
holds for every dictator. So replacing each `x != y` by `x = -y` changes no
`uval` that enters either the completeness or the soundness condition. From
now on `G` is a distribution over equality edges `(x, y)`.

**Step 2: upper bound.** Let `G` be a `(c, s)`-gadget for `P`, whether of
Definition 2.24 type or generic for `Had'_k` (Definition 2.16).

* Dictator `d_i` cuts `(x, y)` iff `x_i != y_i`. So
  `(1/K) sum_i uval(d_i; G) = E_G h(x,y) / K <= c`.
* Let `A` in `F(P)` attain `z*(P)`. `A` is admissible in the soundness
  condition of either definition, so `s <= uval(A; G)`.
* Join `x` to `y` by a path of `h(x,y)` length-one edges. The union bound
  gives `Pr_A[A(x) != A(y)] <= h(x,y) z*(P)`.
* Hence `s <= E_G h z*(P) <= K c z*(P)`, so `s/c <= K z*(P)`.

**Step 3: attainment.** The function `(A, mu) -> E_(e ~ mu) Pr_A[A cuts e]`
is bilinear. Here `A` ranges over the polytope `F(P)` and `mu` over the
simplex of distributions on length-one edges. By von Neumann's minimax
theorem there is a `mu` with `min_A E_mu Pr_A[cut] = z*(P)`.

To balance `mu`, use translations. For `b in F_2^k`, let `T_b` act on `Q` by
`(T_b x)_i = x_(i+b)`. Then `T_b chi_a = chi_a(b) chi_a`. So `T_b` maps each
primary to plus or minus a primary, and `F(P)` is invariant under
`A -> A o T_b`: sign flips preserve uniformity, and folding is preserved. The
translations `T_b` are transitive on the `K` coordinates.

Let `mu~` be the average of `mu o T_b` over `b`. Then:

* By invariance, `min_A E_(mu~) Pr_A[cut] >= z*(P)`.
* Each coordinate direction receives mass exactly `1/K`, so every dictator
  has `uval = 1/K`.

So `mu~` is a `(1/K, z*(P))`-gadget with ratio `K z*(P)`. It satisfies
Definition 2.24, since `F(P)` for `P` is `R(Had_k)`. For `P'` it satisfies
the hypotheses of Proposition 2.19, whose soundness quantifies over folded
distributions only, and so it yields a generic `Had'_k` gadget with the same
`(c, s)`. This proves item 1.

## Proof of item 3 (decoded threshold adversary)

**Geometry.** A signed primary is `sigma chi_p` with `sigma = +-1` and
`chi_p in P`. Two distinct signed primaries are at distance `K/2` (distinct
`p`) or `K` (the same `p`, opposite sign). Let `m(x)` be the largest
agreement of `x` with a signed primary.

* If `m(x) > 3K/4`, the maximizer `sigma chi_p` is unique. Two maximizers
  would each agree with `x` on more than `3K/4` coordinates, and so they
  would be at distance less than `K/2`.
* Call it the anchor of `x`. The anchor of `-x` is `-sigma chi_p`, and
  `m(-x) = m(x)`.

**The adversary.** Draw `xi` uniform on `{-1,1}^P`, then `(i, tau)` jointly
with `xi` as in the hypothesis, and independently `t` uniform on `[3/4, 1]`.
Call `x` *near* if `m(x) > tK`. For near `x` with anchor `sigma chi_p`, let
`D_p` be the event `xi_p != tau chi_p(i)`. Set

* `A(x) = sigma xi_p` if `x` is near and `D_p` holds,
* `A(x) = tau x_i` otherwise.

**A is in F(P).**

* *Folded.* `-x` is near iff `x` is. Its anchor has the same `p` and sign
  `-sigma`, so both branches negate.
* *Random on P.* Take `x = chi_a`. Then `m = K > tK` almost surely, and the
  anchor is `chi_a` itself. If `D_a` holds, `A(chi_a) = xi_a`. Otherwise
  `A(chi_a) = tau chi_a(i) = xi_a`. So `(A(chi_a))_a = xi` is uniform.

**Pricing a length-one edge.** Let `y` be `x` with coordinate `j` flipped.

*Far case: `m(x), m(y) <= 3K/4`.* Neither endpoint is ever near, so
`A = tau d_i` on both. The edge is cut iff `i = j`, which has probability
`1/K` because `i` is uniform. So `K Pr[cut] = 1`.

*Near case: some endpoint has `m > 3K/4`, say `x` with anchor `sigma chi_p`.*

* **Setup.**
  * If `m(y) > 3K/4` too, the anchor of `y` is also `sigma chi_p`. A
    different anchor `sigma' chi_q` would agree with `x` on at least
    `m(y) - 1 >= 3K/4` coordinates, and `sigma chi_p` agrees with `x` on more
    than `3K/4`, so the two would be at distance less than `K/2`.
  * If `m(y) <= 3K/4`, then `y` is never near.
  * Either way only `sigma chi_p` matters. Let `a` and `b` be the agreements
    of `x` and `y` with it, so `|a - b| = 1`. Relabel so that `a = b + 1`,
    which puts `x` on the anchor side: `x_j = sigma chi_p(j) = -y_j`.
  * By the two bullets above, `x` is near iff `a > tK`, and `y` is near iff
    `b > tK`. The case `b <= 3K/4 < m(y)` cannot occur.
* **Probabilities in t.** `a >= 3K/4 + 1`, so `b >= 3K/4`.
  * `Pr[x far] = (K - a) 4/K`.
  * `Pr[x near, y far] = Pr[b <= tK < a] = 4/K`.
  * `y` near forces `x` near.
* **Cut conditions, given `(i, tau, xi_p, t)`.**
  * Not `D_p`: both endpoints get `tau d_i`, and the edge is cut iff `i = j`.
  * `D_p`, both near: both get `sigma xi_p`, so the edge is not cut.
  * `D_p`, both far: cut iff `i = j`.
  * `D_p`, `x` near, `y` far: `A(x) = sigma xi_p = -sigma tau chi_p(i)` and
    `A(y) = tau y_i`. The edge is cut iff `y_i = sigma chi_p(i)`. For `i = j`
    this is false. For `i != j` it says `x_i = sigma chi_p(i)`: `x` agrees
    with the anchor at `i`, which holds for exactly `a - 1` values of
    `i != j`.
* **Sum.** `t` is independent of `(i, tau, xi)`. The hypothesis
  `Pr[D_p | i] = delta` for every `i` gives `Pr[D_p, i = i_0] = delta/K` for
  every `i_0`. So

  `Pr[cut] = (1 - delta)/K + (delta/K)(4(K - a)/K) + (delta/K)(a - 1)(4/K)
           = (1 - delta)/K + 4 delta (K - 1)/K^2`,

  and `K Pr[cut] = 1 + delta (3 - 4/K)`. The value does not depend on `a`,
  `j`, `p` or `sigma`.

The near value is at least `1`, and near edges exist: an edge at a primary is
one. So `max_e K Pr[cut] = 1 + delta (3 - 4/K)`. Item 1 then gives
`R*(k) <= 1 + delta (3 - 4/K)`, and the same argument applies to `P'`.

**Nearest-codeword decoder satisfies the hypothesis with `delta = delta_k`.**
Let `(i, tau)` be uniform among the signed codewords nearest to `xi`. The
distance from `xi` to `tau chi(i)` is `(|P| - tau W_i)/2`, so the mean
normalized distance is `delta_k = 1/2 - E max_i |W_i| / (2|P|)`. Two
measure-preserving symmetries of `{-1,1}^P` are equivariant for the decoder,
because uniform tie-breaking commutes with bijections of the codeword set.

* *Translations* `xi_a -> chi_a(b) xi_a`. They map the codeword `(i, tau)` to
  `(i + b, tau)` and preserve every event `D_a`. So `i` is uniform and
  `Pr[D_a | i]` does not depend on `i`.
* *Coordinate maps.*
  * For `P` (all `a`), use the shift `xi_a -> xi_(a+e)`. It maps `(i, tau)`
    to `(i, tau chi_e(i))`, keeps `i`, and carries `D_(a+e)` to `D_a`.
  * For `P'` (`a != 0`), use `xi_a -> xi_(Ma)` with `M in GL_k(F_2)`. It
    maps `(i, tau)` to `(M^T i, tau)`. Combined with translations to return
    to `i = 0`, it shows that `Pr[D_a | i = 0]` does not depend on `a != 0`,
    because `GL_k` is transitive on nonzero vectors.
* So `Pr[D_a | i]` is a constant. Averaging over `a` shows the constant is
  `E d(xi, C)/|P| = delta_k`. `check_decoder_adversary.py` confirms both the
  uniformity and the per-edge closed form for `k = 3, 4` and both sets,
  using the exact joint law.

## Proof of item 2 (five halves)

Take `tau = +1` and `i` uniform and independent of `xi`. Then
`Pr[D_a | i] = 1/2` for every `a`. Item 3 gives
`R*(k) <= 1 + (1/2)(3 - 4/K) = 5/2 - 2^(1-k)`, and likewise for `P'`.
`check_five_halves_adversary.py` confirms the maximum edge price exactly in
rational arithmetic for `k = 2, 3, 4`. The bound is strictly below HHM+15
Theorem 6.1's `1/(1 - e^(-1/2))`, which exceeds `2.54`.

## Proof of item 4 (exact values, kill for k <= 5)

By item 3, `R*(k) < 2` as soon as `delta_k < 1/(3 - 4/K)`, and likewise for
`P'`. The values `delta_k` and `delta'_k` are exact finite averages.

* `rm1_mean_distance.c` computes them with integer arithmetic.
  * `max_i |W_i|` is invariant under multiplying `xi` by a signed codeword,
    since that permutes the `|W_i|`.
  * The full code has the information set `{0, e_1, ..., e_k}`. So
    enumerating the `2^(K-k-1)` words that are `+1` there visits each coset
    of `RM(1,k)` exactly once.
  * The punctured code is a group of `2K` words, because `k >= 2` makes its
    `2K` signed patterns distinct. The positions `{e_1, ..., e_k}` fix the
    word up to two codewords, so each coset is visited exactly twice.
  * In both cases the enumerated average equals the uniform average.
* `check_decoder_adversary.py` recomputes `delta_3` and `delta_4` for both
  sets by brute force over all `xi` with `Fraction` arithmetic, and it agrees.

The kill inequalities, checked in integers:

* `k = 4`: `1961 * 11 = 21571 < 32768 = 4 * 8192`, and
  `341 * 11 = 3751 < 6144 = 4 * 1536`. The threshold is `4/11`.
* `k = 5`: the threshold is `8/23`.
  * `78015813 * 23 = 1794363699 < 2147483648 = 8 * 2^28`.
  * `2381339 * 23 = 54770797 < 67108864 = 8 * 2^23`.
* `k = 2, 3`: the bounds `5/4`, `1`, `183/128` and `21/16` are all below
  `2`.

So `R*(k) <= 1.8356 < 2` and `R*'(k) < 2` for `2 <= k <= 5`.

**Tightness remarks.** These are not needed for the kill.

* Theorem 3.1 with Theorem 4.1 gives `R*(3) = 11/8` exactly. So the decoder
  bound `183/128` is not tight for `P` at `k = 3`.
* For `P'` at `k = 3`, the column-generation LP in `minimax_gadget_value.py`
  returns `1.3125 = 21/16`. This matches the decoder bound, but the LP is
  floating point, and only the upper bound `21/16` is used below.

## Proof of item 6 (erratum to HHM+15 Proposition 2.25, (1) => (2))

**The counterexample.**

* By Theorem 3.1 there is a `(1/8, 11/64)`-gadget reducing `Had_3` to
  2-Lin(2) in the sense of Definition 2.24.
* Suppose `G'` were a `(1/8, 11/64)`-generic gadget reducing `Had'_3`. Its
  variable cube is `{-1,1}^8`, since `|Sat(Had'_3)| = 8`, and its generic
  primaries are `P'`.
* The decoder adversary `A` of item 3 for `P'` is folded and random on `P'`,
  so `A` lies in `R_gen(Had'_3)`. Step 2 of item 1, applied to `A` in place
  of the optimum, gives
  `11/64 <= uval(A; G') <= K c max_e Pr_A[cut] = 1/8 (1 + delta'_3 (3 - 1/2)) = 21/128`.
* But `21/128 < 22/128 = 11/64`, a contradiction.

So statement (1) holds and statement (2) fails for `k = 3`,
`(c, s) = (1/8, 11/64)`.

**The failing step.** Let `A` be folded and in `R_gen(Had'_k)`, and let `A'`
be the fifty-fifty mixture of `A` and `-A`. The law of
`(xi, A'(chi_0))` is the average of the laws of `(xi, b)` and `(-xi, -b)`,
where `b = A(chi_0)`. Given `xi = zeta`, the probability that
`A'(chi_0) = 1` is `(Pr[b = 1 | zeta] + Pr[b = -1 | -zeta])/2`. This is
`1/2` for every `zeta` iff `Pr[b = 1 | zeta] = Pr[b = 1 | -zeta]`, that is,
iff the law of `b` given `xi` is even in `xi`. The definition of `R_gen`
does not force this.

* For the decoder adversary, `b = A(chi_0) = tau`, because `chi_0` is the
  all-ones vector. It agrees with every signed primary of `P'` on exactly
  `K/2` coordinates, so it is never near.
* Negating `xi` negates each nearest codeword, so
  `Pr[tau = 1 | -zeta] = 1 - Pr[tau = 1 | zeta]`.
* Given `xi' = zeta`, the mixture therefore has `A'(chi_0) = 1` with
  probability `Pr[tau = 1 | zeta]`, the decoded sign. For `k = 3` this is not
  identically `1/2`. For example, if `zeta` is itself a signed codeword,
  `tau` is its sign. So `A'` is not random on `P`.

**Corollary 2.26 survives.** Let `G` be a `(c, s)`-gadget for `Had_k` under
Definition 2.24, on `Q = {-1,1}^K`.

* **The embedding.**
  * The `Had_k` predicate of Definition 2.22 has
    `Sat = {(b chi_S(z))_S : b = +-1, z in F_2^k}`, with `2K` rows. Its
    generic cube is `{-1,1}^(2K)`, with rows indexed by `(z, b)`.
  * Embed `x -> x^ = (b x_z)_(z,b)`. This maps `chi_S` to the generic
    primary `v_S`, and maps `-x` to `-(x^)`.
  * Let `G^` be `G` transported by the embedding.
* **Completeness.** Dictator `d_(z,b)` restricted to the image is `b d_z`. A
  sign on both endpoints preserves every 2-Lin(2) constraint, so
  `uval(d_(z,b); G^) = uval(d_z; G) <= c`.
* **Soundness.** A folded `A^ in R_gen(Had_k)` restricts to
  `A(x) = A^(x^)`. This `A` is folded and random on `P`, so `A` lies in
  `R(Had_k)` and `uval(A^; G^) = uval(A; G) >= s`.
* **Conclusion.** Proposition 2.19 now gives a `(c, s)`-generic gadget for
  `Had_k`. `Sat(Had_k)` is itself a subgroup of `{-1,1}^(2^k)` and is
  balanced pairwise independent: each coordinate is uniform through `b`, and
  for `S != T` the product of the two coordinates is `chi_(S Δ T)(z)`, which
  is uniform. So Proposition 2.17 applies and yields the conclusion of
  Corollary 2.26. In particular the `11/8` hardness of HHM+15 stands.

## Item 5

This is Proposition 49 of Martinsson verbatim, with (a) giving `rs >= s`.
His `1 - rs` is at most our `s`, so any certificate of the form "relaxed
soundness is at most `rs`" certifies a ratio of at most `(1 - rs)/(1 - c)`.

* By (b), passing to completeness `1 - 2^(-k)` does not lower that quantity.
* By (c), it is then at most `2`.

His Section 1.6 states the same conclusion in words.
