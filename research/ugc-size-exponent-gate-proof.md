---
rg: 2
id: ugc-size-exponent-gate-proof
kind: route
title: Decode the output of a fixed-exponent reduction by the ABS subexponential algorithms and contradict ETH
target: ugc-hardness-reductions-need-epsilon-dependent-size-exponent
requires:
  - abs-subexponential-unique-games-and-sse-algorithms
  - rich-2to1-conjecture-is-equivalent-to-ugc
---

All three parts share one frame. The reduction runs in time `poly(n^A)`, the
decoder runs in the time bound it has on YES inputs, and we answer NO if the
decoder does not finish in time. The decoder's output is checked in polynomial
time. The total time is `n^(O(A)) + exp(g(N))` with `N <= poly(n^A)`. If
`g(N) = o(n)` this is `2^(o(n))`, which contradicts ETH. Write `C_T, C_V` for
the absolute constants of ABS Theorem 5.1, so the running time is
`exp(k n^(C_T eps)) poly(n)` and the output value is `>= 1 - C_V eps log(1/eps)`.

## G1: unique games

**Input.** A unique game `G` produced by the reduction: alphabet `k`, at most
`N <= n^A` weighted constraints. On YES, `val(G) >= 1 - gamma`. On NO,
`val(G) <= 1/2`.

1. **Regularize.** Apply ABS Appendix A. It yields a regular game `G'` on one
   vertex per edge endpoint, so `N' <= 2N` vertices.
   * YES: `val(G') >= 1 - gamma/10`, since the cloud-constant lift of an
     assignment satisfies `0.9 + 0.1(1 - gamma)`.
   * NO: `val(G') <= 1 - (1 - 1/2)/10 = 0.95`. By Appendix A, any assignment
     of `G'` of value `1 - beta` gives one of `G` of value `1 - 10 beta`; with
     `beta < 0.05` that would make `val(G) > 1/2`.
2. **Decode.** Put `eps = (gamma/10)^(1/6)`. Choose `gamma_1` so that
   `C_V eps log(1/eps) < 0.05` whenever `gamma < gamma_1`. Run Theorem 5.1 on
   `G'`.
   * YES: `G'` has value `>= 1 - eps^6`, so within time
     `exp(k (2N)^(C_T eps)) poly(N)` the algorithm outputs an assignment of
     value `> 0.95`.
   * NO: no assignment exceeds `0.95`.
3. **Decide.** Answer YES iff the algorithm finishes within that bound and its
   output has value `> 0.95`.
4. **Time.** `k (2N)^(C_T eps) <= n^(o(1)) 2^(C_T eps) n^(A C_T eps)`. If
   `A C_T eps < 1`, this is `o(n)`, so 3SAT has a `2^(o(n))` algorithm,
   contradicting ETH.

Hence `A >= 1/(C_T eps) = C_T^(-1) (10/gamma)^(1/6)`, so `c_1 = 10^(1/6)/C_T`.

## G2: through the BKM noise test

**The construction** (verbatim from Braverman--Khot--Minzer, ITCS 2021,
Section 5, the paper imported in `rich-2to1-conjecture-is-equivalent-to-ugc`).
The input is a 2-to-1 instance `Psi = (L u R, E, [2l], [l], Phi)`. Variables
are the positions of folded long codes `F_u : [m]^(2l) -> [m]`, `u in L`. The
test reads:

> "Sample v∈R at random, a∈[m]^n at random, and b∈[m]^n that is 1−ε correlated
> with a. Sample two neighbours u,w of v independently at random. Set
> A = π^(−1)_(u,v)(a), B = π^(−1)_(w,v)(b) ∈ [m]^(2n). Finally, sample
> x∈[m]^(2n) that is 1−ε correlated with A, and y∈[m]^(2n) that is 1−ε
> correlated with B. Output the equation F_u(x) = F_w(y)."

This text was checked on 2026-09-18 against the retrieved PDF, Section 5,
pp. 19--20. Their `n` is our `l`. By Section 5.1, completeness `1 - eta` gives value
`>= 1 - 2 eta - 3 eps`.

**Size.** The support of the test is contained in the set of tuples
`(v, u, w, a, b, x, y)` with `u, w` neighbours of `v`. Its size is at most

    sum_v deg(v)^2 * m^l * m^l * m^(2l) * m^(2l)  <=  |E|^2 m^(6l).

The weights are products of `1/|R|`, `1/deg(v)^2`, `m^(-l)` and coordinatewise
correlation probabilities, so they are computable in time polynomial in `|E|`
for fixed `(m, l, eps)`. So the output unique game has alphabet `m` and at most
`N <= m^(6l) |E|^2` weighted constraints. Folding only merges variables. With
`|E| <= n^A` and `(m, l)` fixed, `N <= C n^(2A)`.

**Gate.** Under BKM certification, NO instances map to value `<= eps <= 1/2`.
YES instances, including the perfect-completeness ones, map to value
`>= 1 - 5 eps`. Composing gives a 3SAT reduction to unique games with
`gamma = 5 eps` and size exponent `2A + o(1)`. By G1, with
`eps_1 = gamma_1/5`,

    2A >= c_1 (5 eps)^(-1/6),  i.e.  A >= c_2 eps^(-1/6),  c_2 = c_1 5^(-1/6)/2.

**Consequences.**

* **Rich 2-to-1.** In BKM Section 5, "first m needs to be taken sufficiently
  large, then η sufficiently small, and in turn n sufficiently large". So for
  each `eps < eps_1`, every `eta <= eta_0(m(eps), eps)` with
  `l >= l_0(m, eta, eps)` is certified. Now suppose reductions to
  `Gap-Rich_l[1 - eta, eta]` or `Gap-Rich_l[1, eta]` exist with exponent at most
  `A` along a sequence `eta -> 0`. Pick `eps` with `c_2 eps^(-1/6) > A`. Every
  `eta` in the sequence below `eta_0(m(eps), eps)` gives a contradiction.
* **Smooth-design and finite-moment classes.** For these, the certification is
  the soundness transfer that routes `ugc-from-smooth-design-rich-2to1` and
  `ugc-from-finite-moment-pairing-hardness` already consume. The test and its
  size bound are unchanged, so the same argument applies.

G2 is conditional on those certifications, exactly as those routes are. It
imports nothing new beyond ABS.

## G3: small-set expansion on regular graphs

**Input.** A `d`-regular weighted graph `G` on `N <= n^A` vertices, with
`delta N` an integer. We may assume `delta N >= 100`: otherwise `N` is bounded
and we brute-force.

* YES: some `S` has `|S| = delta N` and `Phi(S) <= eta`.
* NO: every set of `delta N` vertices has `Phi >= 1 - eta`.

For `X` a vertex set, write `w(X)` for the total weight from vertices of `X`
into `X`, counting self-loops. So `1 - Phi(X) = w(X)/(d|X|)`.

**Tool.** ABS Theorem 2.1 with `beta = O(1/log(1/eps))`, as in their remark on
p. 8, gives an absolute `C_S` and `eps_S`, and an `exp(M^(C_S eps))`-time
algorithm with this property. Given `eps <= eps_S` and a regular `M`-vertex
graph that has a set of at most `t` vertices with expansion `<= eps`, it finds
a set of at most `2t` vertices with expansion `<= 0.01`.

* Theorem 2.1 states the bound `t`. Its restated proof gives `2t`. We use the
  weaker bound.
* The constants are absolute because ABS say all `O(·)` constants are.

**Iterated extraction.** Put `U_0 = V` and `T_0 = {}`. While
`|T_j| < delta N / 2`:

1. Let `G[U_j]` be the induced graph, regularized with self-loops as in ABS
   Section 4.
2. Run the tool on `G[U_j]` with `eps = 2 eta` and `t = delta N`.
3. Let `S_j` be the output. Set `T_(j+1) = T_j u S_j` and
   `U_(j+1) = U_j \ S_j`.

**The tool's hypothesis holds on YES.** Put `S_j' = S n U_j`.

* Edges of `G[U_j]` leaving `S_j'` are edges of `G` leaving `S`. Edges into
  removed vertices became self-loops.
* `|S_j'| >= delta N - |T_j| > delta N / 2`.

So `Phi_(G[U_j])(S_j') <= eta d delta N / (d delta N / 2) = 2 eta`, and each
round succeeds.

**Bound on the collected set.** Let `T` be the final collected set.

* An edge from `x in S_i` to `y` outside `T` has `y in U_i \ S_i`, so it leaves
  `S_i` in `G[U_i]`. Hence the weight leaving `T` is at most
  `sum_i 0.01 d |S_i|`, so `Phi_G(T) <= 0.01`.
* `delta N / 2 <= |T| < delta N / 2 + 2 delta N`.
* There are at most `N` rounds.

**Repair to exactly `delta N` vertices.**

* **Case `|T| <= delta N`.** Add any disjoint `T'` with `|T u T'| = delta N`.
  The weight leaving `T u T'` is at most `0.01 d |T| + d |T'|`, so

      Phi(T u T') <= 0.01 + (delta N - |T|)/(delta N) <= 0.51.

* **Case `|T| > delta N`.** Delete vertices one at a time, each time one of
  minimum `deg_X(v) = w(v, X)`, until `delta N` remain. Deleting from `X` with
  `|X| = s` lowers `w` by at most `2 min_v deg_X(v) <= 2 w(X)/s`. So

      w(final) >= w(T) prod_(s = delta N + 1)^(|T|) (s - 2)/s
               =  w(T) (delta N)(delta N - 1)/(|T|(|T| - 1)).

  With `w(T) >= 0.99 d |T|`,

      1 - Phi(final) >= 0.99 (delta N - 1)/|T| >= 0.99 * 0.99/2.5 > 0.39.

In either case the procedure outputs a set of `delta N` vertices with
`Phi <= 0.61`. On NO no such set exists when `eta < 0.39`. So we answer YES iff
the procedure succeeds within its time bound; the output is checked in
polynomial time.

**Time.** `N exp(N^(2 C_S eta)) poly(N)`, which is `2^(o(n))` when
`2 A C_S eta < 1`. ETH therefore forces `A >= 1/(2 C_S eta)`, so
`c_3 = 1/(2 C_S)` and `eta_1 = min(0.39, eps_S/2)`.

**Scope.** Regularity is ABS's hypothesis. The node's irregular convention,
`mu(S) in [delta, 10 delta]`, is not covered; that is survivor S3.
