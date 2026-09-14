# Small separated pairing families defeat the folded long-code noise test

Date: 2026-09-11. Status: complete proofs of two obstructions. **This is not a
proof or a disproof of the Unique Games Conjecture**, and it does not contradict
the Braverman--Khot--Minzer theorem, whose full-richness hypothesis is exactly
what fails below. No proof-assistant verification or priority claim is made.

The Cairn region already records one instance: the affine family `F_lin`
(`affine-long-code-test-has-no-uniform-soundness`). Theorem 1 below shows that
the phenomenon has nothing to do with linearity. Any family of pairings that is
*separated* and has size `2^(o(N))` fails the same test. Theorem 2 shows that
the density comparison BKM's analysis relies on (their Lemma 27) needs at
least `m^(N/2)/C` pairings. Together they say that an intermediate family in
BKM's "Making games richer?" program must carry pairing entropy linear in the
alphabet size before this test can be applied to it.

Source read on 2026-09-11: [Braverman--Khot--Minzer, *On Rich 2-to-1 Games*,
ITCS 2021](https://drops.dagstuhl.de/storage/00lipics/lipics-vol185-itcs2021/LIPIcs.ITCS.2021.27/LIPIcs.ITCS.2021.27.pdf):
Definition 5 (richness), Section 1.3 (the families `F_lin`, `F`-rich games and
the chain `F_lin = F_0 <= F_1 <= ... <= F_T = F_all`), Lemmas 23--37 and
Section 5 (the reduction and its soundness).

## 1. Setting

Let `n >= 2` and `N = 2n`. A *perfect pairing* `pi` of `[N]` is a partition of
`[N]` into `n` sets of size two; `pairs(pi)` is that set of pairs. A 2-to-1 map
`p : [N] -> [n]` *induces* `pi` when its fibres are the pairs of `pi`. For two
pairings put

```text
ov(sigma,pi) = |pairs(sigma) intersect pairs(pi)| / n.
```

A family `P` of pairings is **delta_0-separated** when `ov(sigma,pi) <= 1-delta_0`
for all distinct `sigma,pi in P`.

Following BKM Section 1.3, a 2-to-1 game is **`P`-rich** when, for every left
vertex `u`, the pairing induced by the projection of a uniformly random edge at
`u` is uniformly distributed on `P`.

The transformation `R_(rho,m)` is the folded long-code noise test of BKM
Section 5 with `rho = 1-epsilon`, written out exactly in Section 4 of
[the affine artifact](unique-games-affine-test-soundness-2026-09-07.md). The
noise kernel on `Z_m` is `K_rho(s,t) = rho 1_(s=t) + (1-rho)/m`, applied
independently to coordinates. The test:

1. choose a right vertex `v` and two neighbours `u,w`, independently and uniformly;
2. choose `a` uniform in `Z_m^n` and let `b = K_rho(a)`;
3. set `A = p_(uv)^(-1)(a)` and `B = p_(wv)^(-1)(b)`, i.e. `A_x = a_(p_(uv)(x))`;
4. let `X = K_rho(A)`, `Y = K_rho(B)` and accept iff `F_u(X) = F_w(Y)`,

where the `F_u : Z_m^N -> Z_m` are folded: `F_u(X + t 1) = F_u(X) + t`. The
value of the output unique game is the largest acceptance probability over
folded assignments.

## 2. Theorem 1

**Theorem 1.** Let `n >= 2`, `N = 2n`, `m >= 2`, `0 < rho < 1`,
`0 < delta_0 <= 1`, and let `P` be a nonempty `delta_0`-separated family of
perfect pairings of `[N]`. There is a finite `P`-rich 2-to-1 game `G` on a
complete bipartite graph, with left alphabet `[N]` and right alphabet `[n]`,
such that

```text
val(G) <= 16/N + (4 + 4 log_2 N + log_2 |P|) / |P|,                   (T1)
val(R_(rho,m)(G)) >= 1/m + (1-1/m) rho^3 - 2 |P| exp(-N rho^4 delta_0^2 / 96).   (T2)
```

**Corollary.** Fix `m >= 2`, `0 < rho < 1`, `delta_0 > 0` and `c > 0`. Let
`P_N` be `delta_0`-separated families with `|P_N| / log_2 N -> infinity` and
`log |P_N| <= (rho^4 delta_0^2/96 - c) N`. Then `val(G_N) -> 0` while
`val(R_(rho,m)(G_N)) >= rho^3 - o(1)`. Choosing `rho` close to `1` gives output
value close to `1`. So the test has no uniform soundness on `P_N`-rich inputs,
for every output alphabet `m`.

## 3. The source game

Index `P = {pi_0, ..., pi_(|P|-1)}`. Put `s = ceil(2N^2 (ln N + 1) / |P|)` and
`n_0 = s |P|`, so `n_0 >= 2N^2 (ln N + 1)`. Take `U = V = {0, ..., n_0 - 1}` and
all edges `U x V`. The edge `(u,v)` carries the pairing `pi_j` with
`j = (u+v) mod |P|`. For fixed `u` the map `v -> (u+v) mod |P|` is `s`-to-1
onto the indices, so every pairing occurs on exactly `s` edges at `u`: the game
is `P`-rich.

Randomness, all independent:

* for each `(u,j)`, a pair `c_(u,j)` of `pi_j`, uniform among its `n` pairs;
* for each edge `(u,v)` with index `j`, a bijection `r_(uv) : pairs(pi_j) -> [n]`,
  uniform subject to `r_(uv)(c_(u,j)) = 0`.

The projection is `p_(uv)(x) = r_(uv)([x]_(pi_j))`. It is 2-to-1 and induces `pi_j`.

**Value.** Fix labelings `alpha : U -> [N]` and `beta : V -> [n]`. Edge
`(u,v)` with index `j` is satisfied iff `r_(uv)([alpha_u]) = beta_v`.

* If `[alpha_u] = c_(u,j)`, it is satisfied iff `beta_v = 0`.
* Otherwise `r_(uv)([alpha_u])` is uniform on `[n] \ {0}` given the `c`'s. The
  edge can be satisfied only if `beta_v != 0`, and then with probability
  `1/(n-1) <= 4/N`, since `N >= 4`.

So the number of satisfied edges is at most `Sigma_1 + Sigma_2`. Here
`Sigma_1 = sum_u s L_u(alpha_u)` with `L_u(a) = #{j : a in c_(u,j)}`. And
`Sigma_2` counts satisfied edges from the second case: given the `c`'s it is a
sum of at most `n_0^2` independent indicators, each with mean at most `4/N`.

*First term.* For fixed `u` and `a`, `L_u(a)` is a sum of `|P|` independent
Bernoulli`(2/N)` variables. Each `pi_j` has exactly one pair containing `a`,
chosen with probability `1/n`, whatever the structure of `P`. Put
`k_0 = ceil(max(4e|P|/N, log_2(4 N n_0)))`. Then

```text
Pr[L_u(a) >= k_0] <= binom(|P|,k_0) (2/N)^(k_0) <= (2e|P|/(N k_0))^(k_0) <= 2^(-k_0) <= 1/(4 N n_0).
```

A union bound over the `N n_0` pairs `(u,a)` shows that, with probability at
least `3/4`, every `L_u(a) <= k_0 - 1`. On that event
`Sigma_1 / n_0^2 <= (k_0 - 1)/|P| <= 4e/N + log_2(4 N n_0)/|P|`.

*Second term.* By Hoeffding's inequality, for each fixed labeling
`Pr[Sigma_2 >= 5 n_0^2/N] <= exp(-2 (n_0^2/N)^2 / n_0^2) = exp(-2 n_0^2/N^2)`.
There are at most `N^(2 n_0)` labelings, so the probability that some labeling
reaches `5 n_0^2/N` is at most `exp(2 n_0 ln N - 2 n_0^2/N^2)`. Because
`2 n_0^2/N^2 >= 4 n_0 (ln N + 1)`, this is at most `e^(-4) < 1/4`.

Both good events hold with positive probability. Fix such a choice. Then
`val(G) <= 5/N + 4e/N + log_2(4 N n_0)/|P|`. Using
`n_0 <= 2N^2(ln N + 1) + |P| <= 2N^3 + |P|` gives
`4 N n_0 <= 12 N^4 |P|`, and so (T1).

## 4. Decoding the pairing

For `X in Z_m^N` and a pairing `sigma`, let

```text
S_sigma(X) = (1/n) sum_({x,y} in pairs(sigma)) 1[X_x = X_y].
```

*Planted law.* Fix an edge `(u,v)` with index `j`. Under the test, `a` is
uniform and `r_(uv)` is a bijection, so the symbols `a'_c = a_(r_(uv)(c))`,
`c in pairs(pi_j)`, are independent and uniform, and `A_x = a'_([x])`. Write
`X_x = A_x` if `keep_x`, else `X_x = fresh_x`. Here `keep_x` is
Bernoulli`(rho)`, `fresh_x` is uniform, and all these variables are independent.

*Means.* A pair `{x,y}` of `sigma` that is a pair of `pi_j` has
`Pr[X_x = X_y] = rho^2 + (1-rho^2)/m = 1/m + lambda`, with
`lambda = (1-1/m) rho^2 >= rho^2/2`. A pair of `sigma` whose endpoints lie in
different pairs of `pi_j` has independent uniform endpoints, so probability
`1/m`. Hence

```text
E S_sigma(X) = 1/m + lambda ov(sigma, pi_j).
```

*Concentration.* `S_sigma` is a function of the `n` variables `a'_c` and the
`N` variables `(keep_x, fresh_x)`. Changing one `a'_c` changes `X` in at most
two coordinates, hence at most two indicators, so `S_sigma` moves by at most
`2/n = 4/N`. Changing one `(keep_x, fresh_x)` moves it by at most `1/n = 2/N`.
The squared differences sum to `n (4/N)^2 + N (2/N)^2 = 12/N`. McDiarmid's
bounded-differences inequality gives, for `T > 0` and either tail,

```text
Pr[|S_sigma - E S_sigma| >= T] <= exp(-N T^2 / 6)      (one-sided bound).
```

*Separation.* Put `theta = 1/m + lambda (1 - delta_0/2)`. For `sigma = pi_j` the
mean exceeds `theta` by `lambda delta_0/2`. For `sigma != pi_j` in `P` the mean
is at most `theta - lambda delta_0/2`. A union bound over the `|P|` one-sided
events gives

```text
Pr[jhat(X) != j] <= |P| exp(-N lambda^2 delta_0^2 / 24) <= |P| exp(-N rho^4 delta_0^2 / 96) =: e_P,
```

where `jhat(X)` is the least index maximizing `S_(pi_jhat)(X)`. Outside the bad
events the true score is strictly above `theta` and every other score strictly
below, so ties are covered.

## 5. The folded labeling and its acceptance

Let `q(u,j)` be the smaller element of the pair `c_(u,j)` and define, on the
whole cube,

```text
F_u(X) = X_(q(u, jhat(X))).
```

Every score is invariant under `X -> X + t 1`, so `jhat` is too, and
`F_u(X + t 1) = F_u(X) + t`. This is a valid folded assignment on every input.

Condition on `v, u, w`, with indices `j` for `(u,v)` and `j'` for `(w,v)`. On
edge `(u,v)` the coordinate `q = q(u,j)` lies in `c_(u,j)` and
`p_(uv)(q) = r_(uv)(c_(u,j)) = 0`, so `A_q = a_0`. Likewise
`B_(q(w,j')) = b_0`. Put `I = X_(q(u,j))` and `J = Y_(q(w,j'))`. These are the
outputs of `F_u` and `F_w` whenever both decodings succeed.

`I` is a `K_rho` copy of `a_0`, `b_0` is a `K_rho` copy of `a_0`, and `J` is a
`K_rho` copy of `b_0`, with independent noise at each step. The kernels are
symmetric, `a_0` is uniform, and `K_s K_t = K_(st)`, so `J` given `I` has law
`K_(rho^3)`. Hence `Pr[I = J] = 1/m + (1-1/m) rho^3`.

`A` has the planted law of Section 4 for `pi_j`, so `Pr[jhat(X) != j] <= e_P`.
The vector `b` is uniform, because `K_rho` preserves the uniform measure, so `B`
has the planted law for `pi_(j')` and `Pr[jhat(Y) != j'] <= e_P`. Therefore

```text
Pr[F_u(X) = F_w(Y)] >= Pr[I = J] - 2 e_P,
```

with no independence assumed between the decoding errors and the symbols. This
is (T2).

## 6. Consequences and examples

* **`F_lin`** is `1`-separated with `|P| = N-1`, so Theorem 1 contains the
  earlier affine obstruction. The algebraic source game there has the sharper
  bound `2/sqrt(N)`.
* **Fixed-point-free affine involutions of `F_2^k`.** Two distinct ones agree
  on an affine subspace of dimension at most `k-1`, so they share at most `N/4`
  pairs. The family is `1/2`-separated and has at most `2^(k^2+k)` members.
* **Polynomial involutions of degree at most `D`** over `F_2`. By
  Schwartz--Zippel, two distinct ones agree on at most a `1 - 2^(-D)` fraction
  of points, so the family is `2^(-D)`-separated, with
  `2^(O(log^(D+1) N))` members.

Every such family fails. So an enrichment step whose pairings come from any
bounded-description algebraic family cannot feed this test. The test needs
separated pairing families of size at least `exp(rho^4 delta_0^2 N / 96)`.
Families with many near-duplicates are **not** covered; see Section 8.

This does not refute BKM's program. Their chain may pass through small families
as long as the test is only applied at the end. What it rules out is applying
the test at any intermediate, separated, subexponential stage.

## 7. Theorem 2: the density comparison needs exponentially many pairings

For a family `P` of pairings and `m >= 2`, let `nu_(P,m)` be the law of
`z = p_pi^(-1)(x)`, with `pi` uniform in `P`, `x` uniform in `Z_m^n` and `p_pi`
inducing `pi`. The map `p_pi^(-1)` is injective and its image is the set of
`pi`-pair-constant vectors, so

```text
nu_(P,m)(z) = (1/|P|) sum_(pi in P) m^(-n) 1[z is constant on every pair of pi].
```

**Theorem 2.** If `E <= Z_m^N` and `C > 0` satisfy `nu_(P,m)(E) >= theta` and
`nu_(P,m)(z) <= C m^(-N)` for every `z in E`, then `|P| >= theta m^n / C`.

*Proof.* The support of `nu_(P,m)` has at most `|P| m^n` points, each of mass
at most `C m^(-N)` on `E`. So
`theta <= nu_(P,m)(E) <= C m^(-N) |P| m^n`. ∎

**Relation to BKM.** Their Lemma 27 proves this density comparison for the full
family, with `E` the `K`-roughly balanced points and `C = C(K,m)`. Lemma 37
uses it through `E_pi ||h|_pi||_2^2 <= C(K,m) ||f^(>d)||_2^2`. The count of each
symbol in `p_pi^(-1)(x)` is twice its count in `x`, independent of `pi`, so the
balanced set has the same large `nu_(P,m)`-mass for **every** family. Theorem 2
then shows that the comparison fails whenever `|P| < m^n / (2C)`. This is only
an obstruction to that step of the proof. Theorem 1 is the stronger statement
that the test itself fails, for separated families.

## 8. What is not claimed, and open directions

* No NP-hardness, no algorithm, and no statement about UGC or the Rich 2-to-1
  conjecture is asserted.
* **Non-separated families.** The decoder needs separation. A family whose
  pairings share most of their pairs is not covered. A min-hash selection of the
  chosen pair would tolerate near-duplicates, but it correlates the loads
  `L_u(a)` across pairings. Families with a large common core then give the
  source game high value under that construction. This case is open.
* **The sufficiency side.** Section 5 of BKM uses richness only through Lemma 23
  for `pi` uniform in `P(u)`. Their proof of the moment bounds (Lemmas 31, 33--35)
  goes through expectations of functions of degree at most `8d` on the 2-to-1
  maps domain, and the tail bound (Lemma 37) goes through the density comparison
  of Theorem 2. It is therefore natural to ask whether a family that is a
  low-degree design of 2-to-1 maps and has the density comparison already
  suffices. That question is under investigation in the lane that wrote this
  artifact and is not claimed here.
