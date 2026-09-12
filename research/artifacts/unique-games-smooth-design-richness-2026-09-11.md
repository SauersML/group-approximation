# What richness the BKM reduction actually needs

Date: 2026-09-11. Status: complete proofs of Theorems A and C. Theorem B is a
line-by-line transfer of the published analytic proof, with the substitutions
listed. Section 6 is a new **open** formulation. **Nothing here proves or
disproves the Unique Games Conjecture.** No proof-assistant verification or
priority claim is made.

Sources read on 2026-09-11:

* [Braverman--Khot--Minzer, *On Rich 2-to-1 Games*, ECCC TR19-141 (full
  version)](https://eccc.weizmann.ac.il/report/2019/141/): Definitions 2.10--2.11,
  Theorem 2.13, Lemmas 3.1--3.2 and 4.1--4.12, Section 5, Appendices A--C.
  Lemma numbers below are those of this version. The ITCS 2021 version numbers
  them 23--37.
* The companion obstruction artifact
  [unique-games-pairing-entropy-obstruction-2026-09-11.md](unique-games-pairing-entropy-obstruction-2026-09-11.md)
  (Theorems 1--2 there), whose notation is used here: `N = 2n`, perfect
  pairings of `[N]`, the test `R_(rho,m)`, the noise kernel `K_rho`.

## 1. Summary

1. **Theorem A.** On any 2-to-1 game whose edge matchings can be decoded from a
   noisy pull-back table, the folded long-code noise test is no more sound than
   a *derived unique game* read off the same instance. The lemma and its proof
   idea come from the parallel lane `ugc-2` (2026-09-11); it is re-derived and
   written out here.
2. **Theorem B.** BKM's soundness analysis uses uniformity of the random pairing
   through exactly two properties: low-degree moments (a pairing design of
   strength `8d+1`) and a density comparison of the pull-back distribution. Any
   family with both properties can replace full richness.
3. **Theorem C.** The density comparison forces `|F| >= m^n / (2C)`.
4. **Section 6.** The *Smooth-Design Rich 2-to-1 Conjecture*: hardness for
   instances whose pairing distributions are only strength-`t` designs with the
   density comparison. It implies UGC via Theorem B. It is implied by the Rich
   2-to-1 conjecture (at all large alphabet sizes, as BKM's Section 5 uses it).
   Its families can be exponentially smaller than the set of all pairings.

## 2. Theorem A: the derived unique game

Let `G` be a regular bipartite 2-to-1 game with left alphabet `[N]` and right
alphabet `[n]`. For a left vertex `u`, let `M(u)` be the set of distinct
pairings induced by the edges at `u`. Define the unique game `UG_der(G)`:

* left vertices `(u,pi)` with `pi in M(u)`; the label of `(u,pi)` is a pair of `pi`;
* right vertices and right labels as in `G`;
* one edge `((u,pi), v)` for every edge `(u,v)` of `G` inducing `pi`, with the
  bijective constraint `pairs(pi) -> [n]` given by the projection `p_(uv)`.

A labeling of `G` induces one of `UG_der(G)`, sending `(u,pi)` to the pair of
`pi` containing the label of `u`, with the same satisfied edges. So
`val(UG_der(G)) >= val(G)`.

**Theorem A.** Let `m >= 2` and `0 < rho < 1`. Suppose every left vertex `u`
has a decoder `D_u : Z_m^N -> M(u)` with
`Pr[D_u(K_rho(A)) != pi] <= e` whenever `pi in M(u)` and `A` is uniform on
`pi`-pair-constant vectors. Then

```text
val(R_(rho,m)(G)) >= 1/m + (1-1/m) rho^3 val(UG_der(G))^2 - 2e.            (A1)
```

*Proof.* Fix an optimal labeling `lambda(u,pi)`, `beta(v)` of `UG_der(G)`. Let
`q(u,pi)` be either element of the pair `lambda(u,pi)` and define the folded
functions `F_u(X) = X_(q(u, D_u(X)))`. Folding holds if every `D_u` is invariant
under `X -> X + t 1`. The agreement-score decoders below are invariant, and any
decoder can be made so by composing with a canonical representative of the
shift orbit.

Run the test with right vertex `v`, neighbours `u,w`, and induced pairings `pi`
on `(u,v)` and `pi'` on `(w,v)`. Put `y_1 = p_(uv)(q(u,pi))` and
`y_2 = p_(wv)(q(w,pi'))`. Then `A_(q(u,pi)) = a_(y_1)` and
`B_(q(w,pi')) = b_(y_2)`. Let `I = X_(q(u,pi))` and `J = Y_(q(w,pi'))`.

* If both UG_der edges are satisfied, `y_1 = y_2 = beta(v)`. `I` and `J` are
  then `K_rho` copies of `a_(beta)` and `b_(beta)`, with `b = K_rho(a)` and
  independent noise, so `Pr[I=J] = 1/m + (1-1/m) rho^3`.
* Otherwise, if `y_1 != y_2`, then `a_(y_1)` and `b_(y_2)` are independent and
  uniform and `Pr[I=J] = 1/m`. If `y_1 = y_2` the probability is
  `1/m + (1-1/m) rho^3 >= 1/m`.

Let `s_v` be the fraction of edges at `v` satisfied by the labeling. `u` and `w`
are independent uniform neighbours, so `Pr[both satisfied | v] = s_v^2`, and

```text
Pr[I = J] >= 1/m + (1-1/m) rho^3 E_v s_v^2 >= 1/m + (1-1/m) rho^3 (E_v s_v)^2,
```

by Cauchy--Schwarz. Regularity gives `E_v s_v = val(UG_der(G))`. On correct
decoding `F_u(X) = I` and `F_w(Y) = J`. Each query has the planted law of the
hypothesis (`a` and `b` are uniform), so a union bound gives (A1). ∎

**Corollaries.**

* If at every `u` each pairing is induced by exactly one edge, every left vertex
  of `UG_der(G)` has degree one, so `val(UG_der(G)) = 1`. Then
  `val(R_(rho,m)(G)) >= 1/m + (1-1/m) rho^3 - 2e` for *every* such `G`, whatever
  `val(G)` is.
* For `delta_0`-separated `M(u)`, the agreement-score decoder of the companion
  artifact (Section 4) has `e <= max_u |M(u)| exp(-N rho^4 delta_0^2/96)`. The
  random source games of that artifact align the right relabelings, so their
  derived unique game has value one. This is a second proof of
  `separated-small-pairing-families-defeat-the-noise-test`.
* Moral (lane `ugc-2`): on instances with learnable matchings the test inherits
  exactly the hardness of the derived unique game. A proof of UGC through this
  test on such inputs would need that unique game to be hard already, which is
  circular.

## 3. Pairing designs and pull-back smoothness

**Definition (strength-`t` pairing design).** A family `F` of perfect pairings
of `[2n]` is *`t`-wise uniform* if for every partial matching `M` with at most
`t` pairs,

```text
Pr_(pi in F)[M <= pairs(pi)] = 1 / ((2n-1)(2n-3)...(2n-2|M|+1)),
```

which is the probability for a uniformly random perfect matching.

*Relation to BKM's degree.* Let `F~` be the uniform distribution on 2-to-1 maps
`tau o p_pi`, with `pi` uniform in `F` and `tau` uniform in `S_n`. For a monomial
`1_(pi(S)=T)` of degree `k` (Definition 2.10), averaging over `tau` gives
`1[the k specified pairs lie in pi] / (n)_k`. So `F~` fools all of `V_t(S_(2n,n))`
exactly when `F` is `t`-wise uniform. Right relabelings do not change any event
used below, since relabeling the right coordinates permutes the influences of
`f|_pi`. So only the pairing family matters.

**Definition (`C`-smooth).** For `m >= 2` and `K >= 1`, `F` is
`(K,m,C)`-smooth if `nu_(F,m)(z) <= C m^(-2n)` for every `K`-roughly balanced
`z in [m]^(2n)` (Lemma 4.2's notion). Here `nu_(F,m)` is the pull-back
distribution of the companion artifact, Section 7.

**Remark (family-independent mass).** Each symbol occurs in `p_pi^(-1)(x)`
exactly twice as often as in `x`. So whether `z = p_pi^(-1)(x)` is roughly
balanced depends only on `x`. Every family therefore gives the balanced set the
same mass, at least `1 - 2^(-Omega(K))` as in the proof of Lemma 4.12.

## 4. Theorem B: the transfer

**Theorem B.** Fix `m >= 2`, `delta, zeta > 0`, an integer `d >= 1` and
`C_0 >= 1`. Let `K = K(delta,zeta)` be as in BKM's proof of Lemma 3.2. There
are `gamma = gamma(m,delta,zeta,C_0)`, `tau = tau(d,m,delta,zeta)` and
`n_0 = n_0(d,m,delta,zeta,C_0)` such that the following holds for `n >= n_0`.
Let `F` be a `(8d+1)`-wise uniform, `(K,m,C_0)`-smooth family of pairings of
`[2n]`. Let `f : [m]^(2n) -> [0,1]` satisfy `||f^(>d)||_2^2 <= gamma`. Then, for
`pi ~ F~`,

```text
Pr_pi[ exists j : I_j[f|_pi] >= 4 delta  and  max_(i in pi^(-1)(j)) I_i^(<=d)[f] <= tau ] <= 2 zeta.
```

This is Lemma 3.1 with `pi` uniform in `S_(2n,n)` replaced by `pi ~ F~`. The
factor `4 delta` is the form in which BKM's proof concludes, and a rescaling of
`delta`.

*Proof: the substitutions.* Write `S_cond` for the uniform distribution on maps
with `pi(2n-1) = pi(2n) = n`, and `F~_cond` for `F~` conditioned on the same
event. The event has degree one, so `F~` gives it the same probability. A
function of degree at most `k` on the conditioned domain extends to one of degree
at most `k+1` on `S_(2n,n)`. So `F~_cond` fools every function of degree at most
`8d` on the conditioned domain.

* **Lemma 4.6** (`E_pi I_n[g|_pi] <= C(K,m)(I_(2n-1)[g] + I_(2n)[g])`). BKM prove
  it for `S_cond` from the density bound of Remark 4.3. `G[pi] = I_n[g|_pi]`, with
  `g = f^(<=d) 1_E`, has degree at most `2d` on the conditioned domain. This is
  the degree argument in the proof of Lemma 4.9, which is valid because
  `1_E(p_pi^(-1)(x))` does not depend on `pi` (Section 3 remark). So
  `E_(F~_cond) G = E_(S_cond) G` and the bound holds unchanged.
* **Lemmas 4.7--4.8** (typical pairs, conditional second moments). These are
  statements about `S_cond` alone and are used only to prove
  `E_(S_cond)[G^4] <= C(d,m) (E_(S_cond) G)^4` through Theorem 2.13.
  They are unchanged.
* **Lemma 4.9.** `G^4` has degree at most `8d`, so
  `E_(F~_cond)[G^4] = E_(S_cond)[G^4]`. Markov's inequality under `F~_cond`
  gives the same tail bound
  `Pr_(F~_cond)[G >= delta] <= C(d,K,m) delta^(-4) (I_(2n-1)[g]^4 + I_(2n)[g]^4)`.
* **Lemma 4.10.** The averaging over the pair `pi^(-1)(j) = {i,i'}` uses the
  probabilities of degree-one events, which `F~` matches. The union bound over
  `j` is unchanged.
* **Lemma 4.11.** A statement about `f` alone. Unchanged.
* **Lemma 4.12.** `E_(F~) ||q|_pi||_2^2 <= Pr_x[p_pi^(-1)(x) imbalanced]` does
  not depend on the family (Section 3 remark). For the high-degree part,
  `E_(F~) ||h|_pi||_2^2 = E_(z ~ nu_(F,m)) [f^(>d)(z)^2 1_E(z)] <= C_0 ||f^(>d)||_2^2`
  by smoothness, replacing `C(K,m)` there by `C_0`. Take `gamma` so small that
  `C_0 gamma` meets the requirement BKM place on `C(K,m) gamma`.
* **Proof of Lemma 3.2 and the minor modification for Lemma 3.1.** They compose
  the lemmas above with unchanged arithmetic. The refined event with
  `pi^(-1)(j) intersect L = empty` is again a union of degree-one conditionings. ∎

**Corollary B (the reduction).** Fix `epsilon` and let BKM's Section 5 choose
`m`, `delta`, `zeta`, `K` and hence `d`, `tau` and `eta`. Suppose that in an
instance with `n >= n_0`, the pairing family at every left vertex is
`(8d+1)`-wise uniform and `(K,m,C_0)`-smooth, with `gamma` chosen for `C_0`.
Then Section 5.2's soundness argument goes through verbatim: a unique game of
value above `epsilon` yields a 2-to-1 labeling of value `Omega(beta delta tau/d)`.
The completeness analysis (5.1) and the folding symmetries (Appendix C) never
use richness.

## 5. Theorem C: smoothness needs exponentially many pairings

**Theorem C.** If `F` is `(K,m,C)`-smooth, then
`|F| >= (1 - 2^(-Omega(K))) m^n / C`.

*Proof.* Apply Theorem 2 of the companion artifact with `E` the `K`-roughly
balanced points and `theta = 1 - 2^(-Omega(K))`, using the family-independent
mass remark of Section 3. ∎

So the families of Theorem B always have at least about `m^n` members. Together
with `separated-small-pairing-families-defeat-the-noise-test`, this says no
subexponential family can play the role of full richness, whether measured by
BKM's proof or by the test itself (for separated families).

## 6. The Smooth-Design Rich 2-to-1 Conjecture (open)

**Conjecture (SD-Rich).** There is a function `C : N x N -> [1,infinity)` such
that for every `epsilon > 0`, `t >= 1`, `m >= 2` and `K >= 1`, for all
sufficiently large `n`, `Gap-2-to-1_n[1-epsilon, epsilon]` is NP-hard on
instances whose pairing family at every left vertex is `t`-wise uniform and
`(K,m,C(K,m))`-smooth. (Smoothness is asked for one `(m,K)` at a time. Asking it
for all `m` at once would force `log |F| = omega(n)` by Theorem C.)

* **SD-Rich + Theorem B ⟹ UGC.** Given `epsilon`, BKM's choices fix `m, delta,
  zeta, K`. Take `C_0 = C(K,m)`, then `gamma`, then `d` so that
  `(1-epsilon)^(2d)` beats `gamma`, then `t = 8d+1`, then `eta`. Apply SD-Rich
  at `(eta, t, m, K)` and Corollary B.
* **Rich 2-to-1 at all large `n` ⟹ SD-Rich.** The family of all pairings is
  `t`-wise uniform for every `t <= n` and smooth with BKM's `C(K,m)` (Lemma 4.2).
  BKM's Section 5 already uses the Rich 2-to-1 conjecture at arbitrarily large
  alphabets for fixed `eta`.
* **Size.** By Theorem C every admissible family has at least about `m^n`
  members. It need not be all `(2n-1)!!` pairings.

**Remark (families much smaller than all pairings exist; sketch, not claimed in
Cairn).**

1. Let `Q` be `M` independent uniform pairings. For balanced `z`, the number of
   `pi in Q` making `z` pair-constant is Binomial with mean at most
   `C(K,m) M m^(-n)`. A Chernoff bound and a union bound over `m^(2n)` points
   show `Q` is `(K,m,2C(K,m))`-smooth once `M >= 3 m^n (2n ln m + 1) / C(K,m)`.
2. Composing with a `2t`-wise uniform family of permutations `D` (sets of size
   `n^(O(t))` exist, by Kuperberg--Lovett--Peled) gives `D o Q`. It is
   `t`-wise uniform, because inverses of `2t`-wise uniform permutations are
   `2t`-wise uniform, whatever `Q` is. Smoothness survives, because
   `nu_(sigma(Q),m)(z) = nu_(Q,m)(z o sigma)` preserves balance.

So admissible families of size about `m^n n^(O(t)) poly(n)` exist, far below
`(2n-1)!! ~ (2n/e)^n` when `n >> m`.

## 7. Where the obvious routes to SD-Rich die

* **Full richness from unique games (Appendix B).** Right vertices `(v, sigma)`
  with `sigma in S_(2k,k)` turn a unique constraint `phi` into the 2-to-1
  constraint `sigma o phi`, whose pairings are uniform. This needs a hard unique
  game as input and is circular as a source of hardness.
* **Refining the proved 2-to-1 instances the same way.** Composing a 2-to-1
  projection with a further 2-to-1 map gives a 4-to-1 constraint, so the output
  is not a 2-to-1 game.
* **Relabeling at a vertex or per edge.** A fixed label permutation per vertex
  conjugates all of its pairings at once and leaves the family's structure
  unchanged. Per-edge conjugation is pure gauge
  (`edge-conjugation-of-2to1-constraints-is-pure-gauge`).
* **Subexponential algebraic families.** Theorem C and the separated-family
  obstruction.
* **Learnable matchings.** Theorem A: the test is then no more sound than the
  derived unique game.

What remains is a genuinely new outer construction: one where each left vertex
sees a `t`-wise uniform, smooth, exponentially large family of kernel partitions
among its constraints, while keeping the soundness of the proved 2-to-1 theorem.
None is supplied.
