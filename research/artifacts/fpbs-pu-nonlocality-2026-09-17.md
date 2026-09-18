# p_u is not local, and open nonuniqueness certificates are pinned at p_c near amenable limits

Worker swarm-0917-w6-w6-bs-pull, 2026-09-17. Family: logic-computability
(topological complexity of the statement in the space of marked groups).

## 0. Setting

`M_d` is the compact space of `d`-marked groups `(Gamma, s_1..s_d)`. A basic
neighbourhood of `G` is `N_r(G) = {G' : B_r(Cay G') = B_r(Cay G)}` as rooted
labelled balls. Put `X = M_d x [0,1]` with the product topology. For an infinite
marked group `G`, `p_c(G)` and `p_u(G)` refer to Bernoulli bond percolation on
its Cayley graph; `p_u(G) = inf{p : exactly one infinite cluster a.s.}`.

A **nonuniqueness certificate** is a set `U subseteq X`. It is **sound on a class
`C`** of marked groups if `(G',p) in U` and `G' in C` imply `p <= p_u(G')`.
It is **open** (ball-local, Sigma^0_1 in ball data) if `U` is open in `X`, i.e.
membership of `(G,p)` is witnessed by one finite ball of `G` and one open
parameter window. Every finite list of strict inequalities between polynomials
in `p` computed from finite balls defines an open set.

`A_d subseteq M_d` is the set of marked groups `G` that are local limits of
**infinite amenable marked groups `G_k` with `p_c(G_k) != 1`**.

## 1. Imports

* **[EH]** P. Easo, T. Hutchcroft, *The critical percolation probability is
  local*, arXiv:2310.10983, abstract read verbatim from the arXiv API on
  2026-09-17: "We prove Schramm's locality conjecture for Bernoulli bond
  percolation on transitive graphs: If $(G_n)_{n\geq 1}$ is a sequence of
  infinite vertex-transitive graphs converging locally to a vertex-transitive
  graph $G$ and $p_c(G_n) \neq 1$ for every $n \geq 1$ then
  $\lim_{n\to\infty} p_c(G_n)=p_c(G)$."
  Recorded as `fpbs-easo-hutchcroft-pc-locality`.
* **[BK]** `fpbs-hp-relative-burton-keane` (Hutchcroft–Pan Theorem 1.7), applied
  with `H = Gamma`: if `Gamma` is amenable then `p_c(G) = p_u(G)`.
* Standard facts: `p_c(Z^2) = 1/2` (Kesten); on the 4-regular tree `T_4`,
  `p_c = 1/3` (branching process) and `p_u = 1` (for `p < 1` a fixed edge is
  closed with positive probability while both of its sides carry infinite
  clusters, so by the Newman–Schulman trichotomy
  `fpbs-cluster-count-trichotomy` there are infinitely many infinite clusters
  for `p in (1/3,1)`).

## 2. Lemma (lifted exploration)

**Lemma 1.** Let `pi : Gamma -> Q` be a surjection of marked groups sending
`s_i` to `s_i`, and suppose the `2d` elements `s_i^{±1}` stay pairwise distinct
in `Q` (so `pi` induces a covering map of Cayley graphs). Then
`|C_Gamma(o)|` stochastically dominates `|C_Q(o)|` at every `p`, hence
`theta_Gamma(p) >= theta_Q(p)` and `p_c(Gamma) <= p_c(Q)`.

*Proof.* Run a breadth-first exploration of `C_Q(o)` that only tests edges from
a discovered vertex `v` to a not yet discovered vertex `w`. Keep a lift
`l(v) in Gamma` with `pi l(v) = v`, `l(o) = o`. To test the `Q`-edge `{v, v s}`
(`s` a generator), test the `Gamma`-edge `{l(v), l(v) s}` instead; if it is open,
discover `w = v s` and set `l(w) = l(v) s`. Distinct tested `Q`-edges have
distinct lifts (their projections differ), and which edge is tested next is a
function of past outcomes only, so the outcomes are i.i.d. Bernoulli(`p`) and
the discovered set has the law of `C_Q(o)`. The map `l` is injective because
`pi o l = id`, and every `l(w)` is joined to `o` by open lifted edges. So
`|C_Gamma(o)| >= |discovered set|` in this coupling. `QED`

## 3. Theorem A: p_u is neither lower nor upper semicontinuous

**(A1) Not lower semicontinuous.** Let `F = F_2 = <a,b>` and
`S_k = F / F^(k)`, `F^(k)` the `k`-th derived subgroup, marked by `a, b`.

1. `S_k -> F` in `M_2`. The derived series decreases and
   `F^(k) <= gamma_(2^k)(F)`, and `cap_n gamma_n(F) = 1` (Magnus). The ball
   `B_r` is determined by which of the finitely many words of length `<= 2r`
   are trivial; each nontrivial one leaves `F^(k)` for all large `k`.
2. `S_k` is solvable, hence amenable, so `p_u(S_k) = p_c(S_k)` by [BK].
3. For `k >= 1`, `S_k` surjects onto `S_1 = Z^2` with `a,b -> e_1,e_2`, and
   `e_1^{±1}, e_2^{±1}` are distinct, so Lemma 1 gives
   `p_c(S_k) <= p_c(Z^2) = 1/2`. In particular `p_c(S_k) != 1`.
4. By [EH], `p_u(S_k) = p_c(S_k) -> p_c(T_4) = 1/3`, while `p_u(F) = 1`.

So `p_u(lim S_k) = 1 > 1/3 = lim p_u(S_k)`. Without [EH] one still has
`limsup p_u(S_k) <= 1/2 < 1`.

**(A2) Not upper semicontinuous.** `Z x C_k`, marked by `(1,0),(0,1)`,
converges to `Z^2`. Each `Z x C_k` is a quasi-line, so `p_c = p_u = 1`
(an infinite cluster must cross each of the finite cuts `{n} x C_k`, and a
product of infinitely many independent crossing probabilities `< 1` vanishes);
the limit has `p_u(Z^2) = 1/2`.

**(A3) The collapse set is not open, the gap set is not closed-up.** By (A1)
`F_2` has `p_c < p_u` but lies in the closure of `{p_c = p_u}`; the gap function
`p_u - p_c` is not lower semicontinuous at `F_2` (limit `0`, value `2/3`).

## 4. Theorem B: open certificates are pinned at p_c on A_d

**Theorem B.** Let `G in A_d` and let `U subseteq X` be open and sound on
infinite amenable marked groups. Then `(G,p) in U` implies `p <= p_c(G)`.

*Proof.* Suppose `(G,p) in U` with `p > p_c(G)`. Openness gives `r` and
`eta in (0, p - p_c(G))` with `N_r(G) x (p - eta, p + eta) subseteq U`.
Choose infinite amenable `G_k -> G` with `p_c(G_k) != 1`. By [EH],
`p_c(G_k) -> p_c(G) < p - eta`, so for `k` large `G_k in N_r(G)` and
`p_c(G_k) < p - eta`. Then `(G_k, p - eta/2) in U`, and soundness plus [BK]
give `p - eta/2 <= p_u(G_k) = p_c(G_k) < p - eta`, a contradiction. `QED`

Without [EH]: `(G,p) in U` implies `p <= liminf_k p_c(G_k)` along every
admissible approximating sequence (shrink `eta` below `p - liminf_k p_c(G_k)`
and pass to a subsequence).

**Theorem B' (restricted soundness).** The same conclusion holds if `U` is only
sound on `N_r(G) cap {infinite amenable}` for one `r` (the proof only uses
approximants inside `N_r(G)`). Consequently, if `V subseteq X` is any sound
certificate (`(G',p) in V => p <= p_u(G')` for all infinite `G'`), then for
`G in A_d` and `p > p_c(G)`, `V` is not a neighbourhood of `(G,p)`. For a
hypothesis-restricted certificate `V = U cap (H x [0,1])` with `U` open, the
hypothesis set `H` must not be a neighbourhood of `G` (otherwise
`U cap (N_r(G) x [0,1])` is open, sound on the amenable groups of `N_r(G)`, and
Theorem B applies): for every `r`, `H` omits amenable groups in `N_r(G)` whose
`p_c` is within any given distance of `p_c(G)`. Closed spectral hypotheses such as
`rho <= r < 1`, `h >= h_0 > 0`, `||T_q||_(2->2) <= M`, `lambda(q) <= r < 1`
have this property; no finite-ball strict inequality does.

## 5. Corollary C: the walk connectivity rate jumps, so (IS)-type premises are non-local

Let `a_n(G,q) = sum_x mu^n(o,x) P_q(o <-> x)` for simple random walk `mu`, and
`lambda(G,q) = lim_n a_n^(1/n)`, the rate of `fpbs-integrated-pivotal-rate-identity`.

* If `q > p_u(G)` then `P_q(o <-> x) >= theta(q)^2` by Harris on the unique
  infinite cluster, so `lambda = 1`. On amenable `G`, `lambda(G,q) = 1` for every
  `q > p_c(G)`.
* On `Cay(F_2) = T_4`, `P_q(o <-> x) = q^|x|` and `|X_n|` has drift `1/2`, so
  `a_n <= P(|X_n| <= n/4) + q^(n/4)` decays exponentially (Chernoff) and
  `lambda(F_2,q) < 1` for every `q < 1`.
* Hence for every `q in (1/3,1)`: `lambda(S_k,q) = 1` for all large `k` (by [EH],
  `p_c(S_k) < q`), while `lambda(F_2,q) < 1`. The rate is not upper
  semicontinuous in `G` at `(F_2,q)`, and `{G : lambda(G,q) < 1}` is not open.

In general `a_(n+m) >= a_n a_m` (Harris) and `a_n = sup_R a_(n,R)` with
`a_(n,R)` computed in the ball of radius `max(n,R)`, so `lambda` is a supremum of
ball-local continuous functions and is lower semicontinuous: `{lambda <= r}` is
closed (Pi^0_1 in ball data). By Theorem B nothing better is possible on `A_d`:
every premise `P` with `P(G',q) => q <= p_u(G')` (for example `lambda(q) < 1`;
(IS) together with `rho < 1`; `p_c < p_(2->2)`; `p_c < p_q`; finite green-visit
counts) contains no neighbourhood of any `(G,q)` with `G in A_d`, `q > p_c(G)`.

## 6. Which groups lie in A_d

1. **Residually solvable groups with a covering abelian marking.** Let `G` be
   residually solvable (`cap_k G^(k) = 1`), and suppose the marking maps onto a
   free abelian group `Z^m`, `m >= 2`, with the `2d` elements `s_i^{±1}` pairwise
   distinct there. Then the solvable quotients `G/G^(k)` converge to `G` and are
   infinite and amenable. By Lemma 1, `p_c(G/G^(k)) <= p_c(Cay(Z^m, images))`.
   That is at most `1/2`, because two linearly independent images span a `Z^2`
   lattice subgraph. Examples are free groups, closed surface groups and
   right-angled Artin groups with their standard markings.
2. **Products with Z^2.** Let `G` be any LEA marked group, meaning a local limit
   of amenable marked groups, with finite approximants allowed. This includes
   every residually finite group and every residually amenable group. Then
   `G x Z^2` marked by `S ⊔ {e_1,e_2}` lies in `A_(d+2)`. The groups `G_k x Z^2`
   are infinite and amenable. They contain the `Z^2` lattice as a subgraph, so
   `p_c <= 1/2`. They converge to `G x Z^2`, because a word is trivial there
   exactly when its `S`-part is trivial and its `e_i`-exponent sums vanish.

So `A_d` contains nonamenable groups of every standard kind: `F_2`, surface
groups, `SL_3(Z) x Z^2`, and residually finite Kazhdan groups times `Z^2`. It
also contains `F_2 x Z^2`, which belongs to the rigid-decoration class
`F_2 x A`.

## 7. The class kill

**Invariant.** The pinned identity `p_u = p_c` on amenable approximants
([BK]), together with continuity of `p_c` ([EH]).

**Class.** Ball-local (open, Sigma^0_1) nonuniqueness certificates. These are
arguments that certify `p <= p_u(G)` from finitely many finite-ball statistics
with strict inequalities and an open parameter window, with the implication
valid on the amenable groups near `G`.

**Where every member dies.** At the transfer to an amenable approximant
`G_k in N_r(G)`. The certificate also holds for `G_k` at `p - eta/2`, which
forces `p - eta/2 <= p_c(G_k) -> p_c(G)`. So on `A_d` every such certificate
certifies only `p <= p_c(G)`, which says nothing towards `p_c < p_u`.

**Gate (what survives).** A certificate for `p_c(G) < p_u(G)` at `G in A_d`
must consume a hypothesis that is not a neighbourhood of `G` and that fails on
amenable groups arbitrarily close to `G`. Two kinds qualify:

* a quantitative closed spectral or isoperimetric input (`rho <= r < 1`,
  `h >= h_0`);
* infinite-information operator data (`||T_q|| <= M`, `lambda(q) <= r`, exact
  spectral radii of trees as in computer-assisted Schur tests).

The routes established so far (critical l2 gap, l^q gap, (IS), green-visit)
all have this non-open form. Theorem B is consistent with that and explains it.

**Not killed.**

* Arguments that use a closed quantitative expansion hypothesis essentially.
* Arguments on Cayley graphs outside `A_d`.
* (IS) itself. Theorem B is about the shape of certificates; it is not a
  counterexample.

**Novelty check.**

* `fpbs-l2-gap-class-closed-under-local-limits` item 4 is the operator special
  case: `limsup Gamma_M(G_k) <= p_c(G)` for amenable or finite approximants.
  Theorem B makes the statement for `p_u` itself and for every open certificate.
* The live-bus lemma `fpbs-fibre-truncation-pu-lower-semicontinuous` (another
  lane, not yet in this worktree) proves `p_u(G) <= liminf p_u(G_k)` along
  fibre-truncation towers, where `H_k` has finite index in an amenable normal
  `H`. (A1) shows that the inequality fails for general quotient towers, since
  `F^(k)` has infinite index. So the fibre hypothesis is load-bearing.
