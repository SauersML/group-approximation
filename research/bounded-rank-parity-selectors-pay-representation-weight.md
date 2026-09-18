---
rg: 2
id: bounded-rank-parity-selectors-pay-representation-weight
kind: claim
title: On planted-noise YES instances every branch selector whose per-edge bit function factors through at most R arbitrary parities of the right-hand sides, faithful or leaking, has honest orientation-lift value at most one half plus the unclean mass and the square root of the inverse B-degree, the collapse fraction and 2^(2R+1) (1-2eta)^W, where W is the number of source equations needed to represent a difference of branch directions; so on DKKMS-shape neighbourhoods over a source without short anchored parities every selector of parity rank at most eta W is one-half blind
invalidates: []
distinct_from:
  view-local-branch-selectors-are-gauge-blind: that kills selectors whose per-edge view is a set of right-hand-side coordinates spanning no parity of window variables beyond H_U (condition (F)), at views J_e of arbitrary size, and it lists leaking and global views as survivors; this covers arbitrary parities and needs no faithfulness at all, but only up to rank R, so the two classes are incomparable (J_e = { j : vars(m_j) disjoint from vars(U_e) } is faithful of rank Theta(m), out of reach here; a leaking rank-1 view is out of reach there). It also prices the leaking case by the weight of the representation it uses, and bounds the orientation-lift value itself rather than the agreement rate hon_t(o), which alone does not bound the lift because the lift keeps the majority branch at each B-vertex.
  efficient-branch-selectors-list-decode-honest-outer-labels: that kills every polynomial-time selector with an honest witness, conditionally on NP not in RP, through a Fourier list decoder; this is unconditional, allows unbounded computation, and is therefore restricted to selectors of bounded parity rank, which is exactly the resource the decoding argument does not bound. Theorem 2 of that node (P = NP builds a selector) shows no unconditional kill can cover unbounded rank.
  high-advantage-selector-witnesses-decode-good-outer-labellings: that works at lift value near 1 against locally honest patchwork witnesses and needs NP not in RP; this works at every value above one half, against one planted honest witness, and needs no complexity assumption.
  parity-leaking-branch-selectors-reach-near-perfect-completeness: that is the open survivor asking for a global parity-leaking selector; this prices its leakage, showing the leak must have rank above eta W per constraint, so what is left is not leakage but decoding.
  unique-constraints-orient-at-most-half-of-a-fiber: that is the combinatorial injectivity wall inside one fibre; this is a bias bound for a computed branch bit on an instance ensemble.
artifacts:
  - experiments/ugc-parity-leak-2026-09-18/check_parity_leak_bias.py
---

**OPEN** (demoted 2026-09-18 by referee audit before it ever stood: lenses 1
and 2 refuted Lemma 3 and the Corollary. Lemma 3 is literally false as stated —
its proof treats only `1 <= |T| <= N` and never excludes `T = empty`, which is
exactly the collapsing case `x_e + x_f in Lambda_(ef)`, `W_(ef) = 0` — and the
Corollary's hypothesis "a `1 - rho` weight of B-vertices has **all** its pairs
with `W_(ef), g_(ef) > W`" is then satisfied by no B-vertex at all, since Step 6
of the route counts `2^k - 1` collapsing same-window partners per constraint, so
`rho = 1` and the stated bound is `>= 1`, i.e. vacuous. Lens 2 additionally
refuted the class-containment claim against
`view-local-branch-selectors-are-gauge-blind`. Route, proof and artifact are
kept; they are an attempt. See `## Attempts`.)

Route (not yet sound as written):
`bounded-rank-parity-selectors-representation-weight-proof`. Theorems 1, 2 and
Lemma 3 are self-contained linear algebra, one conditional-bias computation and
one second moment. The artifact checks Theorem 1 exhaustively and measures every
parameter of Theorem 2 on random sources. Theorem 1, Steps 0-4 and the
geometric parameters were checked line by line by all three lenses and hold; the
defect is confined to Lemma 3's quantifier and the Corollary's hypothesis.

## Setting

**Source and ensemble.** A 3LIN instance is `I = (M, b)` with rows
`m_1, ..., m_m in F_2^n` of weight 3 and right-hand sides `b in F_2^m`. Fix
`M`. The **planted-noise ensemble** `Y(M, eta)` draws `t` uniform in `F_2^n` and
`v` with independent `Bernoulli(eta)` coordinates and sets `b := M t + v`. Every
draw is a YES instance: `t` violates exactly the equations of
`Viol := supp(v)`, so `val(I) >= 1 - |v|/m = 1 - eta - o(1)` with probability
`1 - exp(-Omega(m))`.

This is the planted form of the gauge of
`view-local-branch-selectors-are-gauge-blind`: there the randomness is `z` with
`I -> I^z`, here it is the planted assignment. The difference is the point of
this node. The gauge fixes the violation pattern `v` — it maps `Viol(t)` to
`Viol(t+z)` unchanged — which is exactly why a selector that reads parities of
`b` outside its window escaped that kill. In `Y(M, eta)` the pattern `v` is
itself random, and a read parity is right only when it meets `Viol` evenly.

**Window family.** As in `grassmann-composed-2to2-coarsenings-are-satisfiable`
and `dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`: `U` runs over
legitimate `k`-tuples of pairwise variable-disjoint equations, `X_U` is the
space of vectors supported on `vars(U)` (dimension `3k`),
`H_U = Span(m_j : j in U)` (dimension `k`), `h_U(m_j) = b_j`. A-vertices are
`(U, L)` with `L in Gr(X_U, l)` and `L meet H_U = 0`; B-vertices are `(V, L')`
with `L' in Gr(X_V, l-1)` and `X_V <= X_U` for every neighbour; a constraint `e`
joins `(U, L)` to `(V, L')` with `L' < L`, and `x_e in L \ L'`.

**Honest labelling and lift.** For an assignment `t` the honest labelling gives
`(U, L)` the restriction `t|_L` — the unfolding of the honest class label at a
**clean** copy, item 5 of
`dkkms-2to1-instances-satisfy-selector-decoding-hypotheses` — and gives
`(V, L')` the restriction `t|_(L')`. An orientation gives each constraint a map
`o_e : Fun(L') -> F_2`; the lift `U_o` has right labels `(tau, beta)` and
accepts `(sigma, (tau, beta))` iff `sigma|_(L') = tau` and
`sigma(x_e) xor o_e(tau) = beta`. Write

```text
A_e := <t, x_e> xor o_e(t|_(L'_e)),
```

which does not depend on the representative `x_e in L \ L'`, because the two
preimages of `tau` differ at every point of `L \ L'`. Let `S` be the set of
clean constraints (window satisfied by `t`), `w_v` the weight at the B-vertex
`v`, `eps_out` the weight of unclean constraints and

```text
X_v := sum_(e in S, e at v) w_e (-1)^(A_e).
```

For the honest left labelling every clean constraint at `v` projects to the same
B-label `t|_(L'_v)`, so the joint maximum over `(tau, beta)` that defines the
lift value is attained at that `tau`, and

```text
hon-lift(o, t) <= eps_out + sum_v (w_v(S) + |X_v|)/2 <= 1/2 + eps_out + (1/2) sum_v |X_v|.
```

(The joint maximum is the correct reading of item (3) of
`orientation-lifts-sandwich-2to1-game-values`, per the 2026-09-18 audit of that
node; for honest left labellings the two readings agree.)

## The class: rank-`R` parity selectors

A selector is a rule `I -> o`. It is a **rank-`R` parity selector** if for every
constraint `e` there are a subspace `C_e <= F_2^m` and a function `Phi_e`,
depending only on `M` and `e`, with

```text
o_e(tau) = Phi_e( (<c, b>)_(c in C_e), tau ),
```

such that `C_e` contains the coordinate vectors `1_j`, `j in U_e`, of the
window's own equations (so the folding offsets `h_(U_e)` are free), and

```text
dim( C_e / (C_e meet Span(1_j : j in U_e)) )  <=  R.
```

No efficiency, uniformity or complexity assumption is made on `Phi_e`. The class
contains:

* every view-local selector reading at most `R` equations, **whether or not**
  its view is parity-faithful, since a coordinate is a parity: so it contains
  the **bounded-view** members of `view-local-branch-selectors-are-gauge-blind`,
  including its *leaking* ones, which that node had to exclude. It does **not**
  contain that node's class outright: Theorem 1 there quantifies over views
  `J_e` of arbitrary size, gated only by faithfulness (F), and
  `J_e = { j : vars(m_j) meet vars(U_e) = empty }` satisfies (F) with parity
  rank `Theta(m)`. The two class kills are **incomparable** — this one reaches
  leaking views at bounded rank, that one reaches faithful views at unbounded
  rank;
* every selector affine in `b` with `b`-independent coefficients, in particular
  *solve the system by Gaussian elimination with fixed pivots and evaluate the
  resulting `t^` at `x_e`* (`R = 1`);
* every selector reading `R` arbitrary syndromes, checksums or aggregates of the
  right-hand sides, however global their support.

It does not contain selectors whose dependence on `b` has rank above `R`. That
restriction is unavoidable: by Theorem 2 of
`efficient-branch-selectors-list-decode-honest-outer-labels`, `P = NP` produces
a selector of honest lift value `1 - eta`, so no unconditional statement can
reach unbounded rank.

## The invariants

For two constraints `e != f` at one B-vertex `v` put
`Lambda_(ef) := L'_v + H_(U_e) + H_(U_f)` and
`P_(ef) := vars(U_e) union vars(U_f)`, and write `theta := 1 - 2 eta`.

* **Leak weight** `W_(ef) := min { |c \ (U_e union U_f)| : c in C_e + C_f,
  M^T c in x_e + x_f + Lambda_(ef) }`, `= infinity` if there is no such `c`.
  In words: the least number of source equations outside the two windows whose
  sum represents the **difference of the two branch directions** modulo the seed
  space and the two folding spaces.
* **Null weight** `g_(ef) := min { |c \ (U_e union U_f)| :
  c in C_e + C_f, c \ (U_e union U_f) != 0, M^T c in Lambda_(ef) }`.
* **Collapse.** The pair collapses if `W_(ef) = 0`, that is
  `x_e + x_f in Lambda_(ef)`; `kappa` is the weight of collapsing pairs.
* **Pair leak profile**
  `Lambda(theta) := E_v E_(e != f at v)[ min(1, 2^(2R+1) theta^(W_(ef))) ]`,
  so `Lambda(theta) <= kappa + 2^(2R+1) E[ theta^(W_(ef)) ; W_(ef) >= 1 ]`.

## Theorem 1 (conditional bias: leaking costs weight)

Fix `M`, a B-vertex `v`, constraints `e != f` at `v` and a rank-`R` parity
selector. Draw `(t, v)` from `Y(M, eta)`, condition on `t` satisfying every
equation of `U_e union U_f`, and on the observation

```text
O := ( t|_(L'_v), (<c, b>)_(c in C_e + C_f) ),
```

which determines both `o_e` and `o_f`. Put `x := x_e + x_f`. Then:

1. **(Blind.)** If no `c in C_e + C_f` has `M^T c in x + Lambda_(ef)`, then
   `E[ (-1)^(<t, x>) | O ] = 0` exactly, for every selector with that
   measurement space, efficient or not.
2. **(Leaking.)** Otherwise, if `2^(2R) theta^(g_(ef)) <= 1/2`,

   ```text
   | E[ (-1)^(<t,x>) | O ] | <= 2^(2R) theta^(W_(ef)) / (1 - 2^(2R) theta^(g_(ef)))
                             <= 2^(2R+1) theta^(W_(ef)).
   ```

Item 1 with `C_e` spanned by coordinates and `x = x_e` is the gauge-blindness
lemma. Item 2 is the new part, and it is what that kill left open. The
mechanism: if `M^T c = x + lambda` with `lambda in Lambda_(ef)` then

```text
<t, x> = <c, b> xor <c, v> xor (a function of t|_(L') and of b|_(U_e union U_f)),
```

so the selector's prediction is correct exactly when **an even number of the
equations it combines are violated by the planted assignment**. Each additional
equation in the combination costs a factor `theta`.

## Theorem 2 (the lift value, not the agreement rate)

Under the hypothesis of Theorem 1 at every pair, for every rank-`R` parity
selector,

```text
E[ hon-lift(o, t) ] <= 1/2 + E[eps_out] + (1/2) sqrt( E_v[1/D_v] + Lambda(theta) ),
```

where `1/D_v := sum_(e at v)(w_e/w_v)^2` is the inverse participation ratio of
the B-vertex and `E[eps_out] = Pr_U[t violates an equation of U] <= k eta`. The
proof is Cauchy--Schwarz over B-vertices and one second moment inside each, with
Theorem 1 supplying every off-diagonal term.

This bounds the **orientation-lift value of the honest labelling**. The bound of
`view-local-branch-selectors-are-gauge-blind` is on the agreement rate
`hon_t(o)`, and `hon_t(o) <= 1/2` does not bound the lift value, because the
lift keeps `max(a_v, 1 - a_v)` at each B-vertex: a selector that is
*consistently wrong* at every B-vertex has agreement rate `0` and lift value
`1`. The second moment above is what rules that out, and it needs the pair
invariant `W_(ef)`, not the single-constraint one. This is a gap in what that
node *concludes* about the selectors it does reach — not a claim to reach more
of them; on class the two kills are incomparable, as above.

## Lemma 3 (when the source has no short representation)

Say `M` is **`N`-expanding** if every set `T` of at most `N` rows spans at least
`2|T| + 1` variables, and that a pair of windows is **`P`-isolated** if no
equation outside `U_e union U_f` has two or more variables in `P_(ef)`.

If `M` is `N`-expanding and the pair is `P`-isolated then
`W_(ef), g_(ef) > N`.

*Proof.* Let `T` be disjoint from `U_e union U_f` with `1 <= |T| <= N` and
`sum_(j in T) m_j` supported inside `P_(ef)` (which contains
`x_e + x_f + Lambda_(ef)`, since `L' <= X_V <= X_(U_e)`). Every variable of `T`
outside `P_(ef)` has degree at least 2 in `T`, so counting incidences
`3|T| >= 2(|vars(T)| - |vars(T) meet P_(ef)|) + |vars(T) meet P_(ef)|`, and
`N`-expansion gives `|vars(T)| >= 2|T| + 1`, whence
`|vars(T) meet P_(ef)| >= |T| + 2`. But `P`-isolation gives
`|vars(T) meet P_(ef)| <= |T|`. Contradiction. QED

**Proposition 4 (random sources, first moment).** Let the rows be independent
uniform weight-3 vectors with `m = C n`, and let the windows be sampled as
DKKMS samples them. Then for every fixed `k` and every
`W = W(n) = o(log n / log log n)`, the probability that the sampled B-vertex
carries a pair with `W_(ef) <= W` or `g_(ef) <= W` is `O_(C,k)(n^(-1/2))`.
*Sketch.* Union over `|T| = j <= W` and over pairings of the incidence slots of
`T`: a configuration with `a` incidences into `P` and the rest matched in pairs
contributes `C(m,j) (3j)^(3j/2) n^(-s) (p/n)^(3j-2s)` with `2s = 3j - a` and
`p = |P| <= 6k`, whose maximum over `s` is
`(C^j/j!)(3j)^(3j/2) max((p^3/n^2)^j, n^(-j/2))`. The sum over `j <= W` is
dominated by `j = 1`, of order `k^3 n^(-2)`, as long as `(3W)^(3/2) = o(n^(1/2))`.
The constants are not optimised and this proposition is **not** part of the
established statement; it says only that the hypothesis of Lemma 3 is the
generic case. The artifact measures the `j <= 3` part directly.

## Corollary (DKKMS-shape neighbourhoods)

Take the folded DKKMS Grassmann instances of
`dkkms-2to1-instances-satisfy-selector-decoding-hypotheses` over a source for
which a `1 - rho` weight of B-vertices has all its pairs with
`W_(ef), g_(ef) > W`, and the planted ensemble `Y(M, eta)`. Import verbatim item
3 of that node: *"Given `(w_e, a_e) = ((V,L'), U)`, the direction `x_e` is
uniform on `X_U \ (L' + H_U)`"*. Then, writing `D = (2^(3k) - 2^(l-1+k))/2^(l-1)`
for the number of constraints per B-vertex and window,

* `E_v[1/D_v] <= 2^(l-3k+1)`;
* `kappa <= (2^k - 1)/(D - 1) <= 2^(l-2k+1)`, under the genericity hypothesis
  (G) that for `U_e != U_f` at one B-vertex
  `(L' + H_(U_e) + H_(U_f)) meet X_(U_e) = L' + H_(U_e)`, which holds whenever
  the equations of `U_f` outside `U_e` use variables outside `vars(U_e)`;
* `Lambda(theta) <= kappa + rho + 2^(2R+1) theta^W`.

Hence for every rank-`R` parity selector,

```text
E[ hon-lift(o, t) ] <= 1/2 + k eta + (1/2) sqrt( 2^(l-3k+1) + 2^(l-2k+1) + rho + 2^(2R+1) theta^W ).
```

Read the limits in this order, which is the DKKMS order:

1. `n -> infinity` with `(k, l, eta, R)` fixed. On a source with
   `W(n) -> infinity` and `rho(n) -> 0` — Proposition 4, or any explicit
   `N`-expanding `P`-isolated family — the last two terms vanish, since
   `theta^W -> 0` for every fixed `eta > 0`. The admissible rank grows too: any
   `R <= eta W(n)` suffices.
2. `k -> infinity` with `l` fixed: the first two terms vanish.
3. `eta -> 0` with `k eta -> 0`, which is the regime DKKMS needs anyway (item 7
   of the membership node fixes `2 k eps_3 <= min(gamma/2, p^2/8)`).

So for every `delta > 0` there are `k`, `l` and `eta` such that on all large
instances of this ensemble **no rank-`eta W(n)` parity selector has honest lift
value above `1/2 + delta`**, whatever computation it performs.

## What this changes for the selector hole

`efficient-branch-selector-on-proved-2to1-instances` asks for a polynomial-time
orientation with YES lift value `1 - eta'` *on every YES input*. The planted
ensemble is a YES input family, so a selector answering the hole must, on almost
every constraint, read a measurement space of rank above `eta W(n)` beyond its
own window's offsets, **or** win through a labelling that is not the honest one.

Against the survivor list of `view-local-branch-selectors-are-gauge-blind`:

* survivor (a), *parity-leaking or global selectors*: bounded-rank leakage is
  now dead, faithful or not, and the reason is quantitative. To gain at a pair,
  the leak must represent `x_e + x_f` by few source equations, and a locally
  sparse source has no such representation (Lemma 3, Proposition 4); with many
  equations the read parity is almost unbiased. So rank must be spent not on
  *leaking* but on *decoding*: combining many long, individually unbiased,
  parities of `b` into a posterior on `t`. That is syndrome decoding of the
  source code, and it is precisely where
  `efficient-branch-selectors-list-decode-honest-outer-labels` takes over,
  conditionally on `NP not in RP`. The two kills now meet: below rank
  `eta W(n)`, unconditional; above it, conditional.
* survivor (b), unclustered menus: untouched (one planted witness is used here).
* survivor (c), non-honest witnesses: untouched at every rank, and now the only
  shelter that neither kill reaches. It is the open node
  `view-local-selectors-beat-one-half-through-non-honest-witnesses`.

Concretely, for `parity-leaking-branch-selectors-reach-near-perfect-completeness`
this is a sharpened necessary condition: its selector's leakage must have rank
above `eta W(n)` per constraint, a quantity that grows with the instance, and
its certificate must survive the decoding kill, so it must be non-honest.

## Check

`python3 experiments/ugc-parity-leak-2026-09-18/check_parity_leak_bias.py`,
default seed 20260918, about 9 s.

1. **Theorem 1, exhaustively.** 12 trials at `n = 9`, `m = 10`, `eta = 0.15`,
   rank 2. Every `(t, v)` is enumerated with its exact weight and grouped by the
   observation cell. Result: 8 blind measurement spaces, in each of which the
   conditional bias is `0` in **every** cell, and 4 leaking ones, in each of
   which the bias respects the bound. Worst violation `0.000000`.
2. **Short representations of a sparse source.** `n = 400`, `m = 800`, `k = 3`,
   `l = 2`, 60 windows. Number of cosets of `L' + H_U` in `X_U` reachable by at
   most 3 equations outside `U`, per window: `0.017` at `|T| = 2` and `0.033` at
   `|T| = 3`, out of `2^(2k-l+1) = 32` cosets. So `W > 3` at 95% of windows
   already at `n = 400`, and the few exceptions are the 3-row configurations
   that fail `2|T| + 1` expansion.
3. **Collapse fraction.** Measured `kappa = 0.02834` over 2.45 million ordered
   pairs of constraints, against `0.02834` predicted by the imported direction
   law. Exact agreement.
4. **Concrete selectors.** `n = 90`, `k = 3`, `l = 2`, `eta = 0.10`, 120
   B-vertices of mean degree 248. Honest lift values: oracle (knows the planted
   `t`; not polynomial time) `1.0000`; **Gaussian elimination on the whole
   system, then evaluate** `0.5095`; **solve the window and the seed label, then
   evaluate** `0.5242`; random orientation `0.5258`. Both natural global
   selectors sit at the floor. The third is a rank-0 selector, so Theorem 2
   covers it; at these toy sizes (`W = 4`, `eta = 0.1`, `k = 3`) the bound is
   vacuous, and the run also prints it along the asymptotic axis `W -> infinity`
   at fixed `(k, l, eta) = (10, 2, 0.002)` and rank 3, where it falls
   `1.000, 1.000, 0.749, 0.521` at `W = 100, 400, 1600, 6400`, converging to
   `1/2 + k eta + 2^((l-2k+1)/2)/2`.

Check 4 is evidence, not proof, for the Gaussian selector: its parity rank is
`n`, far above the theorem's reach. It is the first measurement in this graph of
what the natural global selector actually achieves.

## Not covered

* **Rank above `eta W(n)`**, in particular every selector that really reads all
  of `b`. Theorem 2 of the decoding node shows no unconditional argument can
  cover it; the conditional kill does.
* **Non-honest witnesses.** The bound is on the honest labelling's lift value.
* **Menus.** One planted `t` is used; the McDiarmid step of the gauge-blindness
  node, which extends its statement to equivariant menus of subexponential size,
  is not carried out for this ensemble.
* **Proposition 4's constants**, and whether the smooth regular Gap3Lin source
  that DKKMS composes with has `W(n) -> infinity` and admits planted YES inputs.
  Random sparse sources do. Posted as a live need.
* **NO instances.** Nothing here concerns soundness, which orientation lifts
  inherit for free.

This neither proves nor refutes UGC, the Rich 2-to-1 Games Conjecture, or the
selector hole.

## Attempts

* **First posting of the route, refuted on referee audit (2026-09-18).** Posted
  ESTABLISHED on the strength of
  `bounded-rank-parity-selectors-representation-weight-proof`; two of three
  referee lenses refuted it (verdicts `91955d7d`, `cd2394aa`; lens 3 `5af349ff`
  voted survives but flagged the same two slips as repairable). The node is back
  to OPEN. Three defects, the first two load-bearing:

  - **Lemma 3 is false as stated.** "If `M` is `N`-expanding and the pair is
    `P`-isolated then `W_(ef), g_(ef) > N`." Step 5 of the route (lines 203-220)
    takes `T` disjoint from `U_e union U_f` with `1 <= |T| <= N` and derives
    `|vars(T) meet P| >= |T| + 2` from unique-neighbour expansion against
    `<= |T|` from `P`-isolation. That contradiction rules out `1 <= |T| <= N`
    only. The case `T = empty` is precisely the collapsing pair
    `x_e + x_f in Lambda_(ef) = L' + H_(U_e) + H_(U_f)`, where a `c` supported
    inside `U_e union U_f` already represents the difference and `W_(ef) = 0`.
    `N`-expansion and `P`-isolation are hypotheses on `M` and on the window
    geometry outside the windows; they say nothing about collapse. Proposition 4
    inherits the same defect.
  - **The Corollary's hypothesis is satisfied by no B-vertex, so the Corollary
    is vacuous.** It reads "a `1 - rho` weight of B-vertices has **all** its
    pairs with `W_(ef), g_(ef) > W`". But Step 6 of the same route (lines
    238-245) counts, for every constraint `e` at every B-vertex, the `2^k`
    same-window partners `f` with `x_f in x_e + L' + H_U`; each of the `2^k - 1`
    partners other than `e` has `W_(ef) = 0`. So for `k >= 1` no B-vertex
    satisfies the hypothesis, `rho = 1` for every source, and the bound
    `1/2 + k eta + (1/2) sqrt(2^(l-3k+1) + 2^(l-2k+1) + rho + 2^(2R+1) theta^W)`
    is `>= 1`. The node contains, side by side, a lemma asserting
    `W_(ef) > N` for every pair and an exact count plus an artifact measurement
    (`check_collapse`, `kappa = 0.02834 = (2^k - 1)/(D - 1)`) showing a constant
    fraction of pairs with `W_(ef) = 0`. That `kappa` is added *separately* in
    `Lambda(theta) <= kappa + rho + 2^(2R+1) theta^W` is the tell: collapse was
    meant to be excluded from `rho` and never was. The Corollary is the only
    place the "tends to `1/2`" conclusion is delivered, so as written the
    headline kill is not established.
  - **The class-containment claim against the gauge node is false** (lens 2).
    The "The class" section and the `distinct_from` entry assert that the
    rank-`R` class contains "every view-local selector reading at most `R`
    equations ... so it contains the whole class of
    `view-local-branch-selectors-are-gauge-blind`", and that this is "a gap in
    the class kill of that node, not only a strengthening of it". But Theorem 1
    of the gauge node quantifies over views `J_e` of **arbitrary** size, gated
    only by faithfulness (F): `Q_e meet X_(U_e) = H_(U_e)`. No cardinality bound
    appears. Counterexample: `J_e = { j : vars(m_j) meet vars(U_e) = empty }`
    satisfies (F) while `|J_e| = m - O(k)`, i.e. parity rank `Theta(m)`, far
    above any fixed `R`. The two class kills are **incomparable**, not nested.

  **The repair for the first two is one clause each and the final numeric bound
  is unchanged**: state Lemma 3 as "`W_(ef) = 0` or `W_(ef) > N`" (`g_(ef)` is
  unaffected, since `c' != 0` forces `|T| >= 1`), and define `rho` over
  non-collapsing pairs only, since collapse is already priced by `kappa` in
  `Lambda(theta)`. The intended hypothesis is already visible in the
  `Lambda(theta) <= kappa + 2^(2R+1) E[theta^(W_ef); W_ef >= 1]` bullet. The
  third needs the containment language replaced by an incomparability statement
  in both the prose and the `distinct_from` entry. Until those edits are made
  and re-refereed the node does not stand.

  Secondary overstatements to fix in the same pass, none of them the first gap:

  - Theorem 2 bounds `E[hon-lift(o,t)]` over the planted ensemble, so the
    Corollary's closing "on all large instances of this ensemble no rank-`eta
    W(n)` parity selector has honest lift value above `1/2 + delta`" is an
    average statement, not a per-instance one; the node's own "Not covered"
    section admits the McDiarmid step is missing. The downstream use against the
    selector hole survives on Markov, since one bad YES instance suffices.
  - Check 4's remark that the Gaussian-elimination-with-fixed-pivots selector
    "has parity rank `n`, far above the theorem's reach" contradicts the node's
    own class definition and the code: the pivot pattern depends only on `M`, so
    `t^ = A b` is linear in `b` and `<t^, x_e> = <A^T x_e, b>` is a single
    parity — the selector is rank 1 and fully covered. This under-claims the
    result.
  - The stated limit order "`n`, then `k`, then `eta`" does not work (lens 3):
    after `n -> infinity` at fixed `eta` the residue is
    `1/2 + k eta + (1/2) sqrt(2^(l-3k+1) + 2^(l-2k+1))`, and `k -> infinity`
    blows `k eta` up. The working order is `k` (or `k = l -> infinity`), then
    `eta ~ delta/k`, then `n`, with `R <= eta W(n)` still growing. The claim's
    own closing quantifier is already correct.
  - The `kappa` "measurement" of check (3) is a same-window counting identity —
    `check_collapse` samples one window per B-vertex and returns
    `(2^k - 1)/(D - 1)` by construction — so its "exact agreement" with the
    imported direction law is a tautology, and the cross-window case, the only
    one needing genericity (G), is untested. That file's docstrings also predict
    a different formula (`2^(l-1+k)/(2^(3k) - 2^(l-1+k)) = 0.0323`) and claim of
    check (2) that "None is ever found" while the run reports `0.017` and
    `0.033`.

  **What all three lenses agree holds** and is worth keeping: Theorem 1 in both
  items (Step 1's posterior computation — `E_U <= K <= C` gives `t|_Lambda` from
  `O`, the `C_0` measurements contribute a uniform factor `2^(-dim C_0)`
  independent of `v'`, and `s = dim K' <= dim(C/E_U) <= 2R`; Step 2's exact zero
  in the blind case; Step 3's weight-enumerator ratio with numerator
  `<= 2^s theta^(W_ef)` and denominator `>= 1 - (2^s - 1) theta^(g_ef)`); Step
  0's per-vertex imbalance bound under the joint maximum over `(tau, beta)`,
  including its correct critique that the gauge node's `hon_t(o)` is an
  agreement rate and not the lift value; Step 4's Cauchy--Schwarz and Jensen and
  the off-diagonal use of Theorem 1; Lemma 3's incidence count for `|T| >= 1`;
  the geometric parameters `D = (2^(3k) - 2^(l-1+k))/2^(l-1)`,
  `E_v[1/D_v] <= 1/D`, the genericity argument (G) and `kappa <= 2^k/(D - 1)`;
  and the quoted quantifiers of items 3 and 5 of
  `dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`. The artifact runs
  clean and reproduces every number (bias exactly `0` in all 8 blind cells, all
  4 leaking cells within bound, worst slack `0.000000`; `kappa 0.02834` vs
  predicted `0.02834`; gauss `0.5095`, localsolve `0.5242`, oracle `1.0000`).
