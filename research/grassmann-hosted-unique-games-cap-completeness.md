---
rg: 2
id: grassmann-hosted-unique-games-cap-completeness
kind: claim
title: Gap-UG[1-eta, s] is in P on unique games whose constraint graph is loop-free, weighted-regular and Grassmann-dominating with density rho, for every eta < rho(q-1)/(q X(s)), so Grassmann-hosted UG hardness caps completeness at 1 - rho(q-1)/(q X(s)) and asking for it at completeness tending to 1 is exactly asking for P = NP
distinct_from:
  spectral-gap-ratio-reductions-cannot-prove-ugc: that is the general gate in the ratio lambda_2/(1 - opt) with no graph family named and no converse; this instantiates it on the one family the H3 denial proposes, supplies the constant from an exact spectral computation, and adds the converse, so on that family the statement is an equivalence with P = NP rather than a one-way gate.
  grassmann-graphs-have-constant-normalized-spectral-gap: that is the graph-theoretic input, with no complexity content; this is the complexity consequence and uses that claim as a black box.
  unique-games-hard-on-non-sse-grassmann-constraint-graphs: that asks for the reduction; this asks instead whether asking for it at density one and completeness tending to 1 is asking for P = NP, and where the completeness ceiling for Grassmann-hosted reductions sits.
  affine-ug-easy-on-globally-hypercontractive-graphs: that solves affine unique games over Grass(n,l) at every constant completeness by global hypercontractivity, and only affine ones; this covers arbitrary permutation constraints, needs no hypercontractivity, and bites only at completeness above 1 - rho(q-1)/(q X(s)). The two are complementary and together leave only non-affine constraints at bounded completeness.
  unique-games-hard-at-completeness-one-half: that is the proved hardness at completeness (1-eps)/2 on unrestricted constraint graphs; this is a completeness ceiling for Grassmann-hosted instances, and 1/2 sits below the ceiling, so the two do not conflict.
  unique-games-gap-admits-polynomial-time-algorithm: that is the open refutation of UGC on all instances; this is a polynomial-time algorithm on one named constraint-graph family at high completeness only, and refutes no conjecture.
artifacts:
  - experiments/grassmann-spectral-gap-2026-09-17/check_grassmann_gap.py
---

**OPEN** (demoted 2026-09-18 at landing: all three swarm-0917 referee lenses
returned `refuted` --- see `## Attempts`). The proof is kept as the attempt
artifact `research/artifacts/grassmann-completeness-cap-proof-2026-09-18.md`.
It rests on `grassmann-graphs-have-constant-normalized-spectral-gap` (also
demoted to OPEN on 2026-09-18, proof kept as
`research/artifacts/grassmann-spectral-gap-recursion-proof-2026-09-18.md`) and
on bullet (K1) of `spectral-gap-ratio-reductions-cannot-prove-ugc` (itself
resting on the imported AKKSTV rounding). Everything else is elementary. Replay:
`experiments/grassmann-spectral-gap-2026-09-17/check_grassmann_gap.py`.

All three referees checked Theorems A, B and C line by line and found them
sound; the step they refuted is **Theorem D**, which is independent of A--C and
is marked below. Restoring A--C therefore needs Theorem D restated, not
repaired machinery.

*Setting.* Notation of `spectral-gap-ratio-reductions-cannot-prove-ugc`: for
`s < 1`, `X(s)` is the least integer `x >= 3` with `C_A log(x)/x < 1 - s`, where
`C_A` is the absolute constant of the AKKSTV rounding. Write `Gr_q(n,l)` for the
Grassmann graph and `A_1`, `d_1 = q[l][n-l]` for its adjacency and degree.

**Definition (Grassmann-hosted with density `rho`).** A unique game `U` is
*Grassmann-hosted with density `rho > 0`* if its weighted constraint graph `W`
lives on `V_l(F_q^n)` for some `q >= 2`, `1 <= l <= n-1`, and

1. `W` is loop-free;
2. all weighted degrees of `W` are equal, to `d` say;
3. `W >= (rho d/d_1) A_1` entrywise.

The DKKMS/KMS Grassmann test --- pick a uniformly random pair `L, L'` with
`dim(L cap L') = l - 1` --- is Grassmann-hosted with `rho = 1`. More generally
every `GL_n(F_q)`-invariant edge law supported on that relation is the uniform
one, hence `rho = 1` (Theorem 5 of the graph claim); and any edge law that puts
at least a `rho` share of its weight uniformly on that relation qualifies.

**Theorem A (algorithm and gate).** Fix `s < 1` and `rho > 0`. There is a
deterministic polynomial-time algorithm that solves `Gap-UG[1 - eta, s]`
restricted to Grassmann-hosted instances of density `>= rho`, for every

```text
eta  <  rho (q - 1) / (q X(s)),      in particular for every eta < rho/(2 X(s)).
```

Consequently, if `f` is a polynomial-time reduction from a language `L` with

* `x in L`  =>  `f(x)` is Grassmann-hosted of density `>= rho` and
  `opt(f(x)) >= 1 - eta`,
* `x notin L`  =>  `opt(f(x)) <= s`,

and `eta < rho(q-1)/(q X(s))`, then `L in P`.

**Theorem B (completeness ceiling).** Unless `P = NP`, every reduction from an
NP-hard language to `Gap-UG[c, s]` whose YES outputs are Grassmann-hosted of
density `>= rho` has

```text
c  <=  1 - rho (q - 1)/(q X(s))  <=  1 - rho/(2 X(s)).
```

The ceiling depends only on `s`, `rho` and `q`; it does not move with `n`, `l`,
the alphabet size, or the number of vertices. So completeness on Grassmann
constraint graphs is bounded away from `1` by an absolute constant.

**Theorem C (equivalence).** The statement

> (H3) for every `eta, delta > 0` there is a polynomial-time reduction from
> 3SAT to unique games that are Grassmann-hosted with density `1`, with YES
> value `>= 1 - eta` and NO value `<= delta`

is **equivalent to `P = NP`**. Forward: Theorem A with `s = delta` and any
`eta < 1/(2X(delta))`. Backward: for every `delta > 0` there is a
Grassmann-hosted unique game of value `<= delta` (a counting argument, step (4)
of the route) and one of value `1` (all constraints the identity); hard-wire
both and decide 3SAT in polynomial time.

**Theorem D --- REFUTED 2026-09-18 (was: "the small-set-expansion premise is an
equivocation").** Struck by all three referee lenses. It read: by Theorem 4 of
`grassmann-graphs-have-constant-normalized-spectral-gap` every set in
`Gr_q(n,l)` has `Phi(S) >= (1 - mu(S))(q-1)/q` with the zoom sets attaining it,
hence (bullet 1) "`Gr_q(n,l)` is not a YES instance of `Gap-SSE(eta, delta)` for
any `eta < (1-delta)(q-1)/q`: it **is** a small-set expander in the sense used by
`small-set-expansion-hypothesis` and by Raghavendra--Steurer", and (bullet 3)
"the non-expanding sets contribute nothing beyond the single number `lambda_2`".

Both are false. `Gap-SSE` is a promise problem: "not YES" is not "NO". The sense
those sources use is the NO side, `Phi_G(delta) >= 1 - eta` (near-perfect
expansion), and `Gr_q(n,l)` fails it by a constant --- the zoom-ins have
`mu(Z_x) = [l]/[n] -> 0` with `Phi(Z_x) = q^(l-1)/[l] -> (q-1)/q`. So the graph
is neither a YES nor a NO instance; it lies in the promise gap. And equality in
`Phi(S) >= (1 - mu)lambda_2` only puts `1_S - mu` in the second eigenspace; a
Ramanujan graph with the same `lambda_2` has `Phi(S) = 1 - o(1)` at
`mu(S) = o(1)`, so the extremal small sets are strictly more structure than
`lambda_2`.

What is left, and what the referees agree can be restated in its place:

* `Gr_q(n,l)` is **not** a YES instance of `Gap-SSE(eta, delta)` for any
  `eta < (1 - delta)(q-1)/q`, and is not an expanding NO instance either;
* so A3's premise --- "Grassmann graphs are not small-set expanders" --- is
  **correct** as the literature means it, and the KMS counter-signal is
  untouched;
* the premise is nevertheless **inert** for H3: what Theorems A--C turn against
  near-perfect completeness is the global gap `lambda_2 = 1 - 1/q + o(1)`, and
  that argument never consults the small-set profile. The kill and the small-set
  question are independent, and this claim settles only the first.

Theorem D is *not* used by Theorems A, B or C, and its failure does not touch
them; it is recorded here as the step that must be rewritten before this node
can be re-proposed.

**Decomposition of H3 into independently failing prerequisites.** H3 is the
conjunction of

* **(P1) host** --- the YES outputs are loop-free, weighted-regular and
  Grassmann-dominating with a density `rho_0 > 0` fixed over the family;
* **(P2) completeness** --- YES value `>= 1 - eta` with `eta -> 0` at fixed
  soundness;
* **(P3) soundness** --- NO value `<= delta` for some fixed `delta < 1`;
* **(P4) source** --- the reduction is polynomial time from an NP-hard language.

Theorems A--C say `(P1) and (P2) and (P3) and (P4) => P = NP`. So at most three
of the four survive in a world with `P != NP`, and each may be dropped on its
own:

* **drop (P2).** Completeness `<= 1 - rho_0(q-1)/(q X(delta))` is untouched, and
  this is where the proved world lives: `two-to-two-games-theorem` and
  `unique-games-hard-at-completeness-one-half`. *Falsifier of the kill here:*
  none --- the kill simply does not apply.
* **drop (P1) by density.** `rho_0 = 0` is a real escape: a perfect matching
  inside `Gr_q(n,l)` is loop-free, weighted-regular, supported on Grassmann
  edges, and has `lambda_2 = 0`. So a test whose edge law concentrates on a
  sparse sub-structure of the Grassmann relation evades Theorem A --- but it is
  then not the DKKMS test, whose law is uniform on that relation. *Falsifier:*
  exhibit a DKKMS-shape reduction whose output edge law has
  `rho = o(1)` and still supports the DKKMS soundness analysis.
* **drop (P1) by regularity.** The bipartite containment host `V_(l-1) u V_l`,
  which is what an *orientation lift* of a bipartite 2-to-1 game runs on, is
  biregular but not regular when the two levels differ in size, and (K1) quotes
  a regular hypothesis (its survivor (S1)). Theorem 6 of the graph claim gives
  that host a gap `> 1 - q^(-1/2)`, so only the regularity hypothesis, not the
  spectrum, stands between this kill and the orientation-lift lane. *Falsifier
  / open transfer:* show that the AKKSTV rounding, or a value-preserving
  regularization, applies to biregular bipartite constraint graphs. That would
  extend Theorems A--C verbatim to
  `parity-leaking-branch-selectors-reach-near-perfect-completeness`, which asks
  for exactly (P1)--(P4) on an orientation lift, and kill it the same way.
* **drop (P3).** Soundness near `1` is the `(1-eps, 1-gamma)` regime, which is
  not a UGC statement.

**Consequence for the H3 route.** `ugc-from-grassmann-graph-unique-games-hardness`
remains logically valid --- H3 does imply UGC --- but it is not a decomposition
of UGC into anything smaller: by Theorem C its premise is `P = NP`, which
already implies UGC on its own. So H3 is not a hole to be closed on the way to
UGC; it is a strictly stronger statement, and effort spent on it is effort spent
on `P != NP`. The same applies to everything the graph lists as waiting on H3 ---
`finite-moment-pairing-2to1-hardness`, `smooth-design-rich-2to1-hardness`,
`unique-games-np-hard-below-the-padding-line` and `unique-games-conjecture`
itself: each of them already follows from `P = NP`, so none of them gains
anything from the H3 branch. The two dead attempts recorded on H3 stopping at
completeness
`1/2` are not an artifact of branch selectors: Theorem B forbids any
Grassmann-hosted reduction from passing `1 - rho(q-1)/(q X(delta))`, whatever
the technique.

**What would falsify this claim.** (i) A unique game on `Gr_q(n,l)` with
`opt >= 1 - eta`, `eta < (q-1)/(q X(s))`, on which the AKKSTV rounding returns
value `<= s` --- that is, an error in the imported Theorem 2.4 or in (K1).
(ii) A pair `(q, n, l)` with `lambda_2(Gr_q(n,l)) <= (q-1)/q` --- excluded by
Theorem 2 of the graph claim and its replay. (iii) For Theorem C's converse, a
proof that no unique game on any Grassmann graph has value below `delta` ---
excluded by the counting argument in step (4) of the route.

## Attempts

* **Exact gap into the (K1) ratio gate, plus the counting converse
  (2026-09-18, swarm-0917, scale-shifter; refuted at landing, demoted from
  ESTABLISHED to OPEN).** All three referee lenses returned `refuted`, each of
  them at Theorem D. Verdicts `96bc7dfa`, `124cfa4b` and `17e004e3`, posted on
  `unique-games-hard-on-non-sse-grassmann-constraint-graphs`.

  *What the referees confirmed.* Theorems A, B and C stand as written, checked
  by hand by all three: the exact gap `lambda_2 = [n]/(q[l][n-l]) > (q-1)/q`,
  the domination lemma `lambda_2(W) >= c d_1 lambda_2(Gr)/d` and its
  `GL_n`-transitivity corollary `rho = 1`, the shape hypotheses (K1) quotes, the
  AKKSTV bridge --- `X(s) >= 3` puts `eta/lambda <= 1/3 < 1/e` where
  `t log(1/t)` is still increasing, so passing from the SDP value to `opt` costs
  nothing --- and the Chernoff-plus-union-bound converse (`k = ceil(2/delta)`,
  `d_1 > 6k ln k`). The replay `check_grassmann_gap.py` prints `ALL PASS`, exit
  0, and `bin/cairn check` exits 0. Lens 3 recorded the cross-check that the
  closed form reproduces the classical `theta_1 = q^2[l-1][n-l-1] - 1` and that
  `[n] - (q-1)[l][n-l] = (q^l + q^(n-l) - 2)/(q-1) > 0`. So "H3 restricted to
  density-one, loop-free, weighted-regular Grassmann hosts is equivalent to
  `P = NP`" was judged to go through.

  *The step that failed.* Theorem D bullet 1 (proved in step (5) of the route,
  now `research/artifacts/grassmann-completeness-cap-proof-2026-09-18.md`)
  inferred from "`Gr_q(n,l)` is not a YES instance of `Gap-SSE(eta, delta)`"
  that "it **is** a small-set expander in the sense used by
  `small-set-expansion-hypothesis` and by Raghavendra--Steurer". That is a
  promise-problem non-sequitur and a quantifier flip: the sense those sources
  use is the NO side, `Phi_G(delta) >= 1 - eta` --- this repo's own
  `small-set-expansion-hypothesis` node states the RST corollary
  (arXiv:1011.2586 Cor. 3.3) as "UGC restricted to instances whose constraint
  graph has *near-perfect* expansion of sets of measure in `[delta, M delta]`".
  The route's own Theorem 4 refutes the substituted reading: lens 1 recomputed
  `mu(Z_x) = 9.54e-7`, `Phi(Z_x) = 0.500000` at `q=2, n=40, l=20` and
  `mu = 7.0e-8`, `Phi = 0.666667` at `q=3, n=30, l=15`; lens 2 got
  `Phi = 0.5161` at `mu = 0.030` (`q=2,n=10,l=5`) and `0.5714` at `mu = 0.0017`
  (`q=2,n=12,l=3`); lens 3 got `mu = 3.05e-5`, `Phi = 0.500015` at
  `q=2,n=30,l=15`. For every `eta < 1/q` the graph is neither a YES nor a NO
  instance: it sits in the promise gap. Hence A3's premise is true as standardly
  meant, the KMS counter-signal ("the 2-to-2 graphs always have small
  non-expanding sets") is *confirmed* by Theorem 4 rather than refuted, and the
  charge of "equivocation" was itself the equivocation.

  *Second defect, same step.* "The non-expanding sets contribute nothing beyond
  the single number `lambda_2`: they are its equality cases." Equality in
  `Phi(S) >= (1 - mu)lambda_2` gives only `1_S - mu` in the second eigenspace. A
  Ramanujan or random regular graph with the same `lambda_2 = 1 - 1/q + o(1)`
  has `Phi(S) = 1 - o(1)` on every set of measure `o(1)`, so attaining the floor
  at `mu = o(1)` is strictly more structure --- a large near-top eigenspace,
  i.e. high threshold rank at `1 - lambda_2`. That is precisely the DKKMS/KMS
  phenomenon and what the Bafna--Minzer line consumes.

  *Third, smaller, unfilled (lens 2).* The equivalence with `P = NP` is proved
  only at density `rho = 1`, while the parent claim asks for "(weighted)
  Grassmann 2-to-1 constraint graphs of the DKKMS shape". The route itself
  constructs the `rho -> 0` escape and names the biregular containment host ---
  the host an orientation lift actually runs on --- as surviving through (S1).
  The `distinct_from` entry on the parent that says the parent "stays open only
  in the completeness window that gate leaves" dropped the density escape; it
  has been corrected there.

  *Lens 3's consistency finding.* The established sibling
  `spread-support-overlap-forces-non-expanding-small-sets` concludes that
  Grassmann view graphs with codimension-one adjacency cannot be NO outputs of
  an SSEH reduction for `eta` below theta, using exactly these zoom sets. The
  numbers agree with Theorem 4; the old Theorem D's conclusion did not, and the
  `distinct_from` gloss calling the two "consistent" has been narrowed on the
  graph claim to agreement of the numbers only.

  *Repair all three referees agree on.* Delete the "it is a small-set expander
  in the sense used by SSEH/RS" clause and the mirroring paragraph on the graph
  claim; keep only "not a YES instance of `Gap-SSE(eta, delta)` for
  `eta < (1-delta)(q-1)/q`, and not an expanding NO instance either --- it lies
  in the promise gap"; retitle Theorem D to "the small-set-expansion premise is
  true but inert"; and restate the parent's bullet 3 as "A3's expansion premise
  is correct but inert: the kill comes from `lambda_2`, not from small-set
  expansion". Theorems A--C, the exact gap, the floor, the equalities and the
  replay need no change. That rewrite has been applied to the bodies above as a
  record of the referee finding; it has **not** been re-refereed, so this node
  and `grassmann-graphs-have-constant-normalized-spectral-gap` stay OPEN until a
  fresh pass survives.
