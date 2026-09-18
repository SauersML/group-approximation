---
rg: 2
id: ugc-hardness-reductions-need-epsilon-dependent-size-exponent
kind: claim
title: Under ETH, a 3SAT reduction proving near-perfect UG hardness, SSE hardness, or 2-to-1 hardness consumed by the BKM noise test must have output size exponent tending to infinity (at least c eps^(-1/6), c/eta, c eps^(-1/6)/2)
distinct_from:
  abs-subexponential-unique-games-and-sse-algorithms: that is the imported algorithm; this is the quantitative size gate derived from it, carried through the BKM noise test and through SSE with an exact-measure repair.
  low-label-threshold-rank-reductions-cannot-prove-ugc: that kills reductions whose YES outputs have low label-extended threshold rank, unless P = NP; this kills every fixed-exponent reduction, whatever its spectrum, under ETH.
  spectral-gap-no-outputs-cannot-prove-ugc: that is a NO-side spectral invariant; this is an invariant of the reduction's size, with no structural hypothesis on its outputs.
  sticky-cylinder-gadget-compositions-cannot-prove-sseh: that kills bounded-arity outer compositions by stickiness, unconditionally; this kills fixed-exponent reductions to SSE of every shape, under ETH.
  perfect-completeness-rich-2to1-tractable-skeletons-are-in-p: that kills YES outputs carrying tractable skeletons; this kills fixed-exponent reductions to Gap-Rich[1, eta] of every kind.
---

**ESTABLISHED (conditional statement: ETH is a hypothesis of the theorem, not
assumed as a fact).** Proof: `ugc-size-exponent-gate-proof`, from
`abs-subexponential-unique-games-and-sse-algorithms` and the BKM Section 5
construction imported in `rich-2to1-conjecture-is-equivalent-to-ugc`.

**ETH.** For some `c_0 > 0`, 3SAT on `n` variables has no deterministic
`2^(c_0 n)`-time algorithm. A reduction family has **size exponent `A`** if,
for all large `n`, it maps a formula on `n` variables to an output with at most
`n^A` weighted constraints (or edges), in time polynomial in its output.
Absolute constants `c_1, c_2, c_3, gamma_1, eta_1, eps_1 > 0` come from the
absolute `O(·)` constants of ABS.

**(G1) Unique games.** Let `gamma < gamma_1`. Suppose a reduction maps
satisfiable formulas to unique games of value `>= 1 - gamma`, and unsatisfiable
ones to value `<= 1/2`, with alphabet `k <= n^(o(1))` and size exponent `A`.
Then under ETH `A >= c_1 gamma^(-1/6)`. In particular the exponents
`A(gamma)` of any reductions witnessing `unique-games-conjecture` are unbounded
as `gamma -> 0`. This is ABS's own remark (p. 2), made precise.

**(G2) Every 2-to-1 hardness that reaches UGC through the BKM noise test.**
Call a 2-to-1 instance class `P` (left alphabet `[2l]`) **BKM-certified at
`(eps, m, eta, l)`** when the Section 5 test of Braverman--Khot--Minzer, with
alphabet `m` and noise `eps`, maps instances of value `<= eta` to unique games
of value `<= eps`, and `2 eta + 3 eps <= 5 eps`. Let `eps < eps_1`. Suppose a
reduction maps 3SAT to `Gap-P_l[1 - eta, eta]` with at most `n^A` edges. Then
under ETH `A >= c_2 eps^(-1/6)`.

Consequences, using that the routes certify BKM soundness:

* Rich 2-to-1, in both the `1 - eta` form and the perfect-completeness `1`
  form: BKM Section 5.2 certifies `m >= m_0(eps)`, `eta <= eta_0(m, eps)` and
  `l >= l_0(m, eta, eps)`.
* The smooth-design and finite-moment classes: certified by the soundness
  transfers those two routes consume, `noise-test-sound-on-smooth-design-rich-inputs`
  and, for the finite-moment class, `finite-density-moments-control-noisy-tails`.

So any reductions feeding `ugc-from-rich-2to1-via-bkm-equivalence`,
`rich-2to1-from-perfect-completeness`, `ugc-from-smooth-design-rich-2to1` or
`ugc-from-finite-moment-pairing-hardness` have size exponents `A(eta)` that
are unbounded as `eta -> 0`.

**(G3) Small-set expansion.** Let `eta < eta_1`, `delta > 0`, and suppose a
reduction outputs **regular** graphs (weighted, self-loops allowed) with at most
`n^A` vertices, with `Phi_G(delta) <= eta` on satisfiable formulas and
`Phi_G(delta) >= 1 - eta` on unsatisfiable ones, where
`Phi_G(delta) = min_(mu(S) = delta) Phi(S)`. Then under ETH `A >= c_3 / eta`.
So the exponents of reductions witnessing `small-set-expansion-hypothesis` on
regular graphs are unbounded as `eta -> 0`.

**Invariant.** The size exponent `A`.

**Where every member dies.** At decoding. ABS's threshold-rank dichotomy
decodes the output in time `exp(k N^(O(eps)))`. For outputs of size `N = n^A`
with `A < c eps^(-1/6)`, that time is `2^(o(n))`, so 3SAT itself would be
solved in subexponential time.

**Related, not yet landed here.** A concurrent session posted a two-sided
threshold-rank gate for SSE reductions: YES and NO outputs need rank above
`Z^alpha` under ETH. Its invariant is spectral. This node's invariant is size,
and it needs no rank hypothesis. How the two combine is not worked out here.

**Survivors.**

* (S1) Reductions whose size exponent grows at least like `eps^(-1/6)`: parallel
  repetition with a number of rounds that tends to infinity, or a Label Cover
  source whose size is `N^(f(eta))` with `f -> infinity`.
* (S2) Reductions from sources that have no fully exponential lower bound, or a
  failure of ETH.
* (S3) For G3 only, irregular output graphs. ABS footnote 5 asserts that the
  degree-weighted extension holds but does not prove it.
* (S4) Hardness at completeness bounded away from 1. The 2-to-2 theorem at
  completeness `~1/2` escapes this gate, since ABS note that their algorithm
  needs completeness near 1. So in any route that starts from
  `two-to-two-games-theorem`, the forced blow-up has to be paid at the
  completeness-amplification step, from `1/2` to `1 - gamma`.
