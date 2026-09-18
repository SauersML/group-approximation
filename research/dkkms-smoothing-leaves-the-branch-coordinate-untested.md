---
rg: 2
id: dkkms-smoothing-leaves-the-branch-coordinate-untested
kind: claim
title: In the DKKMS 2-to-1 game a single constraint pins an A-label at a direction x only if its seed contains x, and a fresh smoothing contains a prescribed uniform direction with probability exactly (1 - 3 beta / 4)^k, so the six-flag Grassmann restriction gadget transfers only after paying that factor, while the seed weight at a typical A-vertex is measured to concentrate on one hyperplane
distinct_from:
  grassmann-restriction-test-is-99-percent-rigid: that proves 99 percent rigidity, with absolute constants, for the plain Grassmann restriction test on one ambient space; this shows that the DKKMS game is not that test, measures how far it is, and names the weight the transfer would have to pay.
  dkkms-grassmann-2to1-test-is-locally-99-percent-rigid: that is the open 99 percent statement itself; this is an obstruction to one named proof strategy for it, the six-flag Grassmann restriction gadget, together with the exact weight (1 - 3 beta / 4)^k that that gadget loses and a measurement of the conditional seed law. It makes no claim about other proofs of the rigidity statement.
  dkkms-2to1-instances-satisfy-selector-decoding-hypotheses: that reads the direction law as uniform off L' + H_U and uses it to feed the list decoder; this reads the same direction law from the other side and observes that a uniform direction almost never lies in a second seed space, which is what makes the direction untested.
  view-local-branch-selectors-are-gauge-blind: that is an information bound on the 3LIN gauge and concerns what a selector reads from the right-hand sides; this is a combinatorial property of the DKKMS edge law and concerns what the test itself reads from the A-label.
  spread-support-overlap-forces-non-expanding-small-sets: that turns overlapping supports into non-expanding small sets in the NO direction; this is a completeness-side statement about which hyperplanes of an A-space carry seed weight.
artifacts:
  - experiments/grassmann-99-rigidity-2026-09-18/seed_spread_dkkms.py
  - research/artifacts/dkkms-branch-coordinate-untested-proof-2026-09-18.md
---

**OPEN** (claimed 2026-09-18 via route `dkkms-branch-coordinate-untested-proof`;
**refuted at landing by referee lens 2** of the wave's three-lens stage, at the
import of Lemma 1 into Corollary 3 — the lemma is proved with an
existential/single-constraint quantifier and was then used with a universal
one. Lens 1 independently named the same step "the first step that does not
follow". The statement above has been narrowed to what Lemmas 1 and 2 actually
support; the sentences that were refuted are recorded under `## Attempts`, and
the full route is kept as the attempt artifact
`research/artifacts/dkkms-branch-coordinate-untested-proof-2026-09-18.md`.)

Notation is that of `dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`
(the verbatim ECCC TR16-198 Section 4.2 import): `U` a `k`-tuple of pairwise
variable-disjoint weight-3 equations, `X_U = F_2^(3k)`, `H_U` the span of the `k`
equation vectors, `V` the smoothing of `U` that keeps the `i`-th equation with
probability `1 - beta` and otherwise replaces it by a uniformly chosen one of its
three variables, `L' in Gr(X_V, l-1)` uniform, `L in Gr(X_U, l)` uniform with
`L > L'` and `L cap H_U = 0`, direction `x in L \ L'`.

## 1. Every link on a direction needs a seed through it

**Lemma 1.** Let `(U,L)` be an A-vertex and `x in L`. A constraint of `G_multi`
whose A-endpoint is `(U,L)` determines the value of the A-label at `x` only if
its seed `R` satisfies `x in R`. Any such seed has `R <= X_(V'')` for a smoothing
`V''` of `U`, hence `x in X_(V'')`.

*Proof.* The constraint at the copy with seed `R` says
`A(U,L)|_R = sigma'_R`; it constrains the value `A(U,L)(x)` only when `x in R`.
Seeds of `G_multi` are pairs `(V'', R)` with `R in Gr(X_(V''), l-1)` for a
smoothing `V''`, so `R <= X_(V'')`. QED

Lemma 1 is about **one** constraint. The node originally continued: "the only
way two constraints can pin the same value of an A-label is through a common
direction inside a seed space." That is **false** and is the step lens 2
refuted. By item 1 of `dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`
the constraint is exactly 2-to-1 and the unfolding `Fun(R_C) -> Fun(L)` is a
bijection, so an A-label is a linear functional on `L`; two constraints at the
**same** A-vertex `(U,L)` with distinct seeds `R1 != R2` are two distinct
hyperplanes of `L`, so `R1 + R2 = L` and together they pin `A(U,L)` at every
direction, with neither seed containing it.

What Lemma 1 does give is the hypothesis of the **six-flag gadget** of
`grassmann-restriction-test-is-99-percent-rigid`: that gadget certifies a
direction from an auxiliary `l`-space `N = P + <x,y> != L`, so its three
auxiliary seeds `P + <x>`, `P + <y>`, `P + <x+y>` each have to contain the
direction they certify, and each sits at a *different* target. Everything below
is stated for that gadget, not for agreement arguments in general.

**Lemma 2 (visibility of a direction).** Let `x` be uniform in `X_U` and let
`V''` be a fresh smoothing of `U`, independent of `x`. Then

```text
Pr[ x in X_(V'') ]  =  (1 - 3 beta / 4)^k      exactly.
```

*Proof.* `x in X_(V'')` iff at every block `i` the projection of `x` to block `i`
lies in the span of the variables that `V''` keeps there. The blocks are
independent. At one block, `V''` keeps the equation with probability `1 - beta`,
and then the condition holds; otherwise it keeps one uniform variable `v` and the
condition is `supp(x) cap block_i subset {v}`. For uniform `x` the three block
coordinates are uniform, so `|supp(x) cap block_i|` is `0, 1, 2, 3` with
probabilities `1/8, 3/8, 3/8, 1/8`, and the conditional probability that a
uniform `v` works is `1, 1/3, 0, 0`. Hence the per-block probability is
`(1 - beta) + beta (1/8 + (3/8)(1/3)) = 1 - 3 beta / 4`. QED

`2^(l-1-2k)`-uniformity of the direction is item 3 of
`dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`, so Lemma 2 applies
to the actual direction law up to that total variation distance.

**Corollary 3 (the six-flag transfer is exponentially lossy).** Let `x` be a
direction drawn from the game's own direction law at a target `U`, and let a
second constraint of `G_multi` at the same target, but at a **fresh** A-space
drawn from the edge law independently of `x`, be drawn from that law. Then

```text
Pr[ the second constraint's seed contains x ]  <=  (1 - 3 beta / 4)^k + 2^(l-1-2k).
```

(The seed is `(V'', R)` with `R <= X_(V'')`, so `x in R` forces `x in X_(V'')`;
apply Lemma 2 and the direction's `2^(l-1-2k)` distance from uniform.) The three
direction-certifying flags of the six-flag gadget are of exactly this kind —
each sits at the auxiliary `l`-space `N != L` with a smoothing drawn afresh — so
they carry total game weight at most `(1 - 3 beta / 4)^k + 2^(l-1-2k)`.
Consequently **the six-flag proof** of Theorem R of
`grassmann-restriction-test-is-99-percent-rigid` transfers to `G_multi` only with
`eta` replaced by `eta (1 - 3 beta / 4)^(-k)`, which carries no information once
`beta k -> infinity`. The DKKMS parameter regime takes `k` enormous compared
with `l` (item 7 of the membership node needs
`eps_k = exp(-k / exp(q l)) < p^2 / 8`), so `beta k -> infinity` for every fixed
`beta > 0`.

**Not a bound on other arguments.** Corollary 3 conditions on a second
constraint at a *fresh* A-space. It says nothing about two constraints at the
same A-vertex, where the cost is `O(1)` by the linear-algebra remark after
Lemma 1, and lens 2 measured the same-A-vertex analogue with this node's own
exact rational dynamic program: at `l = 3`, `beta = 1/2` it is
`0.2925, 0.3128, 0.2400, 0.2224, 0.1524, 0.1138, 0.1348` for `k = 2..8`, against
`(1 - 3 beta / 4)^k = 0.3906, 0.2441, 0.1526, 0.0954, 0.0596, 0.0373, 0.0233`;
the ratio *grows* from `0.75` to `5.8`, so `(1 - 3 beta / 4)^k` is not the
invariant under that conditioning.

## 2. What the test actually sees at an A-vertex

For a hyperplane `R < L` write `w(R | L)` for the conditional probability that
the edge's seed is `R` given that its A-space is `L`. Because the process picks
`R` first and then `L` uniformly among the admissible extensions, and the number
of admissible extensions `#{ L > R : L <= X_U, L cap H_U = 0 }` depends only on
`(l, k)` once `R cap H_U = 0`,

```text
w(R | L)  proportional to  S(R) := sum_(V'' : R <= X_(V'')) Pr[V''] / |Gr(X_(V''), l-1)| .
```

`S(R)` factorises over blocks apart from the `|Gr(X_(V''), l-1)|` term, which
sees only the number of smoothed blocks, so it is computed exactly by a dynamic
program.

**Measurement.** `seed_spread_dkkms.py` computes `E_L max_R w(R|L)` exactly for
the law above (only `L` is sampled; the sum over smoothings is exact, in
rationals). With `l = 3`, so that uniform spread would be `1/7 = 0.1429`:

```text
mean of max_R w(R|L), 80 A-vertices per point:
beta = 0.30:  k = 2,3,4,5,6,7,8  ->  0.341 0.398 0.417 0.518 0.499 0.579 0.644
beta = 0.50:  k = 2,3,4,5,6,7,8  ->  0.478 0.607 0.678 0.700 0.727 0.800 0.840

fraction of A-vertices whose dominant hyperplane IS the generating seed L':
beta = 0.50:  k = 2,3,4,5,6,7,8  ->  0.45  0.62  0.70  0.69  0.72  0.76  0.90
```

The median at `beta = 0.5, k = 8` is `0.946`, the maximum `0.9999`. The control
`beta = 0` returns exactly `1/(2^l - 1)` as it must. So the seed weight at a
typical A-vertex concentrates on a single hyperplane, that hyperplane is
increasingly often the generating seed, and both effects grow with `k` at fixed
`l`, which is the direction the DKKMS parameters go.

**Scope of the measurement.** These points are at `l in {2,3}` and `k <= 8`,
while `dkkms-grassmann-2to1-test-is-locally-99-percent-rigid` is quantified for
all `l >= l_0` with `k >= exp(ql)`. The concentration is therefore a trend, not
a check at an admissible parameter point; what carries the regime claim is the
analytic Lemma 2, not this table. (Recorded after referee lenses 2 and 3 both
flagged the extrapolation, 2026-09-18.)

**Reading.** At a typical A-vertex the test effectively asks one question:
"does the A-label vanish on *this* hyperplane?" The complementary coordinate,
which is exactly the branch bit of
`orientation-lifts-sandwich-2to1-game-values` item (5), is asked about with
vanishing weight.

## 3. Consequence: rigidity, if true, is a statement about folding

**Proposition 4 (conditional refutation of Grassmann-layer rigidity).** Suppose
that for a `1 - delta` fraction of the A-mass the conditional seed law puts
weight `>= 1 - xi` on the hyperplane `D(L) := L'` that generated `L` (the
artifact reports this fraction as the column `dom=seed` together with the share
`max_R w(R|L)`), and suppose the germ
`L |-> D(L)` is **folding-compatible**, meaning that for a `1 - delta'` fraction
of the A-mass the class label `sigma_C` can be chosen so that the unfolding
`lambda_(C,U)` satisfies `ker lambda_(C,U) cap L = D(L)`. Then `G_multi` has a
labelling of value `>= 1 - delta - delta' - xi` whose A-labels agree with
`hon_kappa(lambda)` on at most `2^(1-l) + d_kappa(lambda)` of the A-mass, for
every outer labelling `lambda` and every `kappa`. Moreover the *constant*
orientation `g_e := 1` and right bits `b := 0` give its orientation lift the same
value.

*Proof.* Take `tau_(V,R) := 0` at every seed and the class labels supplied by
folding-compatibility. An edge with A-space `L` and seed `R` is satisfied iff
`lambda_(C,U)|_R = 0` iff `R = D(L)`, which happens with conditional weight
`>= 1 - xi` on the good A-mass. For the distance: agreement with `hon_kappa(lambda)`
at a clean copy forces `lambda_(C,U)|_L = lambda_U|_L`, i.e. `lambda_U - 0`
restricts on `L` to the functional with kernel `D(L)`; since `D(L) = L cap X_V`
for the smoothing `V` that produced `L`, this requires `L cap X_V <= ker
(lambda_U)`, and for `L = L' + <x>` with `L'` uniform in `Gr(X_V, l-1)` that has
probability `<= 2^(1-l)` for every fixed `lambda_U`. For the lift: on every
satisfied edge the A-label vanishes on the seed and is non-zero on `L`, so its
value at the direction `x_e in L \ D(L)` is `1`; with `g_e = 1` the branch bit
`o_e = 1 xor 1 = 0` matches `b = 0`. QED

Proposition 4 is stated with its hypothesis, not asserted: folding-compatibility
is exactly the point where the construction can fail, and it is posted as an open
sub-statement. What Proposition 4 does establish is the **shape** of the
remaining question.

**What this kills — and what it does not.** What dies at Corollary 3 is the
**six-flag gadget** of `grassmann-restriction-test-is-99-percent-rigid`: it
certifies directions from auxiliary `l`-spaces and therefore pays
`(1 - 3 beta / 4)^(-k)`, which is vacuous at every admissible `(l,k)`. Smoothing,
which the DKKMS soundness analysis needs, is exactly what removes the links
*that* gadget runs on, and the seed share `E_L max_R w(R|L)` measured in
Section 2 is the invariant that tracks the loss.

This node originally claimed more: that *every* proof of
`dkkms-grassmann-2to1-test-is-locally-99-percent-rigid` importing a 99 percent
Grassmann agreement theorem dies at Corollary 3. **That was refuted** (lens 2,
2026-09-18): Lemmas 1 and 2 bound one configuration and do not quantify over
proofs, and the linear-algebra remark after Lemma 1 exhibits a two-query gadget
at a single A-vertex that pays `O(1)`. So the Grassmann-import lane is **not**
recorded here as dead; only its six-flag member is blocked. Whether some other
Grassmann agreement argument transfers is open.

**What this opens.** Proposition 4 is conditional on folding-compatibility of
the dominant germ, which is posted as an open sub-statement and is not settled
here. If it held, the selector hole
`efficient-branch-selector-on-proved-2to1-instances` would be solved on these
instances by the *constant* orientation `g_e = 1`, so that much of its open
content would be a question about folding classes with no algorithmic content.
That conditional reading is what this node records; it is not a claim that the
missing piece is not a rigidity theorem.

This neither proves nor refutes UGC, the Rich 2-to-1 Games Conjecture, or the
selector hole.

## Check

`python3 experiments/grassmann-99-rigidity-2026-09-18/seed_spread_dkkms.py`
(seed 20260918). It builds the DKKMS edge law verbatim, samples A-vertices from
it, and for each one computes `w(R|L)` for every hyperplane `R < L` exactly, in
rationals, by a dynamic program over the `k` blocks. Reported: mean, median, min
and max of `max_R w(R|L)` and the fraction of A-vertices whose dominant
hyperplane is the generating seed, over 60 samples per parameter point for
`k in {2,...,5}`, `l in {2,3}`, `beta in {0.1, 0.3, 0.5}`; then a trend in
`k in {2,...,8}` at `l = 3` with 80 samples per point; then the `beta = 0`
control, which must return `1/(2^l - 1)` and does.

## Attempts

- **2026-09-18: route `dkkms-branch-coordinate-untested-proof` (refuted by
  referee lens 2; kept as an attempt).** Wave `swarm-0917`, lane
  `e2-w2-ugc-selector-kill`. The route is kept in full as
  `research/artifacts/dkkms-branch-coordinate-untested-proof-2026-09-18.md`,
  with `experiments/grassmann-99-rigidity-2026-09-18/seed_spread_dkkms.py` as
  its artifact; the script reproduces its table exactly.

  *What was refuted.* The universal sentences attached to Corollary 3, and the
  title clause "every 99 percent Grassmann agreement theorem transfers only
  after paying that factor". Lemmas 1 and 2, the block dynamic program and the
  measurement are correct and are kept; the statement above has been narrowed
  to the six-flag gadget, which is what they support.

  *Lens 2 (refuted = true), verbatim:*

  > REFUTED at the import of Lemma 1 into Corollary 3 of
  > `dkkms-smoothing-leaves-the-branch-coordinate-untested` ... the lemma is
  > proved with an existential/single-constraint quantifier and is then used
  > with a universal one.
  >
  > What Lemma 1 proves: "a constraint of G_multi with A-endpoint (U,L) and
  > seed (V'',R) constrains A(U,L)(x) only if x in R". True, and it is about
  > ONE constraint. What the node then uses ("the only way two constraints can
  > pin the same value of an A-label is through a common direction inside a
  > seed space"; Corollary 3: "Every argument that pins the value of an A-label
  > at x needs such a second constraint"; title: "every 99 percent Grassmann
  > agreement theorem transfers only after paying that factor"; "What this
  > kills": "Every proof ... dies at Corollary 3") is a statement quantified
  > over all pairs of constraints and all proofs. That upgrade is false on the
  > node's own imported hypotheses. By item 1 of
  > `dkkms-2to1-instances-satisfy-selector-decoding-hypotheses` the constraint
  > is exactly 2-to-1 and unfolding Fun(R_C) -> Fun(L) is a bijection, i.e.
  > A-labels are linear functionals on L. Hence two constraints at the SAME
  > A-vertex (U,L) with distinct seeds R1 != R2 (both hyperplanes of L) pin
  > A(U,L) on R1 + R2 = L, therefore at every direction x in L, with neither
  > seed required to contain x. Lemma 2's factor (1 - 3beta/4)^k is the cost of
  > a second seed containing x only under Corollary 3's conditioning "a second
  > constraint at the same TARGET U" (a fresh A-space, which is the right
  > conditioning for the specific six-flag gadget, whose auxiliary flags sit at
  > N = P + <x,y> != L). It is not the cost under the same-A-vertex
  > conditioning that an agreement/rigidity argument is free to use.
  >
  > The node's own artifact contradicts the universal version. Re-running
  > `seed_spread_dkkms.py` reproduces E_L max_R w(R|L) = 0.478 (k=2) ... 0.840
  > (k=8) at l=3, beta=1/2, so the non-dominant hyperplanes of one L keep
  > conditional weight 0.52 ... 0.16. Reusing that script's exact rational DP,
  > the quantity Corollary 3 claims to bound, but conditioned on the same
  > A-vertex — Pr[ a second independently drawn constraint's seed contains the
  > direction x | L ] with R1 ~ w(.|L), x uniform in L \ R1 — is 0.2925,
  > 0.3128, 0.2400, 0.2224, 0.1524, 0.1138, 0.1348 for k = 2..8 (l=3,
  > beta=1/2, 30 A-vertices/point), against (1 - 3beta/4)^k = 0.3906, 0.2441,
  > 0.1526, 0.0954, 0.0596, 0.0373, 0.0233. The ratio grows with k (0.75 ->
  > 5.8), i.e. the measured weight decays far more slowly than the asserted
  > rate, so "(1 - 3beta/4)^k" is not the invariant and a two-query gadget at
  > one A-vertex pays O(1), not exp(Theta(beta k)). The load-bearing sentence
  > of the whole result — "the lane that hoped to close this hole by proving 99
  > percent rigidity is dead at Corollary 3" — is therefore an unfilled step,
  > not a theorem.

  *Lens 1 (refuted = false for the selector hole) named the same step
  independently, verbatim:*

  > THE FIRST STEP THAT DOES NOT FOLLOW: the universal sentences attached to
  > Corollary 3 — "Every argument that pins the value of an A-label at x needs
  > such a second constraint", and in the claim node "Every proof of
  > `dkkms-grassmann-2to1-test-is-locally-99-percent-rigid` that imports a 99
  > percent agreement or rigidity theorem for the Grassmann poset ... dies at
  > Corollary 3". Lemmas 1-2 bound the weight of one specific configuration (a
  > second seed through a prescribed direction); they do not quantify over all
  > proofs, and the node itself concedes rigidity could come from the folding
  > classes. What IS established is the narrower, correct statement: the
  > six-flag gadget's flags carry game weight ~(1-3beta/4)^k, so THAT route
  > loses eta -> eta(1-3beta/4)^(-k), vacuous since item 7 forces k large.

  *Secondary defects the referees recorded, now fixed in this node or its
  artifact.*
  1. The route quoted the measurement as "rises from 0.365 at k=2 to 0.831 at
     k=8"; the artifact prints `0.4776` and `0.8397`. This claim node had the
     numbers right; the route file was stale, and is corrected.
  2. The route wrote the parameter bound as `k >= exp(ql)(3l + O(1)) log 2`,
     which is not what item 7 of the membership node gives
     (`(2l + 7) log 2 + 6 log(2/gamma)`). Corrected; the conclusion is
     unaffected.
  3. Corollary 3 is proved for a smoothing `V''` drawn independently of `x`
     but was applied where `V''` is conditioned on containing a hyperplane of
     `L`; the artifact's own `min` column (`0.1429`, exactly uniform at some
     A-vertices) shows the conditional version is false pointwise. The
     aggregate game-weight statement the union bound needs is unaffected. Also
     unstated: the edge law renormalises over `L cap H_U = 0`, which tilts the
     smoothing law by `j`, in the safe direction.
  4. Proposition 4(c)'s `2^(1-l)` assumes `lambda_U|_(X_V)` is not identically
     zero; if it is, the ratio is `1`. Noted in the artifact. Proposition 4 is
     conditional anyway.
  5. The measurement is at `l in {2,3}`, `k <= 8`, far from `k >= exp(ql)`; it
     is a trend, not a check at an admissible point. Noted above.

  *What to do next.* Either close the gap — bound the same-A-vertex seed-sharing
  weight, which the measurement above suggests is `Theta(1)` rather than
  `(1 - 3 beta / 4)^k`, so the universal statement looks false rather than
  merely unproved — or restate the node as the six-flag statement only, which
  is what the body now does, and re-referee it.
