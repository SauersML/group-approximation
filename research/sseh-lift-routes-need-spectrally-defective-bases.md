---
rg: 2
id: sseh-lift-routes-need-spectrally-defective-bases
kind: claim
title: A reduction proving Gap-SSE(eta, 1/q) whose outputs are label-extended graphs of q-label unique games puts its source in P unless the hard core of its constraint graphs has lambda_2 < 5 X(eta) sqrt(eta) on both sides, and if the NO bases moreover carry the multiscale profile on [1/q, tau] their Cheeger cut lies outside the small-set window
distinct_from:
  spectral-gap-ratio-reductions-cannot-prove-ugc: that gates the YES outputs of reductions to Gap-UG, where the YES case is a near-satisfying labeling by definition; this gates reductions to Gap-SSE, where the YES case is an arbitrary small non-expanding set, and the transport needs the load-rigidity lemma plus the necessity half of the lift theorem, giving a two-sided conclusion (both YES and NO bases in the hard core) that the UG gate does not state.
  lifts-over-multiscale-expanders-expand-unless-ug-value-large: that splits the NO case of a lift reduction into a value prerequisite and a base-profile prerequisite; this constrains the base spectrally on both sides and shows the base profile must jump across the window, which that claim leaves open.
  lift-yes-sets-are-labelings-unless-the-base-loses-a-cut: that is the unconditional rounding lemma for one set; this is the reduction-level gate it feeds, and it is conditional on P != NP.
  sse-reductions-need-high-threshold-rank-on-both-sides: that is an OPEN attempt about the threshold rank and square certificates of the OUTPUT graph; this is about the second eigenvalue of the BASE of a lift, uses a different algorithm (AKKSTV rounding, not eigenspace enumeration), and does not depend on the repair that attempt needs.
  single-density-expansion-forces-the-multiscale-profile: that is the missing one-graph propagation lemma, from expansion at density 1/q to expansion across [1/q, tau]; this is the reduction-level gate that consumes it in step (B3), and everything through (B2) is independent of it.
  unique-games-on-expanding-constraint-graphs-are-easy: that is the imported rounding algorithm; this is a statement about what a small-set-expansion reduction can emit.
  sticky-cylinder-gadget-compositions-cannot-prove-sseh: that kills fibred bounded-arity compositions at the NO case by non-expansion of the output; this kills spectrally expanding bases at the YES case by an algorithm, and is conditional on P != NP.
artifacts:
  - experiments/sse-lift-base-gate-2026-09-18/check_load_rigidity.py
---

**OPEN.** Submitted as ESTABLISHED on 2026-09-18 and set back after refereeing
(swarm-0917): two of three lenses refuted the headline step (B3), which imports
the multiscale profile (N2) as if a lift reduction were forced to supply it on
its NO outputs. It is not. See `## Attempts`. The attempted proof is kept as
`sseh-lift-base-spectral-gate-proof`; it now carries
`single-density-expansion-forces-the-multiscale-profile` (**OPEN**) as the
missing prerequisite, so the gate is blocked exactly at that step.

*What is not in doubt.* Items (B0), (B1), (B2) and (B4) below were checked
step by step by all three lenses and survive: the two-sided spectral gate
`lambda_2(H) < 5 X(eta) sqrt(eta)` on the hard core of a support-spread lift
reduction, and its Galois form. Only (B3), (P4) and the shape conclusion drawn
from them are conditional on N2, which is why they are now marked as such
in place. Inputs: `lift-yes-sets-are-labelings-unless-the-base-loses-a-cut`
(the YES-side rounding, **established**),
`lifts-over-multiscale-expanders-expand-unless-ug-value-large`
(the NO-side necessity, established), `spectral-gap-ratio-reductions-cannot-prove-ugc`
(the AKKSTV gate, established), and the standard Cheeger inequality
`h_H <= sqrt(2 lambda_2(H))`.

*Setting.* Fix an integer `q >= 2` and `eta in (0, eta_0]`, where
`eta_0 = (40 X_0)^(-2)` and `X_0 = X(1/2)` is the absolute AKKSTV threshold
below; put `delta = 1/q`. A **lift reduction** for `Gap-SSE(eta, delta)` from a
language
`L` is a polynomial-time map `x -> U(x)`, where `U(x)` is a `q`-label unique
game on a loop-free regular multigraph `H(x)`, whose emitted SSE instance is the
label-extended graph `G(x) = L(U(x))` on `V(x) x [q]`, with

```text
x in L      ==>  Phi_G(1/q) <= eta,
x not in L  ==>  Phi_G(1/q) >= 1 - eta.
```

The reduction is **support-spread** if for every `x in L` every `S` of measure
`1/q` in `G(x)` with `Phi_(G(x))(S) <= eta` has `mu(supp S) >= sqrt(eta)/2`,
where `supp S = {v : S_v != emptyset}`. Let `X(s)` be the AKKSTV threshold of
`spectral-gap-ratio-reductions-cannot-prove-ugc`, the least integer `x >= 3`
with `C_A log(x)/x < 1 - s`; `X` is non-decreasing, so `X(eta) <= X_0 = X(1/2)`
for `eta <= 1/2`. Put `theta = 5 X(eta) sqrt(eta) <= 5 X_0 sqrt(eta)`.

**(B0) NO side, unconditional.** `x not in L` implies `val(U(x)) <= eta` **and**
`Phi_(H(x))(1/q) >= 1 - eta`. Both are the necessity half of
`lifts-over-multiscale-expanders-expand-unless-ug-value-large` (labeling sets
and cylinders). So the base of every NO output is itself a near-perfect small-set
expander at exactly the SSE density.

**(B1) YES side, unconditional.** `x in L` implies at least one of
`val(U(x)) >= 1 - 5 sqrt(eta)`, `lambda_2(H(x)) <= 4 sqrt(eta)`, or
`mu(supp S) < sqrt(eta)/2` for the witness `S`. This is the spectral
trichotomy of
`lift-yes-sets-are-labelings-unless-the-base-loses-a-cut`.

**(B2) Gate.** Let the reduction be support-spread. The set
`E = {x : lambda_2(H(x)) >= theta}` is decidable in polynomial time, and
`L n E` is decidable in polynomial time: on `x in E` run AKKSTV on `U(x)` and
accept iff the returned labeling has value `> eta`. Consequently:

- if `lambda_2(H(x)) >= theta` for every `x in L`, then `L in P`;
- more sharply, unless `L in P`, the language `L` stays hard on
  `{x : lambda_2(H(x)) < theta}`, so **both** YES and NO instances of the hard
  core have `lambda_2(H) < theta = 5 X(eta) sqrt(eta)`.

*Where every member dies.* At the YES output of the reduction, before any
soundness analysis: the invariant is `lambda_2(H)/(1 - val(U))` of the base,
read off the lift by load rigidity.

**(B3) Shape of the base, conditional on N2.** Take `x` in the hard core with
`x not in L`. By (B0) and (B2),

```text
Phi_H(1/q) >= 1 - eta        and       lambda_2(H) < 5 X(eta) sqrt(eta).
```

By Cheeger there is `B` with `mu(B) <= 1/2` and
`Phi_H(B) <= sqrt(2 lambda_2(H)) < sqrt(10 X(eta)) eta^(1/4) < 1/2` for `eta`
small. So `mu(B) != 1/q`. If moreover the base satisfies the multiscale profile
(N2) of `lifts-over-multiscale-expanders-expand-unless-ug-value-large`, namely
`Phi_H(A) >= 1 - nu/24` for `mu(A) in [1/q, tau]` with `nu <= 1/2`, then

```text
mu(B) > tau        or        mu(B) <= nu delta / 6.
```

*Under N2*, the Cheeger cut of the base does not sit inside the small-set
window, and the base's expansion profile has to jump from `>= 1 - nu/24`
throughout `[delta, tau]` to `O(eta^(1/4))` at a scale outside it. The noisy
cube realizes the first alternative (its sparsest cut is a half-cube at measure
`1/2`), and by `f2-cayley-sse-exact-census-small-k` its optimal non-expanding
sets at every density are exactly subcubes.

**The N2 hypothesis is not removable by (B0).** The necessity half forces only
`Phi_H(W) >= 1 - eta` at measure exactly `1/q` — item (4) of
`lifts-over-multiscale-expanders-expand-unless-ug-value-large` says "N1 at level
`nu` and N2 **at scale `1/q`**" — while N2 proper quantifies over all of
`[1/q, tau]` and is a hypothesis of that claim's sufficiency half. So from (B0),
(B2) and Cheeger the only unconditional output is `mu(B) != 1/q`. Closing the
gap is `single-density-expansion-forces-the-multiscale-profile` (**OPEN**).

**(B4) Galois form.** In `Gal(G, K, mu)` the lift is `Cay(G, mu)`, the base is
the Schreier graph on `G/K` and `q = [G : K]`
(`galois-unique-game-value-is-transversal-expansion`). For `G = F_2^N` and `K`
of index `2^c` the base is `Cay(F_2^c, w)` for the pushforward weight, and

```text
lambda_2(Cay(F_2^c, w)) = 2 min_(a != 0) w({b : a . b = 1}) / W.
```

So (B2) says: in the hard core there is a nontrivial character `chi` of `F_2^N`
that is **trivial on `K`** with `w({g : chi(g) = -1})/W < 2.5 X(eta) sqrt(eta)`.
Equivalently the output Cayley graph has a hyperplane of measure `1/2` and
expansion `O(sqrt(eta))` *containing the fibre subgroup `K`*. This is strictly
more than `spectral-gap-ratio-reductions-cannot-prove-ugc` (K4) gives: K4 says
a YES instance of Gap-SSE has some almost-invariant character, this says the
almost-invariant character can be taken to descend to the quotient that carries
the labels.

**Consequence: the decomposition of SSEH along lifts.** Combining with item (4)
of `lifts-over-multiscale-expanders-expand-unless-ug-value-large`, a lift route
to `small-set-expansion-hypothesis` has exactly these independent prerequisites.

- **(P1) Base-family hardness.** For every `nu > 0` there are `eps <= nu`,
  `q` and `tau >= 2/q` such that `Gap-UG(1 - eps, nu^3 tau^2/64)` is NP-hard on
  `q`-label games whose constraint graph satisfies `Phi_H(A) >= 1 - nu/24` for
  every `mu(A) in [1/q, tau]`. *(P1) implies SSEH*, by that item (4).
  *Falsified by* a polynomial-time algorithm for Gap-UG at those parameters on
  those bases. Note the frontier this leaves: by
  `unique-games-on-expanding-constraint-graphs-are-easy` the problem is already
  easy on spectral expanders, so (P1) lives exactly on bases that expand small
  sets and fail to expand globally.
- **(P2) Base spectral defect.** Unless `P = NP`, a family witnessing (P1) has
  **some** YES output with `lambda_2(H) < X(eps)(1 - opt)`, and by (B2)
  `lambda_2(H) < 5 X(eta) sqrt(eta)` on the hard core of both sides of any
  *support-spread* lift reduction. Both quantifiers matter and were overstated
  in the 2026-09-18 submission: (K1) of
  `spectral-gap-ratio-reductions-cannot-prove-ugc` forbids *all* YES outputs
  from having the ratio simultaneously, so its contrapositive gives one bad YES
  output, not a bound on every YES output; and (B2) is stated only for
  support-spread reductions and only on the hard core. *Falsified by* exhibiting
  a hard family all of whose YES bases spectrally expand -- which by (K1) would
  prove `P = NP`. So (P2) cannot fail without a collapse: it is a constraint on
  the shape of any proof of (P1), not a hypothesis one may hope to discharge.
- **(P3) No scale gain.** `Phi_L(1/q) <= min(1 - val, Phi_H(1/q))`, established.
  The density scale `delta` of the output equals a scale at which the base
  already expands. *Falsified by* nothing: it is a theorem. Its force is that
  the `for every eta there is delta` quantifier of SSEH must be met by the base
  family; no amount of lifting, twisting or iterating lifts lowers `delta`.
- **(P4) Profile jump, conditional on N2.** By (B3), a base that *carries N2*
  has its Cheeger cut above `tau` or below `nu delta/6`. Inside this
  decomposition that is not a restriction, since (P1) hypothesizes N2 on the
  family by construction -- but for that same reason (P4) is a property of the
  (P1) family and **not** something (B0) forces on the NO outputs of an
  arbitrary lift reduction; asserting the latter is what refereeing refuted on
  2026-09-18. *Falsified by* a theorem saying that a graph which expands all
  sets of measure in `[delta, tau]` has `lambda_2 = Omega(1)` -- which is false
  (the noisy cube), so (P4) is satisfiable; it is a shape requirement, and the
  only known graphs meeting it are noise graphs and short-code graphs.

Each of (P1), (P2), (P4) can fail without the others: identity permutations on a
noisy cube satisfy (P2) and (P4) and fail (P1) by value `1`; a random unique game
on a Ramanujan graph satisfies (P1)'s soundness and fails (P2); `q` disjoint
copies of an N2 base fails the profile at measure `1/q`.

*Survivors (not killed).*

- **(S1)** Bases that are irregular or carry loops. The import is used only where
  its quoted proof applies, and load rigidity uses regularity through
  `E_(u,v)[l_u] = E_mu[l]`; an early version of the replay that added crossing
  edges without preserving degrees failed item (1) by exactly the degree defect.
  A sibling result of this wave (degree-blow-up-extends-spectral-gap-gate-to-
  irregular-hosts, posted on the bus 2026-09-18 by swarm-0917-w8-w8-ugc-pull and
  not present in this worktree) removes the irregularity hypothesis from the
  AKKSTV half by a degree blow-up that preserves `opt` and does not lower
  `lambda_2`. It does not remove it here, because the blow-up changes the base
  and hence the emitted SSE instance; combining the two is an open repair, and it
  would need the blow-up's effect on `Phi_L(1/q)` to be controlled.
- **(S2)** Reductions that are not support-spread, i.e. whose YES witness lies
  over a base set `P` of measure `< sqrt(eta)/2`. By the load-rigidity lemma the
  witness is then an approximate block system of block size `1/mu(P) > 2/sqrt(eta)`
  over a base region that the walk leaves with probability at most `eta`. If
  `delta >= 2 eta`, such a `P` is itself a base set of measure in
  `[delta, sqrt(eta)/2)` with `Phi_H(P) <= eta/mu(P) <= 1/2`, so a base with the
  N2 profile up to `tau >= sqrt(eta)/2` excludes this branch; for
  `delta < 2 eta`, which is the regime the known constructions live in, the
  branch genuinely survives.
- **(S3)** Reductions whose outputs are not label-extended graphs at all. Nothing
  here touches them; this is the (G2) survivor of
  `sticky-cylinder-gadget-compositions-cannot-prove-sseh` seen from the other
  side.
- **(S4)** The window form. For irregular outputs SSEH allows
  `mu(S) in [delta, 10 delta]`, and the rounding item of the load-rigidity lemma
  is vacuous there; (B0) still holds, and (B3) still holds in its conditional
  form (it never used the rounding item).

**Conditional sharpening over `F_2`.** If
`f2-cayley-subgroup-sets-lose-at-most-log-inverse-density` (currently **OPEN**,
unrefereed) holds, then subgroup enumeration decides `Gap-SSE(eta, 2^(-c))` on
`F_2^k` Cayley graphs in time `N^(c + O(1))` once `eta (c + 3.61) < 2`. Since the
Galois lift of (B4) emits exactly such graphs at `delta = 2^(-c)`, an
elementary-abelian lift route must use `c >= 2/eta - 3.61`, i.e.
`q = 2^c >= 2^(2/eta - 3.61)`. This is stated conditionally and is not used
anywhere above.

ATTEMPTED DERIVATION sseh-lift-base-spectral-gate-proof (blocked on
`single-density-expansion-forces-the-multiscale-profile`)

## Attempts

* **The two-sided gate plus Cheeger against the base profile (2026-09-18,
  swarm-0917; route `sseh-lift-base-spectral-gate-proof`). Submitted as
  ESTABLISHED, refuted by refereeing at step (B3), set back to OPEN.** Two of
  three lenses refuted, independently and at the same step; the third recorded
  the same defect as presentational and asked for the same fix.
  - *What survives and was re-derived by all three lenses.* The load-rigidity
    lemma `lift-yes-sets-are-labelings-unless-the-base-loses-a-cut` items
    (0)-(5), its dichotomy and its spectral trichotomy; (B0), the import of item
    (3) of `lifts-over-multiscale-expanders-expand-unless-ug-value-large` with
    correct quantifiers (labeling sets give `val <= eta`, cylinders give
    `Phi_H(W) >= 1 - eta` at `mu(W) = 1/q`); (B2), the faithful application of
    (K1) of `spectral-gap-ratio-reductions-cannot-prove-ugc` with `s = eta`
    (`f'(x) = U(x)` loop-free regular on `E`, `1 - opt <= 5 sqrt(eta)`,
    `lambda_2 >= theta = 5 X(eta) sqrt(eta) >= X(eta)(1 - opt)`, padding game
    `opt = 1/ceil(1/eta) <= eta` off `E`, `X >= 3` killing (Y-spec) and
    support-spread killing (Y-thin)), and the `E`/`L n E` hard-core logic; and
    (B4). Replay reproduced exactly: `check_load_rigidity.py 1`, 56,208 sets, 0
    failures, exit 0; `bin/cairn check` clean.
  - *Where it dies.* (B3) concluded `mu(B) > tau or mu(B) <= nu delta/6` for the
    Cheeger cut of every NO base in the hard core, and the claim title, the
    sentence "The Cheeger cut of the base never sits inside the small-set
    window", survivor (S4), (P4) and the node bullet on
    `small-set-expansion-hypothesis` all stated it unconditionally. It is not
    unconditional. `Phi_H(1/q) >= 1 - eta` plus `lambda_2 < theta` plus Cheeger
    buys only `mu(B) != 1/q`. The `> tau or <= nu delta/6` conclusion needs
    `Phi_H(A) >= 1 - nu/24` throughout `[1/q, tau]` (to exclude the window) and
    at `mu(B') in [1/q, 2/q]` (to run the padding chain
    `mu(B)(1 - kappa) <= e(B) <= e(B') <= (2/q)(nu/24)`) — i.e. the full N2
    profile. N2 is a hypothesis of the *sufficiency* half of
    `lifts-over-multiscale-expanders-expand-unless-ug-value-large` (item (2)),
    not a consequence of its necessity half: its item (4) forces only "N1 at
    level `nu` and N2 **at scale `1/q`**". Inside the (P1)-(P4) decomposition
    the family carries N2 by construction, so quoting (B3) there is circular
    rather than forcing.
  - *Why the gap is not cosmetic.* Propagating expansion from measure exactly
    `1/q` upward by random halving loses a factor `k = q mu(A)`
    (`1 - Phi_H(A) <= k eta`), so it is vacuous once `mu(A) >= 1/(eta q)`; with
    `eta` fixed and `q -> infinity`, which is the regime SSEH needs, the upper
    part of `[1/q, tau]` is unconstrained. Lens 2 sketched a base of `1/rho`
    weakly coupled noisy-cube-like clusters of measure `rho`,
    `1/q << rho <= tau`, with `Phi_H(1/q) >= 1 - eta`, `lambda_2 ~ 0 < theta`
    and a sparse cut at measure `rho` strictly inside the window — exactly what
    (B3) claimed cannot exist. Recorded as
    `single-density-expansion-forces-the-multiscale-profile` (**OPEN**), now the
    route's missing prerequisite.
  - *Secondary, both flagged by lens 1 and lens 2 and both fixed in place.* The
    claim title and (P2) dropped the support-spread hypothesis that (B2)
    explicitly requires, and survivor (S2) already concedes that branch survives
    for `delta < 2 eta`, which is the regime SSEH actually needs; and (P2)
    asserted "any family witnessing (P1) has `lambda_2(H) = O(eps)` on its YES
    outputs" without the `P != NP` caveat and without restricting to the hard
    core, whereas (K1) only forbids all YES outputs from having the ratio
    simultaneously.
  - *The repair.* Either prove
    `single-density-expansion-forces-the-multiscale-profile` (or the weaker
    window-restricted form recorded in its Attempts, with loss independent of
    `tau q`), or keep N2 permanently as an explicit hypothesis on the NO bases,
    in which case the claim is a statement about lift reductions whose NO bases
    are multiscale expanders rather than about all of them. The gate (B0)-(B2)
    itself — the two-sided `lambda_2 < 5 X(eta) sqrt(eta)` conclusion for
    support-spread reductions — is unaffected and is what should be re-submitted
    first, on its own.
