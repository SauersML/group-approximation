# Near-closure triage on famous open roots, 2026-09-12

Lane `near-closure-triage`.  Input: `cairn why` on MSI over the famous OPEN
roots of `FRONTIER.md`, reduced to the 832 route rows that wait on exactly
one open claim (plus imports).  Excluded: every topic owned by a live lane
(Thompson F, all Boone--Higman cases, Labbé, fixed price, `p_c<p_u`,
quasitrace K-stability, kl-remaining-shapes, unit conjecture char 0,
zero-divisor search, rnorm, Pestov Q3.4, non-RF hyperbolic, one-relator
soficity, simple Kazhdan hyperlinear, non-linear-sofic, Gottschalk, Rokhlin,
INF, Bernoulli entropy, Bowen--Chapman perfection, w6-*, LIX).  Owners come
from `git log --since=12:00` trailers on the premise, route and sibling files.

## Headline

There is **no genuine near-closure** on a famous root.  Every single-premise
route waits on a premise that is either recorded as *equivalent* to its root
(PTS1, `stw99-xciv-r-has-local-norm-central-z-copies`) or is itself a named
open question in the literature (FF--W p.7, Q1.9, Q1.12).  The ranking below
orders by (value of either answer) x (smallness of the premise) x (traction).

## Ranked top 5 (all unowned since 12:00)

**1. `sp2g-z-full-c-star-algebra-has-llp` at g=2** -> `non-hyperlinear-group`
via `non-hyperlinear-from-sp2g-llp` and
`nonhyperlinear-from-sp4-llp-maslov-dichotomy` (reqs=3 each).
- *Why it looks decidable:* Fournier-Facio--Willett arXiv:2603.18456v2 p.7:
  "It seems to be open whether higher rank arithmetic groups always fail the
  (L)LP."  LP already fails (ISW arXiv:2006.01874 Ex. 1.3(i)).  The refutation
  side is one ISW Theorem C instance: Theorem 4.3 allows `A = C1` ("In the
  case A is C1 with trivial action, Theorem 4.1 recovers Theorem 2.3"), so
  Connes-embeddable twisted factors along a null Maslov sequence refute LLP
  (`sp4-small-maslov-twisted-group-factors-are-ce`, SMT1).
- *Obstacle already recorded:* ISW Theorem A has no data (Deligne: no
  finite-dimensional projective representations off classes 0, 1/2); the
  Siegel (`Sym^2`) and Klingen (Heisenberg) radicals carry only finitely many
  invariant scalar classes, so no `Z^2 x| Sigma` subgroup exists.
- *Impact:* either answer settles FF--W's p.7 question for `Sp_4(Z)`; LLP gives
  an explicit non-hyperlinear finite cyclic Deligne cover
  (`sp4-llp-failure-or-maslov-nonhyperlinear-extension`).
- *Owner:* none.  Sibling `sp2g-z-flexibly-hs-stable` touched 13:40 by session
  01PWzw.

**2. `mf-trace-gap-defect-ratio-models` (P1)** -> `mf-implies-hyperlinear`
via `mf-implies-hyperlinear-via-rank-profile` (reqs=2).
- *Why:* one quantitative rate.  Conjugate-tensor then tensor-power
  amplification turns op-norm defect `eps` and trace gap `kappa` into
  2-norm defect^2 about `k eps^2` against gap about `k kappa`, so
  `eps^2/kappa -> 0` is exactly what the amplification route consumes.  It
  holds for free when the mark has positive density (RF, LEF, amenable).
  Direct sum with a large multiple of an exact representation leaves `eps`
  unchanged and averages `kappa`, so (P1) is free for every `g` outside the
  finite-dimensional radical; only elements killed by every
  finite-dimensional unitary representation remain.
- *Obstacle:* the claim's own analysis: (T)-rigid exact ambients squeeze the
  mark to density `O(eps^2)`, so any proof must use genuinely approximate
  ambients.
- *Impact:* MF implies hyperlinear.  *Owner:* none.

**3. `sp4-mod3-twisted-fibres-have-llp` (TF3)** -> `non-hyperlinear-group`
via `nonhyperlinear-from-odd-maslov-fibre-llp` (reqs=4) and
`non-hyperlinear-from-e3-fibre-llp`.
- *Why:* the LLP question is localized to one twisted central corner of the
  explicit finitely presented Kazhdan group `E_3`.  It is FF--W Question 1.12
  at a live instance; FF--W Cor. 3.36 (Packer--Raeburn fibres) gives only the
  direction "all fibres LLP => `C*(E)` LLP".
- *Obstacle:* the fibre has no finite-dimensional representations, and eight
  Attempts bullets close the retract, covariance, fixed-size and Folner lanes.
- *Impact:* `E_3` non-hyperlinear.  *Owner:* none.

**4. `sl3-z-weakly-ucp-stable`** -> `non-hyperlinear-group` via
`non-hyperlinear-from-sl3-z-weak-ucp-stability` (reqs=4) and
`sl3-large-prime-collapse-from-weak-ucp-stability` (reqs=5).
- *Why:* Dogon Def. 1.5, equivalent to flexible HS-stability; FF--W Thm 1.1
  (LLP + RFD => very flexibly stable) is the positive model.
- *Obstacle:* its hypotheses are fenced for `SL_3(Z)`, whose full C*-algebra
  fails LLP (ISW Cor. B).  *Impact:* non-hyperlinear group.  *Owner:* none.

**5. `projective-trace-square-transfer-for-sl3-pair` (PTS1)** ->
`non-hyperlinear-group`, the single open premise of three reqs=1 routes
(`nonhyperlinear-from-projective-trace-square-transfer`,
`sl3-amalgamated-free-exclusion-from-projective-transfer`,
`sl3-regular-double-collapse-from-projective-transfer`) and one reqs=3 route.
- *Why:* exact finite-dimensional representations satisfy it: they factor
  through congruence quotients (superrigidity + CSP), strong approximation
  makes `rho(SL_3(Z))` and `rho(SL_3(Z[1/2]))` equal, and (T) gives a
  constant.
- *Obstacle:* that is the calibration case; the claim itself records PTS1 as
  equivalent to canonical RCC and to non-hyperlinearity of the arithmetic HNN
  group, and its Attempts record S3/S4 leaks.  *Owner:* none.

Alternates: `stw99-xciv-r-has-local-norm-central-z-copies` (reformulation);
`random-complex-linear-cocycle-stability` -> `nonsofic-hyperbolic-group`;
`projective-commutant-transfer-for-arithmetic-pair` (PTS1 family); SMT1 and
`sp4-isw-theorem-c-embeddable-twist-data-exists` (refutation side of #1).

## Owners since 12:00 (path-limited trailers)

Owned: `laurent-vertex-rounds` (sessions 01PWzw and this one),
`hyperlinear-groups-kill-rigid-compression-defects` (018da4Z),
`sp2g-z-flexibly-hs-stable` (01PWzw).  No since-noon commit touches any top-5
premise, SMT1, TC1 or the Sp_4 LLP/Maslov dichotomy.

## Source checks (PDFs fetched on MSI, read locally)

- ISW arXiv:2006.01874: Theorem A (relative (T), `c_n -> 1` non-coboundary on
  `Lambda`, finite-dimensional projective representations => not LLP);
  Cor. B; Theorem C / 4.3 and the `A = C1` sentence; Cor. D, E; Ex. 1.3(i);
  Remark 1.2 (LP, LLP pass to subgroups); Theorem G.
- FF--W arXiv:2603.18456v2: Thm 1.1; Q1.9, Q1.10, Q1.12; the p.7 sentence;
  Prop. 3.35, Cor. 3.36, Ex. 3.37 (`H_2(Lambda)=0` => every central extension
  inherits (L)LP).
