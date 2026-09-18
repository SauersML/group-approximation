---
rg: 2
id: near-perfect-selectors-on-rigid-dkkms-instances-put-np-in-rp
kind: claim
title: At every DKKMS parameter point in the covering regime, every randomized polynomial-time branch selector, with any views and on any reduction into the DKKMS construction, whose YES orientation lifts reach value 1 - 10^(-5) puts the source promise problem in RP
distinct_from:
  high-advantage-selector-witnesses-decode-good-outer-labellings: that decodes selectors only from witnesses assumed to be near a locally honest patchwork (Corollary A) or assuming the OPEN rigidity node (Corollary B); this discharges both assumptions with Theorem R, so it needs nothing about the witness, the views or the rigidity node, and it names the exact parameter regime.
  dkkms-near-perfect-labellings-are-outer-honest: that is a combinatorial structure theorem with no selector and no complexity content; this is its complexity consequence for every orientation lift.
  efficient-branch-selector-on-proved-2to1-instances: that is the OPEN selector hole; this refutes it under NP not in RP at every parameter point of the regime.
  parity-leaking-branch-selectors-reach-near-perfect-completeness: that is the OPEN global-view selector hole; this refutes it under NP not in RP whenever its instances D(I) are the DKKMS construction in the regime, whatever the views and whatever the parity leakage.
  view-local-branch-selectors-are-gauge-blind: that caps bounded parity-faithful views at 1/2 plus leakage, over honest menus; this is view-free, certificate-free and menu-free, but only at completeness 1 - 10^(-5).
artifacts:
  - experiments/ugc-seed-law-2026-09-17/check_seed_law_regime.py
---

**ESTABLISHED.** Route: `near-perfect-selectors-on-rigid-dkkms-instances-proof`.

## Setting

The notation is that of `dkkms-near-perfect-labellings-are-outer-honest`
(Theorem R) and of `high-advantage-selector-witnesses-decode-good-outer-labellings`
(Theorem 3, Corollary A). `G_folded(I)` is the folded DKKMS 2-to-1 game
(ECCC TR16-198, Section 4.2) built on a regular 3LIN instance `I`, with
parameters `l, k` and `beta = log log k / k`. For an orientation `o` of its
edges, `U_o` is the orientation lift of `orientation-lifts-sandwich-2to1-game-values`,
a unique game on the doubled right alphabet. Put

```text
SD*(l,k) = beta sqrt(k) 2^(l+3) + 3 * 2^(l-k),     p0 = 2^(-l)/192,
eps_k    = exp(-k / exp(q l))                        (DKKMS Lemma 5.4).
```

A parameter point `(l, k)` is **in the regime** if

* (R) `l >= 3` and `SD*(l,k) <= 10^(-5)`; and
* (A) `2^(l-1-2k) <= 1/16` and `eps_k <= p0^2 / 4`.

(R) implies the side conditions of Theorem R (`2^(l-1) beta <= 1/8`,
`2^(l-k) <= 1/200`, `3k >= l+2`). (A) is the admissibility condition of
Corollary A.

## Statement

**Theorem S.** Fix `(l,k)` in the regime and `eps_3 > 0`. Let `Lang` be a
promise problem with a polynomial-time map `x -> I(x)` into regular 3LIN
instances such that YES inputs go to instances with value `>= 1 - eps_3` and NO
inputs to instances with value `<= s*` (the soundness of DKKMS Theorem 4.1).
Let `S` be any randomized polynomial-time algorithm that, on input `x`, outputs
an orientation `o = S(x)` of `G_folded(I(x))`. `S` may read the whole input,
including every right-hand side, and may be global, adaptive and
parity-leaking. Suppose that for every YES input `x`,

```text
Pr_S [ val( U_(S(x)) (G_folded(I(x))) ) >= 1 - 10^(-5) ]  >=  theta(|x|)  >=  1/poly(|x|).
```

Then `Lang in RP`. With `Lang = Gap3Lin(1 - eps_3, s*)`, which is NP-hard by
DKKMS Theorem 4.1, this gives `NP in RP`.

**Corollary S1 (the proved-instance selector hole).**
`efficient-branch-selector-on-proved-2to1-instances` asks, for each `eta`, for
a polynomial-time orientation of `R_eta` with YES lift value
`1 - eta'(eta)` and `eta' -> 0`. Under `NP not in RP`, this fails at every `eta`
where `eta'(eta) <= 10^(-5)` and the parameters of `R_eta` are in the regime.
It is a conditional refutation at those parameter points, not an unconditional
one.

**Corollary S2 (the global parity-leaking hole).**
`parity-leaking-branch-selectors-reach-near-perfect-completeness` asks for a
reduction from a gap-3LIN problem to Grassmann 2-to-1 instances `D(I)` of DKKMS
shape and a selector `S` with YES lift value `1 - eta'`, `eta' -> 0`. If `D(I)`
is the DKKMS construction at parameters in the regime, composed with any
polynomial-time map between 3LIN instances, then Theorem S applies to every
selector. The views, the parity leakage and the certificate are irrelevant.
Under `NP not in RP`, the route `ugc-via-parity-leaking-branch-selector` is
therefore closed on DKKMS-form instances in the regime. Its necessary condition
from `view-local-branch-selectors-are-gauge-blind` (leakage
`w_bad >= 1 - 2 eta'`) is not the binding constraint: near completeness 1,
full leakage does not help either.

**Corollary S3 (the regime is automatic for q >= 2).** Suppose the advice
dimension `q` of DKKMS Lemma 5.4 is at least `2`. Then for every `l >= 43`,
every `k` with `eps_k <= p0^2/4` already satisfies `SD*(l,k) <= 10^(-5)`. So
(A) implies (R), and Theorem S holds at every Corollary-A-admissible point.
This is checked numerically in (c) of the artifact over `43 <= l < 200`; the
first such `l` is `43`. For `l >= 200` it follows because
`log k_A(l) = 2l + O(log l)` grows faster than
`log k_0(l) = (2 ln 2) l + O(log l)`. The gap between the two slopes is
`2 - 2 ln 2 > 0.61`, and at `l = 199` the margin is already more than `90`
nats, while the `O(log l)` terms change by `O(1/l)` per unit step. For `q = 1` there is a window
`k_A(l) <= k < k_0(l)` that Theorem S does not cover.

## What it kills (impact type 3)

**Class.** Every approach that orients the DKKMS 2-to-1 instances in
polynomial time and asks for YES lift value tending to `1`. This covers
oblivious, local, global, parity-leaking, bounded-rank, adaptive and
randomized selectors, with or without an honest or any other certificate.

**Invariant.** Near-1 lift value forgets to a near-1 labelling of the plain
2-to-1 game. By Theorem R, every such labelling is `1/128`-close to a locally
honest patchwork of an outer labelling of value `15/16`. The unique lift then
lets one guessed right label at a B-vertex propagate over its whole star, and
that star spans `X_U`.

**Step where every member dies.** Corollary A (Theorem 3) decodes an outer
labelling of value `> eps_k` at rate `p0^2 c1/2 >= 5 p0^2/16`. On NO inputs,
Lemma 5.4 rules this out.

**Survivors.**

* Completeness strictly between `1/2` and `1 - 10^(-5)`. This is the constant-bias
  cell. It would already beat `unique-games-hard-at-completeness-one-half`, but
  it does not give UGC along these routes.
* Parameter points outside the regime: `q = 1` with `k < k_0(l)`, or any
  non-DKKMS choice of `beta`.
* Instances that are not the DKKMS construction: another inner test, or an outer
  game other than `Phi_k`.

## Reconciliation with the smoothing concern (need 207b4529)

A lease on the bus (e2-w2-ugc-selector-kill, not landed on main) reported that
DKKMS smoothing makes any per-tuple agreement argument vacuous, because a fixed
direction lies in a fresh `X_V` with probability `(1 - 3beta/4)^k`. It also
reported that the seed law at an A-vertex concentrates on one hyperplane. Its
Proposition 4 then says that, if this dominant germ were folding-compatible,
local rigidity would fail and the constant orientation would solve the selector
hole.

The artifact computes the exact conditional seed law
`w(R | U,L) ∝ E_V[1{R <= X_V} / |Gr(X_V, l-1)|]` of the quoted edge process.

* At `beta = 1/2`, the law does concentrate (E max share `0.38 -> 0.60` for
  `k = 2 -> 8` at `l = 3`).
* At the DKKMS choice `beta = ln ln k / k`, it tends to uniform on the `2^l - 1`
  hyperplanes. At `l = 3` its total variation from uniform falls from
  `0.18` (`k = 16`) to `0.02` (`k = 8192`), always below
  `beta sqrt(k) 2^(l-1)`, which is the covering scale of `SD*`.

The concentration is therefore an artifact of `beta sqrt(k) 2^l >> 1`. Theorem R
never needs a fixed direction to lie in a fresh `X_V`, because its per-tuple
test draws `V` before `L'`. In the regime, Theorem R and Proposition 4 together
answer need 207b4529 **NO**. Independently, Theorem S shows that the constant
orientation, which is polynomial-time, cannot reach YES lift value
`1 - 10^(-5)` in the regime unless `NP in RP`.

This neither proves nor refutes UGC.

## Attempts

* **Composition (2026-09-18).** This node is the composition of Theorem R
  (Corollary N) with Corollary A. The only new points are three:
  - forgetting the right bit maps lift witnesses onto 2-to-1 labellings, and
    patchworks back onto lift patchworks with the same bits;
  - the regime bookkeeping, including S3;
  - the seed-law computation that reconciles the smoothing concern.
