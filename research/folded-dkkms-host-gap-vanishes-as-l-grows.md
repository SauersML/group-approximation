---
rg: 2
id: folded-dkkms-host-gap-vanishes-as-l-grows
kind: claim
title: The folded DKKMS 2-to-1 host has spectral gap at most 2(beta + 6 * 2^(-l)) for l >= 6, because the equations frozen by a Lemma 4.1 class form a class invariant that a two-step walk changes only on a beta + 3 * 2^(1-l) fraction of blocks; so the spectral selector gate is vacuous on DKKMS instances once l > log2(24 / (X(delta) eta'))
distinct_from:
  folded-dkkms-hosts-keep-spectral-gap-as-smoothing-vanishes: that conjectures a lower bound c(l) > 0 on the same gap, uniform in beta and k, and draws from it a conditional kill of H1 with "l fixed by delta"; this is a proved upper bound that tends to 0 as l grows, and it shows that the conditional kill does not follow, because the gate threshold X(delta) eta' does not see l.
  orientation-lift-selectors-need-vanishing-host-gap: that is the gate (necessary condition lambda_2 < X(delta) eta' on YES hosts); this shows the DKKMS host family itself meets that necessary condition at every eta', so the gate adds nothing on DKKMS.
  akkstv-rounding-holds-on-all-loop-free-constraint-graphs: that proves gate (G) on loop-free hosts; this bounds the gap of the one host family the gate was aimed at.
  near-perfect-selectors-on-rigid-dkkms-instances-put-np-in-rp: that kills near-perfect selectors on DKKMS by rigidity plus outer soundness (NP not in RP); this shows the spectral lane cannot replace or extend that kill, in particular not to the constant-bias cell.
artifacts:
  - experiments/ugc-folded-gap-upper-2026-09-17/check_folded_gap_upper.py
---

**ESTABLISHED.** Route: `folded-dkkms-host-gap-vanishes-proof`.

## Setting

`G_folded` is the folded DKKMS 2-to-1 game of ECCC TR16-198, Section 4.2,
built on a regular 3LIN instance `(X, Eq)` with `m` equations, tuple size `k`,
subspace dimension `l` and smoothing `beta`. All definitions are quoted
verbatim in the route. `lambda_2(G)` is `1 - sigma_2` of the normalized
bipartite matrix of the weighted constraint graph (classes `C` against
`B`-vertices `(V, L')`). This is the normalized-Laplacian gap used by gate (G)
and by `orientation-lift-selectors-need-vanishing-host-gap`.

Put

```text
gamma  = 2^(l - 2k) (e^(3 beta k)/2 + 1)                (mass of L meet H_U != 0)
pi*    = max over variable triples t of P_mu(t is a frozen triple of the class)
rho    = (beta + 3 * 2^(1-l)) / ( (1 - gamma) ((1 - beta)(1 - 3 * 2^(1-l)) - gamma - pi*) ).
```

For a regular instance whose triples have multiplicity at most `mu`,
`pi* <= mu k / ((1 - nu)(1 - gamma) m)`, where `nu = O(k^2/|X|)` is the
illegitimate fraction (DKKMS). So `pi* -> 0` as `n -> infinity` at fixed `k`.

## Statement

**Theorem F.** For every regular 3LIN instance, every `l >= 2`, `k` and
`beta in [0, 1]` with `rho < 1`,

```text
lambda_2(G_folded)  <=  1 - sqrt(1 - rho)  <=  rho.
```

If moreover `l >= 6`, `beta <= 1/32` and `gamma + pi* <= 1/32`, then
`lambda_2(G_folded) <= 2 (beta + 6 * 2^(-l))`.

At the DKKMS smoothing `beta = ln ln k / k` this is `12 * 2^(-l) + o_k(1)`.

**Corollary F1 (the gate is vacuous on DKKMS hosts).** Fix `delta` and
`eta' > 0`, and let `X(delta) >= 3` be the constant of gate (K1). Take
`l >= log2(24 / (X(delta) eta'))` with `l >= 6`, and `k`, `n` so large that
`2 beta < X(delta) eta' / 2` and `gamma + pi* <= 1/32`. Then every DKKMS host
at `(l, k)` on at least `n` variables has `lambda_2 < X(delta) eta'`. So the
hypothesis of gate (G) and of `orientation-lift-selectors-need-vanishing-host-gap`
fails there, for every selector and at every completeness `1 - eta'`,
including the constant-bias cell `eta' in (10^(-5), 1/2)`.

**Corollary F2 (the recorded conditional kill does not follow).** The
conditional kill of H1 recorded in
`folded-dkkms-hosts-keep-spectral-gap-as-smoothing-vanishes` and in
`parity-leaking-branch-selectors-reach-near-perfect-completeness` reads
"`eta' >= c(l)/X(delta)` with `l = l(delta)`". DKKMS do not fix `l` by
`delta`. Their Hypothesis 3.6 and Lemma 3.17 hold "for all sufficiently large
integers `l`", and the proof of Lemma 5.3 uses `l` only through them, through
Lemma 3.20 ("Since `l` could have been chosen large enough") and through
"all hidden constants may depend on δ and `l` but are independent of `k`. So
for large enough `k` ...". So a reduction designer may take `l = l(delta, eta')`.
By Theorem F, `c(l) <= 12 * 2^(-l) + o(1)`, so the lower bound `c(l)/X(delta)`
tends to `0` along the admissible choices. Even if the OPEN lower bound
`c(l) ~ 4^(-l)/2` of that node is proved, it gives no lower bound on `eta'`
that is uniform over DKKMS parameter points. (The reading "every `l >= l_0(delta)`
is sound" is of the DKKMS proof, not of the wording of Lemma 5.3, which says
"there exists large enough `l << k`". F1 does not depend on it.)

## What it kills (impact type 3)

**Class.** Every spectral or expansion gate of the form "YES host gap
`>= Phi(delta) eta'` implies tractability", with `Phi` independent of `l`,
used as a kill of selector routes on DKKMS 2-to-1 hosts. This covers gate
(K1)/(G) of AKKSTV and its blow-up, as well as any alphabet-free unique-games
algorithm on expanding constraint graphs.

**Invariant.** The set of frozen triples `Frozen(C)`, the equations `e` with
`e` inside the singled-out set `I(C)`, is a function of the class `C` (DKKMS
Claim 4.5 together with legitimacy). A two-step walk `C -> (V, L') -> C'`
keeps every frozen triple whose equation survives smoothing and whose rank
survives the restriction `L -> L'`. That happens except with probability
`beta + 3 * 2^(1-l)` per block.

**Step where every member dies.** Gate hypothesis
`lambda_2 >= Phi(delta) eta'`. It fails as soon as
`2^(-l) < Phi(delta) eta' / 24` and `beta` is small, and DKKMS soundness
places no upper limit on `l`.

**Survivors.** Gates whose threshold decays with `l` at least like `2^(-l)`
(none is known; AKKSTV-type rounding is alphabet-free); hosts other than
DKKMS; and all non-spectral kills (rigidity plus outer soundness, as in
Theorem S).

## Belief change (impact type 4)

The graph recorded that the folded host keeps a gap "set by the folding, not by
the smoothing", and that this yields a kill of near-perfect selectors on
DKKMS "under P != NP alone". The first half is right at fixed `l`. The second
half is wrong. The folding keeps the gap away from `0` only at rate
`Theta(2^(-l))` at best, since the rank-2 blocks are frozen, and `l` is a free
parameter of the reduction. The measured values `0.179` (`l = 1`) and
`0.034` (`l = 2`) already decay by a factor of about 5 per unit of `l`.

## Attempts

* **Frozen-triple test function (2026-09-18).** **Proved.** Theorem F comes
  from the Rayleigh quotient of `f_w(C) = sum over t in Frozen(C) of w(t)`,
  averaged over random signs `w`. The artifact checks the rank-drop lemma
  exactly and evaluates `rho`. On the `n = 24`, `k = 2`, `l = 2` instance it
  confirms `lambda_2 <= 1 - sqrt(1 - rho_exact)` (`0.0349 <= 0.279` at
  `beta = 0`). That instance enforces only disjointness, not DKKMS legitimacy
  (b), and frozen sets are constant on 1799 of 1828 classes; the class
  statistic used there is the intersection over members, which is always a
  class function.
* **Open refinement.** Close the gap between the lower heuristic
  `~ 4^(-l)/2` and this `~ 12 * 2^(-l)`. The lower heuristic counts only free
  blocks; rank-1 blocks move along the equation–variable–equation walk and
  probably contribute `Theta(2^(-l))`. This does not affect F1.
