---
rg: 2
id: dkkms-certified-parameters-lie-in-the-selector-kill-regime
kind: claim
title: Every parameter point at which the DKKMS soundness proof certifies 2-to-1 soundness below 1/16 lies in the Theorem S regime, so a near-1 branch selector on the proved 2-to-1 instances at any small eta puts NP in RP, with no advice-dimension window
distinct_from:
  near-perfect-selectors-on-rigid-dkkms-instances-put-np-in-rp: that proves the RP collapse only at parameter points in a stated regime (R)+(A), and leaves a q = 1 window k_A(l) <= k < k_0(l) and every point with q >= 2, l < 43 uncovered; this shows that the regime contains every point the DKKMS Lemma 5.3 proof certifies at soundness below 1/16, for every advice dimension q, so the window contains no certified point.
  efficient-branch-selector-on-proved-2to1-instances: that is the OPEN selector hole; this shows it implies NP in RP outright (no parameter caveat), which is a conditional refutation, not a refutation.
  dkkms-2to1-instances-satisfy-selector-decoding-hypotheses: that checks the decoding hypotheses of the honest-witness decoder against the paper text; this reads the inequalities of the paper's soundness proof as constraints on the parameter point itself.
artifacts:
  - experiments/ugc-dkkms-regime-closure-2026-09-17/check_dkkms_regime_closure.py
---

**ESTABLISHED.** Route: `dkkms-certified-parameters-regime-proof`.

## Setting

`G_folded(I)` is the folded DKKMS 2-to-1 game (ECCC TR16-198, Section 4.2) on a
regular 3LIN instance `I`, with parameters `l, k`, `beta = log log k / k`, and
advice dimension `q` of the outer game of their Lemma 5.4. The regime of
`near-perfect-selectors-on-rigid-dkkms-instances-put-np-in-rp` (Theorem S) is

* (R) `l >= 3` and `SD*(l,k) = beta sqrt(k) 2^(l+3) + 3 * 2^(l-k) <= 10^(-5)`;
* (A) `2^(l-1-2k) <= 1/16` and `eps_k = exp(-k/exp(q l)) <= p0^2/4`, `p0 = 2^(-l)/192`.

A parameter point `(delta, l, k, q, r, C)` is **DKKMS-certified** if the proof
of DKKMS Lemma 5.3 (soundness `delta`) goes through at it. That proof uses two
inequalities on the point (quoted verbatim in the route):

* (P1) smooth advice: the non-smooth mass `sqrt(beta) k^(1/4)` of Lemma 4.10 is
  at most `alpha(l)/2`, where `alpha(l) = delta1 2^(-l^2-2)` is the function
  produced by the proof of their Lemma 3.7 (`delta1 <= 1`);
* (P2) outer margin: `eps_k < delta alpha(l)/4`, since the extracted strategy
  wins with probability at most `Pr[E1 and E2 and E3]` times a conditional
  probability, and (16) bounds that event only by `delta alpha(l)/4`.

## Statement

**Theorem C.** Every DKKMS-certified point with `l >= 5` satisfies (R) and (A).
Every DKKMS-certified point with soundness `delta < 1/16` has `l >= 6`.

**Corollary C1 (the selector hole implies NP in RP).** Suppose
`efficient-branch-selector-on-proved-2to1-instances` holds, with
`eta'(eta) -> 0`. Pick `eta < 1/16` with `eta'(eta) <= 10^(-5)`. The hole
defines `R_eta` as the folded DKKMS reduction behind the 2-to-1 form of
`two-to-two-games-theorem`. Its soundness is DKKMS Lemma 5.3, proved through
Lemmas 3.17 and 3.7 from Hypothesis 3.6, which the later papers supply. So its
point is DKKMS-certified at soundness `eta`. Theorem S (Corollary S1) and
`dkkms-2to1-instances-satisfy-selector-decoding-hypotheses` read it the same
way. By Theorem C that point is in the regime, so Theorem S applies to the
selector and gives `NP in RP`. Hence, under `NP not in RP`, the hole is false,
and the two routes
for which it is last missing (`rich-2to1-via-branch-selector-on-proved-2to1-instances`,
`smooth-design-rich-2to1-via-branch-selector`) are closed. The survivor "q = 1
window" and the survivor "q >= 2, l < 43" listed under Theorem S are empty.

*Scope.* "Certified" refers to the proof as printed, where `alpha(l)` comes
from Lemma 3.7. The (R) half is robust. Item 2 of the Lemma 5.3 proof keeps the
factor `2^(l+5)`, and `alpha <= 1`, since it lower-bounds a probability.
Together these give (R) for `l >= 8` whatever `alpha` is. Only the (A) half uses
the printed `alpha(l) <= 2^(-l^2-2)`. A different soundness certificate for
`R_eta` with a far larger `alpha` would need that half redone.

*Instance family.* C1 takes `R_eta` exactly as the hole defines it: the folded
DKKMS TR16-198 game. A live verifier verdict against
`kms-2to2-instances-are-padded-dkkms-selector-lecs` raises a doubt. It suggests
that the proved 2-to-2 instances may instead be the natively 2-to-2 A-A
Grassmann reduction of Khot--Minzer--Safra (ECCC TR16-124). If so, C1 kills the
hole only on the DKKMS family. The same selector question asked on the TR16-124
family is not covered here, because Theorem S is stated for `G_folded`.

**Corollary C2.** The same holds for
`parity-leaking-branch-selectors-reach-near-perfect-completeness` whenever its
instances `D(I)` are the DKKMS construction at a certified point after a
polynomial-time 3LIN map (Corollary S2 of Theorem S, now without a regime
hypothesis).

## Why it matters (impact type 3)

Theorem S killed near-1 selectors only inside a regime, and its own Corollary S3
showed that the obvious sufficient condition, (A) alone, misses a window for
`q = 1` of width `e^l l <= k < 4^l 10^10`. That window was the last place a
near-1 selector on the proved instances could live. The window is an artifact:
it comes from reading (A) as the only constraint on `k`. The soundness proof of
the proved instances needs **smooth advice** (P1), which forces
`k >= 2^(4 l^2 + 12)`, and that alone gives (R). The margin (P2) is charged the
factor `alpha(l) <= 2^(-l^2-2)` of the zoom-in counting, which alone gives (A).

**Invariant and step.** The invariant is the smooth-advice mass
`sqrt(beta sqrt k)` of Lemma 4.10. Every certified point pays for it at
Step (16) of the Lemma 5.3 proof. Paying it there is exactly covering at scale
`2^(-2 l^2)`, far below Theorem R's need `10^(-5) 2^(-l-3)`.

**What survives on the selector side.** Only YES lift completeness strictly
between `1/2` and `1 - 10^(-5)`, and instance families other than the DKKMS
construction. Every route in the graph that asks for near-1 completeness from
an orientation of the proved 2-to-1 instances is now closed under
`NP not in RP`.

This neither proves nor refutes UGC.

## Attempts

* **Parameter audit (2026-09-17).** The artifact scans `q = 1..12`,
  `l = 3..200`, with both the natural and the base-2 reading of `log log`. It
  takes the least `k` satisfying (P1) and (P2) at `delta = delta1 = 1`, which
  is the most permissive case, and checks (R) and (A). The only failures are
  at `q = 12`, `l = 3`, where (A) fails, and that point is below the `l >= 5`
  of Theorem C. The largest `beta sqrt(k) 2^(l+3)` at a certified point is
  `2^(-18)`. On all 198 values of `l` where the `q = 1` window of S3 is
  nonempty, (P1) fails on the whole window.
