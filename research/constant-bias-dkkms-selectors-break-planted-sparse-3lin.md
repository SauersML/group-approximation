---
rg: 2
id: constant-bias-dkkms-selectors-break-planted-sparse-3lin
kind: claim
title: A constant-bias DKKMS branch selector yields a polynomial-time distinguisher of advantage 1 - o(1) between planted noisy 3XOR and random 3XOR on D random triangle factors (m = Dn/3, constant D and noise) -- routed through (P2^RU) alone, this is the constant-bias kill of H1 without (P1^RU), under the sparse-LPN hypothesis in place of NP not in RP
distinct_from:
  constant-bias-dkkms-selectors-put-np-in-rp: that concludes NP ⊆ RP and needs the worst-case hardness (P1^RU); this concludes an average-case break and needs no hardness prerequisite at all, only (P2^RU).
  planted-regular-3lin-inputs-are-robustly-unique: that is the membership theorem and its corollary for arbitrary algorithms on (RU-YES, NO); this is the selector consequence, conditional on (P2^RU).
  locally-read-witnesses-are-sound-on-planted-2to1-inputs: that concerns locally read witnesses on planted 2-to-1 inputs; this concerns selector-produced orientations and passes through the one-sided decoder of Theorem CLV.
---

**OPEN.** One route, `constant-bias-selectors-break-planted-3lin-proof`.
Its only prerequisite that is not ESTABLISHED is (P2^RU),
`dkkms-orientations-admit-star-lists-on-robustly-unique-inputs`.

## Statement

Fix the DKKMS parameters `(k, l, beta)` with `l >= 8`, the constant-bias
constants `0 < gamma' < gamma <= 0.105`, the list budget `L` of Corollary DK^C
of `value-free-star-list-references-put-np-in-rp`, and `eps = eps_3` as in
`dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`. Let
`sel` be "a constant-bias selector exists" for regular Gap3Lin through DKKMS
(`selector-witness-hypotheses-collapse-to-selector-free-form`). Let
`D >= max(2 * 10^4 k^2, 20/sigma^2)` with `sigma := min(eps, s* - 1/2)`, where
`s* > 1/2` is the Gap3Lin soundness constant (Remark S of the membership
node). Let RU-YES be taken at any radius
`rho in [0.061/k, (1 - beta0)/(12k))` and any `r0 >= 0`.

**Claim.**

```text
sel   =>   planted M(n, D, eps/2) and random M(n, D, eps/2) are distinguishable
           in randomized polynomial time with advantage 1 - exp(-Omega(n)).
```

Here `M(n, D, eta)` is the regular sparse 3LIN model of
`planted-regular-3lin-inputs-are-robustly-unique`.

The route derives this from `F_inf(SL^C, RU-YES)`, which is (P2^RU), and
from ESTABLISHED nodes. So the implication "(P2^RU) => claim" is proved;
the claim stays open until (P2^RU), or another route to it, is proved.

**Consequence.** Assume the sparse-LPN hypothesis for this model, that is,
no polynomial-time algorithm distinguishes the two with advantage `1/2`. Then
the claim gives `not sel`. This kills the constant-bias cell of H1
(`parity-leaking-branch-selectors-reach-near-perfect-completeness`) on DKKMS
without any NP-hardness statement about robustly unique inputs. The kill is
then conditional on one open structure statement and one standard
average-case assumption. The previous form was conditional on two open
statements, (P1^RU) and (P2^RU), and on NP not in RP.

## What would decide it

* **Proving (P2^RU)** on RU-YES at some radius `rho >= 0.061/k` makes this
  claim ESTABLISHED. Since RU-YES shrinks as `rho` decreases, the radius at
  which (P2^RU) is proved matters. The planted instances actually satisfy RU
  with `C = 0` at every radius above about `(kappa + 3eps/4)/(3 - o(1))`
  once `D` is a large enough multiple of `k^2`, because `q(p) = 3p - O(p^2)`
  in Step 2 of the membership route. So a proof at radius `0.03/k` would
  still suffice after raising `D`. This refinement is not proved here.
* **(P2^RU) restricted to planted inputs** is enough. The proof only feeds
  planted draws that land in RU-YES to the algorithm. So a proof of
  `F_inf(SL^C, P_pl)`, with `P_pl` the planted inputs satisfying the
  conclusions of Theorem PR, suffices. That class has `C = 0`, a
  hypergraph expanding at density `0.06/k`, and slot measures within
  `1 +- 9k^2/n` of uniform. It may be a better-structured target than RU-YES
  itself.
* **Falsifiers.** A constant-bias selector together with evidence that
  planted and random `M(n, D, eps/2)` are indistinguishable would refute the
  claim, and with it (P2^RU). A weaker outcome leaves the claim open but
  without a route: an orientation of lift value `>= 1/2 + gamma` on a planted
  instance that no short star list explains. That refutes (P2^RU) on `P_pl`.

## Attempts

* **2026-09-20, swarm-0917-w21-w21-ugc-follow (probability-random).**
  Created. The route composes Corollary D's proof (which shows
  `(P_0, NO) in RP` before using hardness) with Theorem PR of
  `planted-regular-3lin-inputs-are-robustly-unique`.
