---
rg: 2
id: good-dkkms-orientations-admit-short-star-lists-on-hard-inputs
kind: claim
title: (SF_P) On an NP-hard sub-promise P of low kernel rank of regular Gap3Lin through DKKMS, every orientation of the 2-to-1 game whose lift has value >= 1/2 + gamma has a lift labelling explained by a star list of at most L arbitrary outer labellings (D^C_L <= gamma - gamma'), with L inside the Corollary DK^C budget -- the single remaining, selector-free prerequisite of the constant-bias kill of H1 through Theorem CLV
distinct_from:
  selector-witness-hypotheses-collapse-to-selector-free-form: that proves every per-selector witness hypothesis is equivalent to its selector-free form (or to no selector, or implies P != NP), and reduces the kill to this statement; this is the open selector-free statement itself.
  star-list-structure-is-circular-on-decodable-yes-inputs: that refutes this statement on any P containing J-instances (kernel rank k - O(log(1/gamma'))) through the flip orientation; this asks for it on low-kernel-rank inputs, where the flip mechanism is unavailable.
  dkkms-ev-list-structure-needs-lists-exponential-in-k: that refutes the selector-free list structure for one labelling on rank-(k-8) J-instances; this excludes those inputs.
  value-free-star-list-references-put-np-in-rp: that is the decoder (Theorem CLV) this statement would feed; this is only its structure prerequisite, selector-free.
  parity-leaking-branch-selectors-reach-near-perfect-completeness: that is H1; this, with its NP-hardness prerequisite, would kill H1's constant-bias cell on DKKMS under NP not in RP, and does not by itself decide H1.
---

**OPEN.**

## Statement

Fix the DKKMS parameters `(k, l, beta)` with `l >= 8`, constants
`0 < gamma' < gamma` in the constant-bias cell, and `L <= (p gamma'/3)^(1/2) exp(k/(4 exp(q l)))`
(the Corollary DK^C budget of `value-free-star-list-references-put-np-in-rp`).
The notation is that of
`selector-witness-hypotheses-collapse-to-selector-free-form`. For `r >= 0`,
let `P_r` be the set of YES inputs of regular Gap3Lin such that every kernel
map on `D(x)`, in the sense of Theorem O of
`star-list-structure-is-circular-on-decodable-yes-inputs`, has rank `<= r`.

**Claim.** There is `r = r(k, l, gamma')` such that both of the following
hold.

* **(P1) hardness.** `(P_r, NO)` is NP-hard under Karp reductions.
* **(P2) selector-free star lists.** For all but finitely many `x in P_r`,
  every orientation `o` of `G(x)` with `val(U_o) >= 1/2 + gamma` has a lift
  labelling `W` with `val(U_o, W) >= 1/2 + gamma` and a list `Lambda` of at
  most `L` arbitrary outer labellings with `D^C_L(proj W, Lambda) <= gamma - gamma'`.

**Consequence.** By Corollary D of
`selector-witness-hypotheses-collapse-to-selector-free-form`, (P1) and (P2)
together give: every constant-bias selector on DKKMS puts NP in RP. So under
NP not in RP, the constant-bias cell `(1/2, 1 - 10^(-5))` of H1 dies on
DKKMS. By the same node, every per-selector witness route to that kill must
prove (P2), or its analogue for another class `P` and another NP relation,
unless it proves `P != NP`. The two prerequisites can fail independently.

## Why it is open

* **(P2) is refuted only at high kernel rank.** The known violators are the
  flip orientation `o*` on J-instances of rank `k - O(log(1/gamma'))`
  (Theorem O) and the defect-line labelling `h` on rank-`(k-8)` J-instances
  (Corollary EL of `dkkms-ev-list-structure-needs-lists-exponential-in-k`).
  Both use flat stars, where a large homogeneous kernel makes a star
  degenerate on half its mass. The node
  `star-list-structure-is-circular-on-decodable-yes-inputs` lists
  "kernel rank `< k - 2l - O(log(1/gamma'))`" as the region it does not
  reach. Nothing is known there.
* **(P1) is unchecked.** Håstad-format images of Label Cover have equation
  vectors of bounded support spread across blocks. They look kernel-free, but
  no bound on the kernel rank of `D(x)` has been proved for them. There is
  one easy sufficient condition. If the inputs in `YES minus P_r` can be
  certifiably decoded in polynomial time, then `(P_r, NO)` is NP-hard,
  because a decider for it plus the certified decoder decides `Lang`. The J-copy
  test of Proposition S does this for J-instances, but general high-rank
  inputs have not been handled.
* **Candidate route to (P2).** A 51 percent list decoding of the DKKMS
  Grassmann test, from lift labellings of any good orientation, with
  iterated zoom-in/zoom-out references, as in the "iterated KMS zoom decoding"
  bullet of H1's Attempts. The obstacle recorded there is per-star split
  ambiguity. The doubled lift makes agreement two-sided at the free bit
  `b_q`.

**Falsifier.** A YES input of kernel rank `<= r`, with an orientation of lift
value `>= 1/2 + gamma`, every lift labelling of which has `D^C_L > gamma - gamma'`
against every `L`-list. A natural test case is a local-kernel version of the
flip orientation: flips on stars whose kernel is degenerate only on a
constant-size sub-block.

## Attempts

* **2026-09-19, swarm-0917-w16-w16-ugc-pull (finite-models).** I set this
  up as the residue of `selector-witness-hypotheses-collapse-to-selector-free-form`,
  and tried the obvious attack in both directions.
  - *Direct attack on (P2), from the soundness side.* DKKMS soundness decodes
    labellings of value `>= delta` into zoom-in/zoom-out structure. That
    analysis is run on labellings of the NO-side inner game, and its list
    size is `exp(poly(1/delta))` for the local restrictions only. It does not
    give per-star references. It dies at the per-star split ambiguity noted
    in H1's Attempts: a zoom global function fixes a star's evaluation only
    up to the free bit `b_q`.
  - *Refutation attempt (local flip).* This transplants `o*` to kernels of
    rank `r` on a sub-block. The flat-star mass then falls to about `2^(r-k)`,
    so the flip gains `O(2^(r-k))` of `D^C` and no longer beats the budget.
    The attempt dies at Theorem O item 1's value bound, which needs rank
    `k - O(log(1/gamma'))`.

  Both prerequisites remain untested.
