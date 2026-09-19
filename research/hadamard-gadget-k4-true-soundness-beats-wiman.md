---
rg: 2
id: hadamard-gadget-k4-true-soundness-beats-wiman
kind: claim
title: R*(4) > 331440289/227504128, that is, Wiman's relaxation is lossy at k = 4 and some Had_4 gadget has strictly larger true deletion ratio than Wiman's (positive folding gap at k = 4)
distinct_from:
  hadamard-gadget-ratio-k4-sandwich: that proves the window [1.45685, 1.53473] for R*(4); this is the open statement that the lower end is not attained.
  hadamard-crossing-needs-folding-gap: that shows any crossing of 2 needs a positive folding gap at the crossing k; this asks for the first positive gap, at k = 4.
  hadamard-gadget-crosses-padding-line: that needs R*(k) > 2 for some k >= 6; this is a much weaker, finite, k = 4 test of whether true soundness buys anything over the relaxation.
artifacts:
  - experiments/ugc-hadamard-gadget-k4-2026-09-17/probe_gadget_gap.py
  - experiments/ugc-hadamard-gadget-k4-2026-09-17/probe_gadget_gap_WF.log
  - experiments/ugc-hadamard-gadget-k4-2026-09-17/results-2026-09-19.txt
---

**OPEN.** The claim is
`R*(4) > 331440289/227504128 ~ 1.4568540 = K z_U(4)`. The last equality is
numerical: see `hadamard-gadget-ratio-k4-sandwich`.

## Why it matters

* **It resolves Martinsson's stated question.** He writes, verbatim, "by
  using a relaxation, it is uncertain whether Wiman found the optimal
  Max-Had 4 gadget or not."
* **It is the smallest test of the folding-gap prerequisite.** `Delta(3) = 0`
  exactly, so `k = 4` is the first open case. If `Delta(4) = 0` and the gap
  also vanishes at `k = 5`, then `hadamard-gadget-crosses-padding-line` loses
  its only mechanism at small `k`.
* **It could beat Martinsson's point.** A true-soundness Had_4 gadget with
  ratio above `1.48969` would give a better Min-2Lin(2)-deletion hardness
  ratio from `k = 4` alone than Martinsson's lifted point `73139148/49096883`.
  This depends on how the gadget composes with Had_4 hardness, as in HHM+15.

## A concrete test

Take the folded-LP dual gadget `W_F`, listed in `results-2026-09-19.txt`.

* **Its relaxed ratio is low.** It is exactly `1.316609`.
* **Its folded ratio found so far is high.** The best folded value found by
  heavy local search is `1.552017`. This is an upper bound on its true
  soundness ratio, not a lower bound.
* **The claim follows if** the exact folded minimum at `W_F` gives a ratio
  above `1.4568540`. That is 14 exact pinned Min-2Lin(2)-deletion instances,
  each on `2^15` variables with `2^18` edges.
* **Why a gap is plausible.** On 9 of the 14 pattern orbits, the relaxed
  optimum at `W_F` has a non-folded locus covering 99.95% of `Q`. So the
  relaxation ignores folding almost entirely on those patterns.
* **Why this is not decisive.** The heavy search does not even reproduce
  the column-generation LP value `1.5347`. Heuristic folded values are
  therefore unreliable here.

## Ways it can fail

* **An exact folded solve.** If the exact folded minima at `W_F` give a
  ratio at most `1.45685`, this particular witness is gone.
* **Better folded adversaries.** Folded adversaries with exact or stronger
  pricing could push the certified upper bound of
  `hadamard-gadget-ratio-k4-sandwich` down to `331440289/227504128`. That
  refutes the claim.

## Attempts

* **Heuristic folded column generation.** Run on 2026-09-19 by
  swarm-0917-w16-w16-ugc-break.
  * It reached a certified `R*(4) <= 1.534726`.
  * Its pricing is 1-opt local search with folding-lemma starts and random
    kicks. It is not exact, so it proves no lower bound.
  * The step that fails is exact folded pricing: MILP pricing with HiGHS
    (`hadk_price.py`) was too slow at `2^15` variables.
