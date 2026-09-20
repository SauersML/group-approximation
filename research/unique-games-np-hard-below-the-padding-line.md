---
rg: 2
id: unique-games-np-hard-below-the-padding-line
kind: claim
title: Some unique-games gap strictly below the padding line is NP-hard -- rationals s < 2c - 1 < 1 and an alphabet K with Gap-UG_K[c, s] NP-hard (deficit ratio above 2)
distinct_from:
  unique-games-conjecture: that asks for (1-eps, eps) for every eps, deficit ratio tending to infinity; this asks for one point with ratio above 2, and is strictly implied by it (route padding-line-hardness-from-ugc); nothing here converts it back.
  unique-games-hard-at-completeness-one-half: that is the proved point ((1-eps)/2, eps), ratio 2(1-eps)/(1+eps) < 2, strictly above the line; this asks to cross the line.
  ug-hardness-deficit-ratio-padding-line: that is the established invariant and class kill; this is the open milestone it isolates.
  small-set-expansion-hypothesis: that is a stronger open hypothesis implying UGC; this is a weaker open necessary consequence of UGC.
---

**OPEN.** There are rationals `0 <= s < 2c - 1`, `c < 1`, and an alphabet size
`K` such that `Gap-UG_K[c, s]` (YES: `val >= c`, NO: `val <= s`) is NP-hard.
Equivalently, by `ug-hardness-deficit-ratio-padding-line`, some NP-hard
unique-games point has deficit ratio `R(c, s) = (1-s)/(1-c) > 2`.

**Why it is a milestone.**

* It is **necessary** for `unique-games-conjecture`, by the route
  `padding-line-hardness-from-ugc`. A refutation of it, for example a
  polynomial-time algorithm telling `val >= c` from `val <= s` whenever
  `s < 2c - 1`, refutes UGC.
* It is **independently failable.** It asks for one constant-gap point, not a
  family with vanishing deficit. So soundness and completeness can stay
  constants bounded away from `0` and `1`. For example, take a point with
  `c < 1 - 1/800` and `R < 56`, such as `(3/4, 1/4)`. There, neither
  `low-label-threshold-rank-reductions-cannot-prove-ugc` (which needs
  `c >= 1 - 1/800`) nor item 3 of `spectral-gap-no-outputs-cannot-prove-ugc`
  (which needs `56 eps0 < 1 - delta`, i.e. `R > 56`) applies as stated.
* **Every recorded unconditional point is on the wrong side.** The 2-to-2
  point `((1-eps)/2, eps)` has `R < 2`, and so does every padding of it. The
  earlier O'Donnell--Wright points have `R = 5/4`. O'Donnell and Wright,
  *A new point of NP-hardness for Unique Games*, STOC 2012, p. 3, verbatim:
  "Via trivial reductions, our Main Theorem extends to give NP-hardness of
  (c, 3/4 c + o(1))-approximating Unique-Games (for c ≤ 1/2) and also of
  (c, 1 − 5/4(1−c) + o(1))-approximating Unique-Games (for c ≥ 1/2)". For
  `c >= 1/2` that is `R -> 5/4`. The author of this node found no imported
  point with `R > 2`. This is a report on the graph and the two cited sources,
  not a survey claim.
* **Its hard core is completeness above 1/2.** By item 2 of
  `ug-hardness-deficit-ratio-padding-line`, any witness has `c > 1/2`. By its
  item 5, no padded proper split of any d-to-d game is a witness. That covers
  the whole 2-to-2 split pipeline of `unique-games-hard-at-completeness-one-half-proof`,
  whose certified completeness uses exactly the one-branch count.

## Attempts

* **Split a proved 2-to-2 or d-to-d instance, then pad.** **Dead (2026-09-18)**
  -- `ug-hardness-deficit-ratio-padding-line`, item 5. *Invariant:* proper
  branches, so exactly one branch holds on each satisfied constraint. *Step:*
  completeness, where the YES value is at most `(1 + lambda)/2` against a NO
  floor of `lambda`. Survivors: improper constraints whose branches coincide
  on a large set of labels, non-split outputs, and label re-encoding
  compositions.
* **Amplify the proved UG point black-box: gadgets, code composition, walk
  powering, tensor powers.** **Dead for twin-splitting maps and pure tensor
  powers (2026-09-18).** See `twin-mixture-caps-deficit-ratio-of-local-amplifiers`,
  swarm-0917-w7-w7-ugc-follow.
  - *Invariant:* mass faithfulness on twins. The YES instance `M = aS + bH`,
    a satisfiable twin mixed with a NO instance, has value exactly `c`. It is
    split by the map exactly as the NO instance `(a+b)H` is.
  - *Step:* completeness on `M`, where `c' <= lambda + (1 - lambda) s'`. So
    `R' <= (1 - s_H)/(1 - c) <= 1/(1 - c)`, and tensor powers give
    `R' <= R/(1 - v0)`.
  - From the 2-to-2 point `((1-eps)/2, eps)` every such map, and every chain
    of them with paddings, stays at `R' <= 2/(1 + eps) < 2`. This covers the
    label re-encoding survivor above whenever the composition is applied to a
    unique game as a black box.
  - Survivors:
    - non-black-box maps, correct only on a reduction image that is not
      closed under twin mixtures, such as the KMS instances;
    - cross-component maps such as expanderization or global re-pairing;
    - label-sensitive mass (distortion `D` gives only `R' <= 1 + D(R_H - 1)`);
    - randomized maps;
    - a gadget applied after a tensor power;
    - direct reductions from 3LIN or label cover with non-split outputs.
* **Hadamard gadget reductions into Max-2Lin(2) (2026-09-18,
  swarm-0917-w11-w11-ugc-break).** These are the direct non-split survivor
  above, and the family behind the records `11/8` and `1.48969`.
  - *Status:* **dead for `k <= 5`**, and **dead for every relaxed-soundness
    certificate**. For every `k` the ratio is capped at `5/2 - 2^(1-k)`. See
    `hadamard-gadget-deletion-ratio-window`.
  - *Invariant:* `delta_k`, the mean normalized distance of a random word to
    `RM(1,k)`.
  - *Step where it dies:* soundness against a decoded threshold adversary.
    The adversary decodes the primaries to a signed dictator, and corrects
    only inside the cap `m(x) > tK`, with `t` uniform on `[3/4, 1]`. It
    prices every length-one edge at `K Pr[cut] = 1 + delta_k (3 - 4/K)`,
    which is below `2` for `k <= 5`.
  - *Decomposition:* the family now reduces to the independently failable
    `hadamard-gadget-crosses-padding-line` through
    `padding-line-hardness-from-hadamard-gadget`.
  - *Survivors:*
    - `k >= 6` with true soundness. At `k = 6` the decoder bound is about
      `1.9889` by Monte Carlo, so it is likely dead but not proved.
    - From `k = 7` the decoder adversary is inconclusive.
* **Gadget reductions from 3Lin(G) into permutation 2-CSPs on the alphabet
  `G`.** **Dead for groups `Γ` with few fixed points (2026-09-18).** See
  `three-lin-gadgets-stay-below-padding-line`, swarm-0917-w12-w12-ugc-break.
  - *Invariant:* pairwise uniformity of the source constraint set. It gives
    unique anchors `γ ∘ x_j` above agreement `(1 + ρ)/2`, and exact decoding
    from two of the three coordinates.
  - *Step:* per-gadget soundness. An anchored threshold adversary that is
    random on the primaries has expected deletion at most `λ c`, with
    `λ = 1 + (2q^2 - q - 2)/(3q^2) < 5/3`. This covers Max-2Lin(Z_q), affine
    2Lin over `F_q`, `UG_3` and `A_5`, and `UG_4` has the cap `89/48`.
  - Survivors:
    - all of `UG_q` for `q >= 5`, where the adversary gives only `2.21` at
      `q = 5`;
    - output alphabets larger than the source alphabet;
    - source predicates with small information sets, such as Hadamard;
    - global NO-side certificates that are not per gadget.
* **Per-gadget local gadgets from 3Lin, kLin or quasigroup predicates into
  `UG_L`, any `L >= q`, any permutations.** **Dead (2026-09-20).** See
  `gadgets-into-any-unique-games-stay-below-padding-line`,
  swarm-0917-w20-w20-ugc-break, route
  `padding-line-via-local-gadgets-from-latin-predicates`.
  - *Invariant:* the fibre-plurality score `σ` along the free coordinate. It is
    relabelling-invariant and `1/N`-Lipschitz, `1` on the free primary and
    `1/q` on the others.
  - *Step:* soundness certification. A threshold switch on `σ` between two
    uniform reading points caps `R <= 2 - 1/N`. For 3Lin that is `2 - 1/q^2`,
    e.g. `49/25` for `UG_5`. The script finds it attained once `L > q`.
  - This closes survivors 1 and 2 of the entry above (`UG_q` for `q >= 5`, and
    larger output alphabets with injectively encoded primaries).
  - Survivors: Hadamard with `k >= 6`; sources below the `1/q` threshold, such
    as label cover and d-to-1; long-code labels; global certificates.
