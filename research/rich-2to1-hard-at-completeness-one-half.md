---
rg: 2
id: rich-2to1-hard-at-completeness-one-half
kind: claim
title: For every eps it is NP-hard to tell fully rich 2-to-1 games of value >= (1-eps)/2 from value <= eps
distinct_from:
  rich-2to1-games-conjecture: that asks completeness 1-eps on rich instances; this is the proved gap at completeness (1-eps)/2, so richness itself costs nothing at the one-half wall.
  unique-games-hard-at-completeness-one-half: that is the unique games gap at completeness one half; this is the fully rich 2-to-1 gap, obtained from the imperfect-completeness 2-to-1 theorem by an arbitrary orientation lift and the BKM right merge, losing a factor 2 only in soundness.
  two-to-two-games-theorem: that gives near-1 2-to-1 hardness on linear F_lin-type pairings, far from rich; this gives rich pairings at completeness one half.
  perfect-completeness-rich-2to1-tractable-skeletons-are-in-p: that kills right merges at completeness 1; this uses a right merge at completeness one half, where that kill is silent.
artifacts:
  - experiments/orientation-lift-2026-09-17/check_orientation_lift.py
  - experiments/audit-rich-2to1-one-half-2026-09-18/check_bipartization_and_branch_formula.py
  - research/artifacts/rich-2to1-one-half-audit-2026-09-18.md
---

**ESTABLISHED.** For every `eps > 0` there is a constant `k = k(eps)` such
that `Gap-Rich-2-to-1[2k]((1-eps)/2, eps)` is NP-hard. The instances are weighted
bipartite 2-to-1 games with left alphabet `[2k]` and right alphabet `[k]`. At every
left vertex a weighted random incident edge induces the uniform distribution on
all perfect pairings of `[2k]` (BKM Definition 5, with edge weights read as
multiplicities).

**Meaning.** The richness condition is not what separates the proved theorems
from the Rich 2-to-1 Conjecture. At completeness one half it is free: lift a
proved 2-to-1 instance by an arbitrary orientation and right-merge it. What the conjecture adds
is completeness above one half. By `orientation-lifts-sandwich-2to1-game-values`,
that is the completeness of a branch selector, not a property of the pairing law.

**Proof in one line.** Lift the imperfect-completeness 2-to-1 instances by any
orientation, then apply the BKM right merge. The values move in the windows
`[1/2, 1]` and `[1, 2]`.

This is not a new hardness phenomenon. It is a composition of imported results
and the elementary lift bound, recorded because the target node says "the
whole difficulty is concentrated in supplying richness". Read at the one-half
wall, that sentence is false.

DERIVATION rich-2to1-hard-at-completeness-one-half-proof

## Attempts

* **Adversarial audit, three lenses (2026-09-18, calibration lane,
  `e2-w2-audit-ugc1`).** **SURVIVES; status unchanged.** Full record, with every
  import quoted verbatim from the downloaded sources, in
  `research/artifacts/rich-2to1-one-half-audit-2026-09-18.md`. The audit also
  covers `orientation-lifts-sandwich-2to1-game-values`, which this claim
  consumes.
  - *Lens 1 (first step that does not follow).* None. `U_o` is a unique game
    because `a -> (p_e(a), o_e(a))` is injective between sets of size `2k`; the
    sandwich `val(G)/2 <= val(U_o) <= val(G)` is the forget-the-bit projection
    and the uniform random bit, both attained; `val(U) <= val(Psi(U)) <=
    2 val(U)` holds pointwise in the left labelling because a fibre has two
    elements; `|S_(2k,k)| = (2k)!/2^k` is the right count and is constant; the
    gap arithmetic at `eps_0 = eps/2` is correct.
  - *Lens 2 (imports).* All three imports check out against the sources.
    `Psi` is Braverman--Khot--Minzer Appendix B verbatim, its value bounds are
    BKM's own completeness remark and soundness paragraph, and the even-alphabet
    padding is BKM footnote 3. Richness matches BKM Definition 1.5 in its literal
    sense (uniformly random incident edge, regular graph), because the merge map
    `sigma` is drawn independently of the edge, so `P(u)` is uniform under *any*
    edge weighting and `Psi` preserves biregularity. Step 1's 2-to-1 form is
    faithfully paraphrased from Khot--Minzer--Safra footnote 2, now quoted in
    full; its stronger anchor, not previously recorded here, is
    Dinur--Khot--Kindler--Minzer--Safra TR16-198 Definition 1.2 (`d`-to-1 games,
    `|Sigma_A| = d |Sigma_B|`, edge-fraction value) and Theorem 1.2
    (Hypothesis 3.6 gives `Gap-2-to-1(1-delta, delta)` NP-hard), with
    Hypothesis 3.6 discharged by KMS Theorem 1.8.
  - *Lens 3 (calibration).* The same composition proves `Gap-UG[(1-eps)/2, eps]`,
    which is exactly `unique-games-hard-at-completeness-one-half` -- the argument
    lands **on** the known one-half wall and never crosses it. It proves nothing
    at completeness above `1/2`; it is consistent with
    `perfect-completeness-rich-2to1-tractable-skeletons-are-in-p` because 2-to-1
    hardness is inherently imperfect-complete, so `Psi(U_o)` is never satisfiable;
    the linear-unique-games, expanding-constraint-graph and entangled-value
    algorithms are all vacuous at completeness `1/2`.
  - *Defects found, none load-bearing.* (D1) Item (3) of the sandwich claim node
    is stated with `w_v(L,b)` read off the `G`-optimal right label, under which
    the identity is false; explicit 3-edge instance where it returns `3/10`
    against a true lift value `2/5`, replayed in the check script, part (B). The
    derivation file states the correct reading (`max_m` inside each branch) and is
    right. Two informal sentences that say the lift "loses exactly the minority
    branch mass" inherit the error. (D2) "For every `eps`" should be "for every
    sufficiently small `eps`"; the promise is empty for `eps >= 1/3`. (D3) BKM's
    regularity and uniform-edge hypotheses are not mentioned. (D4)
    `two-to-two-games-theorem-citation` verifies Theorem 1.4 but not footnote 2,
    which is the sentence Step 1 consumes.
  - *Novelty, lower than the node implies.* BKM state both halves themselves:
    `Gap-Unique[1/2, eps]` NP-hard is called there "a simple corollary" of the
    2-to-1 Games Theorem, and "the reduction from Unique Games to Rich 2-to-1
    Games is straightforward, and is given in Appendix B". Composing those two
    published sentences gives `Gap-Rich-2-to-1[1/2, 2 eps]` in two lines, with a
    **better** completeness than the `(1-eps)/2` proved here and with no
    orientation lift, hence with no dependence on the footnote-2 import. That
    short path deserves a second, import-only route file; adding one is outside
    this worker's edit permissions.
  - *By-product, a new obstruction.* Reading footnote 2 as a generic
    gap-preserving `2-to-2 -> 2-to-1` transformation is false. For the only
    bipartization that keeps the `(2k, k)` alphabet ratio -- one fresh right
    vertex per constraint, alphabet `F_2^l / {0, b_c + b'_c}`, two 2-to-1 edges
    of weight `w_c/2` -- the edge-fraction value is exactly `(1 + OPT(U))/2`, so
    it maps `Gap 2-to-2[1-eps, eps]` to `Gap 2-to-1[1 - eps/2, (1+eps)/2]` and
    its soundness is above one half for every `eps`. Constraints with
    `b_c = b'_c`, which KMS Definition 1.3 permits, are unique rather than 2-to-1.
    Proof and 400-instance exact replay in part (A) of the check script. The same
    random bit is lost twice: as the lift's branch, costing completeness on the
    way down, and as the choice of which of a right vertex's two edges to
    satisfy, costing soundness on the way up.
