---
rg: 2
id: malcev-root-steps-put-commutator-root-one-relators-in-h
kind: claim
title: When a Magnus segment step adjoins a k-th root of a commutator, the rational Mal'cev completion of a free nilpotent group of Fibonacci class keeps the edge alive, which certifies 16 of the 36 length-14 relators the landed rules leave open; the 18 still open have a root in the middle letter, and no residually torsion-free-solvable target climbs their steps
distinct_from:
  retract-segment-steps-put-perfect-kernel-one-relator-groups-in-h: its rule R retracts onto an edge group via a map to Z with value +-1 on one edge element. Here every map to Z kills the edge element (a commutator), so no retraction exists; the target is nilpotent of unbounded class instead. Its item 3 bounds the solvable length of targets for e = (0, +-1, 0); item 3 here has no length bound, for e = (0, +-2, 0) with propagation.
  magnus-segment-steps-put-one-relator-groups-in-h: its rule 1 needs a map to Z nonzero on both edge elements; here every map to Z vanishes on the edge. Item 3 here answers its item 5 (nonabelian Q) negatively, for all residually-solvable Q with torsion-free normal abelian series, on the 18-word frontier.
  edge-injective-quotients-give-hughes-free-division-rings: item 1 there is the engine used at every step, with a nilpotent target; its item 2 (and the root and root-tower rules built on it) needs a map to Z nonzero on the edge, which fails here.
  kaplansky-zero-divisor-conjecture: this adds no case of the conjecture; groups in H are locally indicable, and torsion-free one-relator groups already satisfy it (Higman; Brodskii, Howie; Lewin-Lewin for the division-ring embedding).
artifacts:
  - experiments/amalgam-segment-steps-2026-09-17/nilpotent_root_certify.py
  - experiments/amalgam-segment-steps-2026-09-17/census_shard.py
  - experiments/amalgam-segment-steps-2026-09-17/census-L14.txt
  - experiments/amalgam-segment-steps-2026-09-17/frontier_check.py
  - experiments/amalgam-segment-steps-2026-09-17/frontier-L14.txt
  - experiments/amalgam-segment-steps-2026-09-17/probe.py
  - experiments/amalgam-segment-steps-2026-09-17/vcs_triage.py
---

**ESTABLISHED** (written proof, unreviewed) by
[[malcev-root-steps-put-commutator-root-one-relators-in-h-proof]]. Item 1 is a new rule. Items 2 and 4 are
computations. Item 3 is an obstruction with a sharpness example. Nothing is new for the zero-divisor conjecture.

**Setting.** As in [[retract-segment-steps-put-perfect-kernel-one-relator-groups-in-h]]:
- `𝓗` is the class of [[vertex-injective-quotients-give-hughes-free-division-rings]].
- `G = <a, t | r>` with `t` of exponent sum `0`, and Magnus rewrite `r' ∈ F(a_0, …, a_m)`.
- The segments are `S_[0,n]`, with `S_[0,-1]` free.
- "The landed rules" are the hierarchy rules, rule 1 of [[magnus-segment-steps-put-one-relator-groups-in-h]] and
  rule R (item 1 of the retract node).

## Theorem

1. **Commutator-root step (rule N).** Let `m = 2` and let `r'` be, up to rotation and inversion, the cyclic word
   `a_2^k u(a_0, a_1)^{-1}` with:
   - `|k| ≥ 2`;
   - `u` of exponent sums `(0, 0)`;
   - commutator coefficient `c(u) ≠ 0`, the image of `u` in `γ_2 F_2 / γ_3 F_2 = Z`, i.e. the signed area of its
     lattice path.

   Then `G ∈ 𝓗`. The same holds from the bottom.
   - Each step `S_[0,n] = S_[0,n-1] *_{u_n = a_{n+2}^k} <a_{n+2}>` is climbed by item 1 of the edge-injective
     lemma. The target is the rational Mal'cev completion of the free nilpotent group of class `f_{n+2}`
     (Fibonacci) on `a_0, a_1`, with `a_{j+2} ↦ u_j^{1/k}`.
   - The leading Lie terms satisfy `L_{j+2} = (c/k)[L_j, L_{j+1}] ≠ 0` (Shirshov–Witt), so the edge element
     survives.
   - Every map to `Z` kills `u_n`, so no landed rule applies.
   - The class has to grow with `n`. In a torsion-free nilpotent target, `a_{j+2}` lies in the isolator of
     `γ_{w_j + w_{j+1}}`, so the weights grow at least like Fibonacci numbers. A target of bounded class kills
     `a_n` for large `n`.
2. **Census at length 14** (`census-L14.txt`, `census_shard.py 14 12 i --amalgam`, 12 shards). There are 85774
   classes of cyclically reduced, non-proper-power two-generator relators of length 14, up to rotation, inversion
   and relabelling.
   - The landed rules without rule R certify 85711. Rule R certifies 27 more. So **36 relators of length 14 are
     the first that no landed rule certifies** (the census through length 13 leaves nothing open).
   - Rule N (item 1) certifies 16 of the 36, each in one untwisted step from the top or the bottom, with
     `k = 2` and `c = 2`.
   - 2 more (`AAAbabbAAAbbab`, `AAABaBBAAABBaB`) have a Nielsen image, after one elementary move, that the landed
     rules certify. This is incompleteness of the certifier's normalisation, not a new rule.
   - **18 remain open.** They are the explicit frontier, listed in `census-L14.txt` and checked in
     `frontier-L14.txt`. All 18 have span 2, `e = (0, ±2, 0)` (13 with `-2`, 5 with `+2`), and top and bottom
     letters that each occur exactly twice (10 with `a_1` twice, 8 with `a_1` four times).
   - **Length 15** (`census-L15.txt`, 36 shards, `frontier-L15.txt`). There are 239144 classes.
     - The landed rules without rule R certify 238866, and rule R certifies 126 more, which leaves 152.
     - Rule N certifies 16 of them, all with `k = 3` and `c = 2`. The Nielsen search certifies none.
     - **136 remain open**, in two shapes:
       - 8 are of the item-3 shape, with `e = (0, -3, 0)` and occurrences `(2, 3, 2)`. Item 3 applies to them. The
         small Sol/Klein search of `frontier_check.py` finds no first-step target for them. Whether one exists is
         open.
       - 128 have span 2 and a middle letter `a_1` that occurs **exactly once** (occurrences `(3, 1, 3)`), with
         `e_0, e_2 ∈ {±1, ±3}`. Here `B_n` is free on `a_n, a_{n+2}`, and the step is an amalgam along the whole
         rank-2 window `<a_n, W(a_n, a_{n+2})>`, which is not a free factor. No cyclic rule (1, R, N) and no
         retraction applies, since a rank-2 retract of `F_2` is all of `F_2`. Item 3 does not apply either.
3. **The frontier: no residually torsion-free-solvable target, at any length.** Let `r'` have span 2 and
   `e = (0, ε, 0)` with `ε ≠ 0`, and let `r'(1, y, z)` and `r'(x, y, 1)` both be conjugate to nonzero powers of `y`.
   All 18 frontier words of length 14 and the 8 of this shape at length 15 satisfy it (`frontier_check.py`,
   columns kill-lo and kill-hi).
   - Let `𝒮` be the class of groups with a finite normal series with torsion-free abelian factors, e.g.
     torsion-free nilpotent groups, free solvable groups, `Z^k ⋊ Z` and Sol lattices.
   - Then every map from `S_[0,n]` with `n ≥ 2` to a residually-𝒮 group kills all interior letters
     `a_1, …, a_{n+1}`.
   - So for `n ≥ 1` no residually-𝒮 group, in particular no free, residually torsion-free nilpotent, free
     solvable or poly-`Z` group, is a target for the step `S_[0,n] ⊂ S_[0,n+1]` in item 1 of the edge-injective
     lemma. That step is a cyclic HNN extension along words in `a_{n+1}, a_{n+2}`.
   - For the 18, `Hom(S_[0,n], Z) = {(0, w)}` on the window, and the edge functionals take only even values or 0
     on it, so rule R fails at every level.
   - **Sharp at the first step.** For each of the 18 words there is a map `S_[0,1] -> Z^2 ⋊_B Z` that is nontrivial
     on all four edge elements of the first two steps. Here `B = [[3,4],[2,3]]` (Sol, 8 words) or `B = -I`
     (10 words). So `S_[0,1] ∈ 𝓗` for all 18, but a solvable target stops working at the next step.
   - This is stronger than item 3 of the retract node in two ways. It has no bound on the solvable length,
     because the propagation hypothesis kills every interior letter once one dies. And it covers `ε = ±2`.
4. **Virtually-compact-special triage** (`vcs_triage.py`). The sufficient test is C'(1/6), which implies
   hyperbolic and cubulated (Wise), hence virtually compact special (Agol).
   - At length 14, C'(1/6) needs every piece to have length at most 2.
   - 0 of the 45 length-14 relators certified by rule R, rule N or the Nielsen search pass it: their maximal
     pieces have length 3 to 6.
   - 0 of the 18 frontier words pass it: their maximal pieces have length 3 or 4.
   - At length 15 the numbers are the same: 0 of the 142 relators that need rule R or rule N pass it, and 0 of
     the 136 open ones.
   - Negative immersions (Louder–Wilton, Linton) need primitivity rank above 2, which never holds for two
     generators.
   - So for none of these groups is membership in `𝓗` known to follow from Fisher–Sánchez-Peralta. For any that
     is virtually compact special by another route, only the crossed-product and positive-characteristic
     statements of `𝓗` are new. VCS is undecided for all of them, not refuted.

## What is new, and what is not

- **Nothing for the zero-divisor conjecture**, as for the retract node: torsion-free one-relator groups are locally
  indicable.
- **Hughes-free existence** in characteristic `p` and for crossed products over all division rings, for the 16
  rule-N relators of length 14, the 16 of length 15, and every relator of the item-1 shape at any length. It is also
  new for the 2 length-14 relators certified through a Nielsen image.
- **The mechanism.** The landed rules ask `Z` to see the edge. When the edge is a commutator, nothing abelian
  sees it, but a nilpotent target of growing class does, because taking roots in a Mal'cev completion is free.

## Where it stops

- The frontier is the 18 words of item 3. A target for their steps must lie in `𝓗` but not be residually 𝒮, so it
  cannot be residually torsion-free solvable. For example, it cannot be free, a RAAG or poly-`Z`.
- The candidates are groups in `𝓗` that are not residually solvable: one-relator groups already certified at
  length at most 13, or amalgams of poly-`Z` groups such as `S_[0,1]` (in `𝓗` by item 3). Folding maps
  `S_[0,n] -> S_[0,1]` that reflect the index fail, because a reflected triple `(j, j+1, j)` is not a relation.
- At length 15 a second shape appears: 128 words whose middle letter occurs once, so every step is an
  amalgam along a rank-2 window. That needs a target injective on a free group of rank 2, i.e. a rule of a
  different kind, and is open.
- Rule N is sound only with `α = β = 1`. Twists `a_2 = α^{-1} σ β^{-1}` change the leading terms and are not
  covered by the proof.
