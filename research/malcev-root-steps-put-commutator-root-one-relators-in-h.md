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
  - experiments/amalgam-segment-steps-2026-09-17/census-L15.txt
  - experiments/amalgam-segment-steps-2026-09-17/frontier-L15.txt
  - experiments/commutator-root-preorders-2026-09-19/pre_sat.py
  - experiments/commutator-root-preorders-2026-09-19/runs.log
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

## Attempts

- **Pro-unipotent step (w12-059).** [[pro-unipotent-magnus-steps-put-one-relators-in-h]] takes the whole Magnus HNN
  step at once when `e_0 e_m ≠ 0`. It solves for the top letter in the completed free group of the window, so the
  base alone decides membership in `𝓗`.
  - All 128 words of the rank-2-window shape of item 2 at length 15 are then in `𝓗`.
  - The open part through length 15 is the 26 words of item 3: 18 of length 14 and 8 of length 15, all with
    `e = (0, ε, 0)`. That rule applies to them in no basis, because `H_1` of the kernel of `G -> Z` vanishes
    rationally.
  - Its targets are residually 𝒮, so item 3 here excludes them for the 26. `G(1, k)` is not residually 𝒮 and
    lies in `𝓗`, so family C targets remain allowed.
- **Global targets for the 26 (w13-059).** [[commutator-root-frontier-kills-pl-and-bi-ordered-targets]] rewrites
  all 26 words as `y_1^K = [y_0^α, y_2^β]`, which gives at most six groups. Each is in `𝓗` iff one map to `𝓗` keeps `y`.
  - PL groups of an interval kill `y` for all 26. This includes Thompson's `F`, which is in `𝓗` and not residually
    solvable.
  - Bi-orderable groups kill `y` for the 8 words with `(α, β) = (-1, 1)`.
  - Baumslag–Solitar groups kill `y` for all 26.
  - Open: `G(1, n)` targets and bi-orderings of `G(K; 1, ±1)`.
- **G(1, n) targets and order obstructions (w14-059).**
  - [[bg-chains-are-residually-tf-solvable-so-g1n-targets-die]] proves that every finite Baumslag–Gersten chain is
    residually 𝒮. So the kernel of `G(1, n) → Z` is locally residually 𝒮, and every map from the 26 words to
    any `G(1, n)`, `n ≠ 0`, kills the root. This closes the `G(1, n)` candidates for all `n`, including `|n| ≥ 3`.
  - [[commutator-root-minus-one-groups-have-generalized-torsion]] shows that in `G(K; -1, 1)` a product of
    `K^2 + K` conjugates of `y` is `1`. So the 8 words with `(α, β) = (-1, 1)` have no target without generalized
    torsion.
  - For `G(K; 1, ±1)`, a SAT test of bi-order consistency on word balls finds no certificate up to radius 4.
  - Open: bi-orderability of `G(2; 1, 1)`.
- **Bi-orderable targets for `G(K; 1, ±1)`: preorder SAT balls (w15-059).** Open. `G(2; 1, 1)` is still undecided.
  - **What was tested.** A map from `G` to a bi-orderable group with `y ≠ 1` is the same thing as a bi-invariant
    total preorder on `G` with `y > 1`. By compactness, if none exists, some finite set of the conditions T/M/C/S/Y
    in `experiments/commutator-root-preorders-2026-09-19/pre_sat.py` is already unsatisfiable. The script builds
    that clause set on the ball `B(W, r)`: reduced words of length at most `r` in `y_0, …, y_{W-1}`, merged by exact
    equality (Britton). Products are taken only with one factor of length at most `r1`. For `G(2; 1, 1)`, the
    `--chain` units add `y_i^k < y_{i+1}`, which item 4 of
    [[commutator-root-frontier-kills-pl-and-bi-ordered-targets]] forces.
  - **Results.** Every run is SAT (`runs.log`). So no obstruction to a target, and none to bi-orderability, is
    supported on these balls:
    - `G(2; 1, 1)`: `(W, r, r1) = (4, 5, 3)`, `(5, 5, 2)`, `(3, 6, 3)` and `(3, 7, 2)`, all with the chain.
    - `G(2; 1, -1)`: `(4, 5, 2)`.
    - `G(3; 1, 1)`: `(4, 4, 2)`.
    - `G(3; 1, -1)`: `(4, 4, 2)`.

    Calibration: the same script is UNSAT for `(2, -1, 1)`, which has generalized torsion.
  - **Forced shape of any order (proved, one line).** Let `a = y_0`, `b_0 = y_1` and `e_k = b_0^{-k} a b_0^k`.
    Conjugation by `t` sends `e_k` to `b_k = y_2^{-k} y_1 y_2^k`. Conjugation by `y_2` pushes each archimedean class
    `c_k` into `c_{k+1}`, and `b_k ∈ c_{k+1}`, so the classes of the `e_k` strictly increase. Hence
    `[a, b_0^k] = a^{-1} e_k` dominates `a` for `k ≥ 1`. On the free group `K = F(a, b_k : k ∈ Z)`, the kernel of
    `P = <y_0, y_1, y_2> → Z` (y_2-exponent), the order therefore has `γ_2 K` non-convex. That excludes every
    Magnus-type or nilpotent-lex order on `K`, although `K` does carry a `ψ`-invariant Magnus order with the right
    classes `c_k` (via `H_1(K) ⊂ Q a' ⊕ Q((s^{-1})) b`).
  - **Next.** Either build a `t`- and `y_2`-compatible non-Magnus order on `K` (candidate: germs or transseries under
    composition, where `[a, b]` can dominate `a`), or find an UNSAT ball with `W ≥ 4` and `r ≥ 6`. The latter needs
    a sparser product enumeration: `(4, 6, 2)` and `(3, 7, 3)` exceed 2 GB with the present one.
- **Hyperseries conjugators put `G(K; 1, ±1)` in 𝓗 (w16-059).** Resolved for 18 of the 26 frontier words, by
  [[hyperseries-conjugators-put-commutator-roots-in-h]] (written proof, unreviewed, on Bagayoko arXiv:2509.09186).
  - **Target.** The bi-ordered group `Γ` of positive infinite hyperseries under composition, in which all elements
    `> x` are conjugate. Using Abel functions, if `x < A < B` then some conjugator `c` with `A ∘ c = c ∘ B` lies
    below `x`.
  - **Tower.** This fixes the sign of each new letter. So `N_[0,∞)` of `G(K; 1, ±1)` maps into `Γ` with every
    letter on one side of `x`, which makes the map injective on every edge group. The edge-injective lemma and the
    shift isomorphisms then give `G ∈ 𝓗`, and reversing `t` gives the same for `(-1, -1)`.
  - **Not settled.** Bi-orderability of `G(2; 1, 1)` is still open, because the map ignores `t`. The preorder-SAT
    run `(4, 6, 2)` was dropped: it exceeds 2 GB.
  - **Left.** The 8 words with `(α, β) = (-1, 1)`. There the sign rule fails, and generalized torsion kills
    bi-orderable targets. Next: find an 𝓗-target with generalized torsion for `N_[0,3]` of `G(2; -1, 1)`, or prove
    that every such target kills `y`.
