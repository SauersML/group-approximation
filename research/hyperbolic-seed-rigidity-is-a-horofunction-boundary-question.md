---
rg: 2
id: hyperbolic-seed-rigidity-is-a-horofunction-boundary-question
kind: claim
title: The distance-gradient seed of a hyperbolic group is locally forced, so its SFT compactification is quantum rigid iff the horofunction boundary SFT is; this holds for trees of finite groups, and one-ended boundaries admit no finite-modification wall certificates
requires:
  - hyperbolic-groups-have-sft-horofunction-compactifications
  - quantum-rigidity-is-decided-on-the-derived-subshift
  - finite-type-branch-blow-ups-are-sft-compactifications
  - tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts
  - k-local-distance-functions-on-hyperbolic-groups-are-global
distinct_from:
  hyperbolic-groups-have-sft-horofunction-compactifications: that proves (C1) and (C2) for the distance-gradient SFT Y_k; this addresses the third condition for the class 𝒞, quantum rigidity, and reduces it to the boundary.
  quantum-rigidity-is-decided-on-the-derived-subshift: that is the general reduction for locally forced isolated points; this verifies its hypothesis for Y_k and records what is and is not known about the boundary.
---

**ESTABLISHED** (lane proof, bh-g2-buildings, 2026-09-18; elementary; not reviewed): parts 1–3.
**OPEN:** part 4, quantum rigidity of `∂_h` beyond trees of finite groups (surface groups included).

Notation: `Γ` hyperbolic, `S` finite symmetric, `k ≥ 13δ + 4`, and `Y_k` the distance-gradient SFT,
with seed `y_* = ∇d(·,1)`. By `hyperbolic-groups-have-sft-horofunction-compactifications`, `Y_k` is the
horofunction compactification `Γ ⊔ ∂_h`. Put `∂Y_k = Y_k ∖ Γ.y_*`. This is the SFT obtained by forbidding
the seed pattern, and it equals `∂_h`.

## 1. The seed is locally forced

This is in the sense of `quantum-rigidity-is-decided-on-the-derived-subshift`, with radius `ρ = R` from part
4(a) of `finite-type-branch-blow-ups-are-sft-compactifications` (`R ≥ max(k, k_C + 2)`, where `k_C` is
Cannon's tail length).
- **The step.** That proof deduces `f(g)` for `|g| = n+1` from `f = |·|` on `B_n(1)`. It uses one ball
  `B_R(g'')` whose centre `g''` lies on a geodesic `[1, g]`, and it reads only two things:
  - the values on `B_(k_C)(g'') ⊆ B_n(1)`;
  - the fact that every pattern of the language on `B_R(g'')` is a genuine distance pattern. Each such
    pattern extending these values has the same `k_C`-tail as `|·|` at `g''`, hence the same cone, hence
    value `|g|` at `g`.
- **Why this is local forcing.** This is one step of the forcing closure `F_(j+1)`. It reads the language on
  a single `ρ`-ball. So the closure exhausts `Γ` from `F_0 = B_R(1)`.

**Consequence.** By Corollary A of `quantum-rigidity-is-decided-on-the-derived-subshift`, `Y_k` is quantum
rigid at all large scales iff `∂_h = ∂Y_k` is. Membership of `Γ` in `𝒞` through this seed is exactly quantum
rigidity of the horofunction boundary SFT.

## 2. Trees of finite groups: rigid

Let `Γ = A_1 * … * A_m` be a free product of finite groups, not virtually cyclic, with
`S = ⋃ (A_i ∖ {1})`. Its Cayley graph is a tree of cliques.
- **The recoding.** For a distance-like `h`, the gradient at `v` records, in each clique through `v`, which
  vertex is the exit toward the target or centre. This is the finite-group compactification letter of
  `tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts` on each piece. The two codings determine
  each other on `B_1`.
- **Rigidity transfers.** A `D`-family for `Y_k` becomes a `(D−1)`-family for the glued `X^+` by products
  over `B_1`. The `Y_k`-letters are polynomials in the `X^+`-letters on `B_1`. So rigidity of `X^+` (the
  tree-gluing theorem, part 4) gives rigidity of `Y_k`.
- **Special cases.** The free group with a free basis is the case where the "cliques" are the edges of the
  tree. There, `∂_h` is the end shift (`free-group-boundary-shift-is-quantum-rigid`).

## 3. One-ended boundaries have no finite-modification wall certificates

Let `Γ` be one-ended, and let `x, z ∈ ∂_h` with `x = z` outside a finite set `F`. Then `x = z`.
- **Bellman equation.** Let `h, h'` be the horofunctions of `x` and `z`. They are distance-like (part 4 of
  `k-local-distance-functions-on-hyperbolic-groups-are-global`), so `h(v) = 1 + min_s h(vs)` at every
  vertex.
- **Descending paths leave `F`.** A descending path from `v ∈ F` is an infinite geodesic, so it leaves `F`.
  Hence `h(v) = min { length(π) + h(end π) : π a path from v leaving F }`, and likewise for `h'`.
- **Matching outside.** The gradients agree off `F`. The complement of `F` has one infinite component, and
  its finite components are handled by the same formula. So `h − h'` is a single constant outside `F`, and
  then on `F` too.

**Consequence.** The two-piece certificate of `rigid-subshifts-over-free-factors-are-tight-almost-everywhere`
(Lemma 1′) can never be fed by bounded pieces. A non-rigidity proof for `∂_h` would need two points whose
difference set splits into two far-apart *infinite* pieces.

## 4. Open: rigidity of ∂_h beyond trees

**Update (same day): SETTLED.** `hyperbolic-groups-lie-in-the-rigid-compactification-class` proves rigidity
for every hyperbolic group, with Gromov-product drop chains and window transport. Surface groups are also
covered by walls (`wall-chamber-distance-sfts-are-quantum-rigid`). The analysis below is kept as a record.

Three routes fail as they stand.
- **Tree chain.** The monotone chain `1 − A_i ≤ B_i ≤ 1 − A_(i+1)` needs the letter at an endpoint to be
  determined once the centre is known to lie beyond a junction. In a non-tree hyperbolic graph it is not:
  the local target has lanes (Webster–Winchester).
- **Determinism closure.** `determinism-closure-certifies-quantum-rigidity` cannot certify even the tree
  case. A letter is determined by `|S| − 1` neighbours, and the closure never leaves `B_(2D)`. Rigidity of
  the end shift is a monotone-chain phenomenon.
- **FP certificate.** `topologically-free-subshift-full-groups-force-quantum-rigidity` would give rigidity
  from finite presentation of `F(G_V × (Γ ⋉ ∂_h))`, when `Γ` has trivial finite radical, so that the action
  is topologically free. BBMZ (arXiv:2309.06224) embed `Γ` in a full contracting RSG on `∂_h`, and that RSG
  in a finitely presented simple group. They do not state that the V-stabilized full group itself is
  finitely presented. That import is the missing piece.

**Test case.** A closed surface group with its standard generators. Its Cayley graph is planar and
bipartite, so same-level points are at even distance. By `k-local-distance-functions-on-hyperbolic-groups-are-global`,
descents fellow-travel within `2δ+4`. So a monotone chain would have to run through bounded tubes
between lanes.

## Lesson for general BH

For hyperbolic groups the whole (★𝒞) package reduces to one statement: quantum rigidity of the horofunction
boundary SFT.
- The seed is free (locally forced).
- Finite type and density are theorems.
- Finite defects are impossible (Bellman).

Rigidity is known exactly where the boundary is a tree of cliques. Past trees, the obstruction is the lanes:
the same phenomenon that breaks Busemann merging. The next proof must carry commutation through bounded
tubes of parallel descents, not along single rays.

## Referee (bh-ref-hl, 2026-09-18): PASS for parts 1 and 3; part 2 PASS conditional on the tree-gluing rigidity theorem

This is an internal lane review.
- **Part 1 (local forcing).** This is the key step.
  - Take `g''` on `[1,g]` with `B_(k_C)(g'') ⊆ B_n(1)` and `g ∈ B_R(g'')`, so `R ≥ k_C + 2` suffices.
  - Any language pattern `β = d(·,q) + c` on `B_R(g'')` is genuine, because `Y_k = K_h` by
    `hyperbolic-groups-have-sft-horofunction-compactifications` (PASS, f2a29310d1).
  - If `β` has the same `k_C`-tail as `|·|` at `g''`, then Cannon's theorem, applied after translating by `q^(−1)`, gives it the
    same cone. So `β(g) − β(g'') = |g| − |g''|`.
  - This is exactly one step of the forcing closure `F_(j+1)`, and the extra agreement the closure imposes only strengthens the
    hypothesis. `F_0 = B_R(1)` isolates the seed by part (3) of the k-local node.
  - So Corollary A of `quantum-rigidity-is-decided-on-the-derived-subshift` applies. I did not referee that corollary.
- **Part 2 (trees of finite groups).** The recoding between `Y_k` letters and clique-exit letters is mutually local on `B_1`. This
  part rests on part 4 of `tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts`, which I have not reviewed.
- **Part 3 (Bellman).**
  - Seedless points have no sink, so descending paths are infinite geodesics and leave any finite `F`.
  - For one-ended `Γ`, take `F′ = F ∪` (the finite components of `Γ ∖ F`). Every path leaving `F′` ends in the infinite component,
    where `h − h′` is constant. So `h = h′ + c` on `F′`, and `x = z`. Correct.
- **Part 4.** It is OPEN as stated. I did not check the BBMZ remark (arXiv 2309.06224) at source.
