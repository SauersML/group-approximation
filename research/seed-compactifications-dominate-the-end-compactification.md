---
rg: 2
id: seed-compactifications-dominate-the-end-compactification
kind: claim
title: The difference set between a seed point and any translate coarsely connects the two seeds, so every seed compactification maps onto the Freudenthal end compactification; over groups with infinitely many ends the seed boundary has a perfect kernel mapping onto the end space, and scattered seeds exist only over one- or two-ended groups
requires:
  - tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts
  - quantum-rigidity-is-decided-on-the-derived-subshift
distinct_from:
  quantum-rigidity-is-decided-on-the-derived-subshift: that shows rigidity of a locally forced seed lives on its derived levels and perfect kernel; this shows where the perfect kernel must exist, namely over every infinitely ended group, and where it may vanish.
  seeds-never-survive-marked-approximation: that is a gluing-free isolation property of the group among marked groups; this is a gluing argument inside one group, across cuts of its Cayley graph.
  fp-v-times-subshift-full-groups-force-connected-differences: that forces coarse connectivity of difference sets from finite presentation of a full group; this forces it from the seed axioms alone, with no host and no rigidity.
---

**ESTABLISHED** (lane bh-star-a, 2026-09-18; elementary lane proof below; one referee PASS, bh-ref-engines 2026-09-18; no priority
claimed). Rigidity, density and finite presentation are not used.

## Setting

- `Γ` is finitely generated, with Cayley graph `Cay(Γ, S)` and word metric `d`.
- `Y ⊆ A^Γ` is an SFT whose forbidden patterns live on balls `B_r`.
- `y_* ∈ Y` satisfies (S1), with seed pattern `π` on `B_(R_0)`, and (S2), `Stab(y_*) = 1`, as in
  `tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts`.
- `Ȳ` is the orbit closure of `y_*`, and `∂Y = Ȳ ∖ Γ y_*`.
- For `g ∈ Γ`, `Δ(g) = {p : y_*(p) ≠ (g.y_*)(p)}` is the **difference set**.

## Theorem

1. **Separation lemma.** For every `g ≠ 1`, the sites `1` and `g` are joined by a path in `Cay(Γ, S)`
   inside `N_(2r)(Δ(g)) ∪ B_(R_0 + 2r) ∪ g B_(R_0 + 2r)`.
2. **End domination.**
   - Let `g_n → ξ` and `h_n → η` be sequences in `Γ` converging to distinct Freudenthal ends `ξ ≠ η`.
     Then `(g_n.y_*)` and `(h_n.y_*)` have no common accumulation point in `Ȳ`.
   - So the identity of `Γ` extends to a continuous, `Γ`-equivariant surjection
     `Φ : Ȳ → Γ ⊔ Ends(Γ)` with `Φ(∂Y) = Ends(Γ)`.
3. **Perfect kernels.**
   - If `Γ` has infinitely many ends, then `∂Y` is uncountable, and its perfect kernel `K` satisfies
     `Φ(K) = Ends(Γ)`, a Cantor set.
   - So a **countable (scattered) seed compactification exists only over groups with at most two ends.**

## Proof

**1.** Put `M = N_(2r)(Δ(g)) ∪ B_(R_0+2r) ∪ g B_(R_0+2r)`, and let `C` be the component of `M` containing
`1`. Suppose `g ∉ C`, and let `K_0` be the set of vertices outside `C` adjacent to `C`.
- `K_0` separates `1` from `g`.
- Every `k ∈ K_0` lies outside `M`, so `d(k, Δ(g)) > 2r`, `d(k, B_(R_0)) > 2r` and `d(k, gB_(R_0)) > 2r`.
- **The glued point.** Let `C_1 ⊇ C` be the component of `Γ ∖ K_0` containing `1`, and `N = N_(2r)(K_0)`.
  Define `x = y_*` on `C_1 ∪ N` and `x = g.y_*` elsewhere. On `N` the two agree, since `N ∩ Δ(g) = ∅`.
- **`x ∈ Y`.** Take a window `pB_r`. It has diameter `≤ 2r`. If it met both `C_1 ∖ N` and a point outside
  `C_1 ∪ N`, a path of length `≤ 2r` between them would cross `K_0` at distance `≤ 2r` from the first
  point, which is impossible. So `x` agrees on the window with `y_*` or with `g.y_*`, and every window of
  `x` is allowed.
- **Two seeds.** `B_(R_0)` is connected and misses `N`, so it lies in `C_1`, and `x` has the seed pattern
  at `1`. Likewise `gB_(R_0)` lies in the component of `g`, where `x = g.y_*`.
- **Contradiction.** By (S1) at both sites, `x = y_* = g.y_*`, so `g = 1` by (S2). ∎

**2.** Suppose `z` is a common limit of subsequences of both sequences.
- Choose a finite `K_0` such that `ξ` and `η` lie in different components `C_ξ ≠ C_η` of `Γ ∖ K_0`, and put
  `N = N_(2r)(K_0)`.
- Take `n` and `m` large. Then `g_n.y_*` and `h_m.y_*` agree with `z` on the finite set `N`, and
  `g_n B_(R_0) ⊆ C_ξ ∖ N` and `h_m B_(R_0) ⊆ C_η ∖ N`.
- Glue as in part 1: `x = g_n.y_*` on `C_ξ ∪ N`, and `x = h_m.y_*` elsewhere.
- The window argument gives `x ∈ Y`, with seeds at `g_n` and at `h_m`. So `g_n.y_* = h_m.y_*`, hence
  `g_n = h_m`, but they lie in disjoint components. This is a contradiction.
- **The map `Φ`.** For `z ∈ ∂Y`, write `z = lim g_n.y_*`. Then `g_n → ∞`: an isolated point with trivial
  stabilizer has a discrete free orbit. Pass to a subsequence converging to an end `ξ`, and set `Φ(z) = ξ`.
  - This is well defined by the first paragraph.
  - Continuity follows by a diagonal argument with the same uniqueness.
  - Equivariance is clear.
  - `Φ` is surjective, because every end is a limit of group elements and `Ȳ` is compact. ∎

**3.**
- `Φ(∂Y) = Ends(Γ)` is uncountable when there are infinitely many ends, so `∂Y` is uncountable.
- The scattered part `Ȳ ∖ K` of a compact metrizable space is countable, so `Φ(K) ⊇ Ends(Γ) ∖ (countable)`.
- `Φ(K)` is closed, and `Ends(Γ)` is a Cantor set, in which the complement of a countable set is dense.
  So `Φ(K) = Ends(Γ)`. ∎

## Calibration

- **`F_n`, tree seed.** `Φ` is a bijection on the boundary (the ends of the tree).
- **`Z`, `C_Z`.** Two ends, countable seed; `Φ(±∞) = ±∞`.
- **`Z^2`, `C_Z ⊠ C_Z`.** One end, countable seed of Cantor–Bendixson rank 3. It is allowed.
- **Master route.** `Λ_0 ∗ Z` has infinitely many ends. So the glued seed of bf61de7d0 always has a Cantor
  perfect kernel, carried by the Bass–Serre ends, and that kernel is where its rigidity must be proved.

## Consequences for CAP (v6 gate 1)

- **Where rigidity costs something.** Combine with `quantum-rigidity-is-decided-on-the-derived-subshift`
  (bh-invent-10): for a seed whose Cantor–Bendixson levels are locally forced, rigidity is decided on the
  perfect kernel `K`.
  - Over infinitely ended groups, `K` maps onto a Cantor set of ends, and rigidity is a genuine condition
    there. Compression codings (trees, `∂` of free products) are exactly how it has been paid.
  - Over one-ended groups, `K` may be empty. A scattered seed with locally forced levels is then rigid **for
    free** (bh-invent-10, Corollary B).
- **So CAP for rigid seeds contains a rigidity-free subproblem:**
  > (CAP_sc) Is the word problem of every finitely presented one-ended group carrying a scattered seed with
  > locally forced levels in one fixed class?
  - A single scattered, locally forced seed over a one-ended fp group with hard word problem refutes CAP,
    with no quantum argument at all.
  - Every CAP proof must cover such seeds by a purely combinatorial bound.
- **Passing to one-ended overgroups.** `𝒞` is closed under `× Z`, and `Λ_0 × Z` is one-ended for infinite
  `Λ_0`, so (SEED) loses nothing by assuming `Λ_0` one-ended. But a product seed `Y_0 ⊠ C_Z` keeps the
  perfect kernel of `Y_0`. Whether an infinitely ended `Λ_0` admits a scattered (non-product) seed after
  multiplying by `Z` is **open**. It is the first test of (CAP_sc).
- **Relation to the κ-bounds.** bh-invent-15's sandwich `log T_WP ≲ κ(n) ≲ |Ball(R(n+c))| · δ(2R+O(n))`
  (b970e40ae) holds for all seeds, scattered or not. So on the scattered side, ¬CAP needs the Dehn function
  or the forcing radius to grow. Linear-forcing seeds put everything into `δ`.

## Lesson for general BH

A seed must **see the ends** of its group.
- Across any finite cut, the seed point and its translates cannot be glued without creating a second
  origin. So every seed compactification refines the end compactification, and over infinitely ended
  groups it carries a Cantor perfect kernel, where rigidity has to be paid, by compression.
- Over one-ended groups nothing forces a perfect kernel, and a scattered seed is rigid automatically.
- So the quantum condition of CAP is live only on perfect kernels, which ends force. CAP's scattered part
  over one-ended groups is a purely combinatorial question about how much computation a countable,
  locally forced SFT compactification can carry.

## Referee (bh-ref-engines, 2026-09-18): PASS

- **Part 1 is correct.**
  - Points of `K_0` lie outside `M`, since a point adjacent to `C` and in `M` would be in `C`. So they are more
    than `2r` from `Δ(g)`, `B_(R_0)` and `gB_(R_0)`. The strict inequality gives `N ∩ Δ(g) = ∅`.
  - A window of diameter `≤ 2r` meeting both `C_1 ∖ N` and the outside of `C_1 ∪ N` would contain a geodesic
    crossing `K_0` within `2r` of its first point. So windows see only one of the two points.
  - `B_(R_0)` and `gB_(R_0)` are connected, miss `N`, and lie on opposite sides. The two seeds force
    `y_* = g.y_*`.
- **Part 2 is correct.**
  - The same gluing across a finite cut separating `ξ` from `η` gives the contradiction `g_n = h_m`.
  - `Φ` is well defined, continuous by the uniqueness plus a diagonal choice, equivariant, and onto: every end
    is a limit, and `Ȳ` is compact.
- **Part 3 is correct.**
  - The scattered part of a compact metrizable space is countable, and it contains the isolated orbit `Γy_*`.
  - So `K ⊆ ∂Y`, and `Φ(K)` is a closed set containing the cocountable, hence dense, part of the Cantor end
    space.
  - Scattered seeds therefore exist only over groups with at most two ends.
- **Dependence.** The CAP section (rigidity "for free" on scattered seeds) rests on
  `quantum-rigidity-is-decided-on-the-derived-subshift` (bh-invent-10, Corollary B), which I did not referee.
  So `(CAP_sc)` as a rigidity-free subproblem of CAP is conditional on that node.
- **Credit.** The cut-and-glue argument across a finite separating set is the one D. B. Cohen used to show that
  groups with more than one end carry no strongly aperiodic SFT (Adv. Math. 2017). This node extends it to seeds
  and to the end map, and should cite him. Also credit Freudenthal–Hopf for the end space.
