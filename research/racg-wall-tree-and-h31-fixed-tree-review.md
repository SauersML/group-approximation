---
rg: 2
id: racg-wall-tree-and-h31-fixed-tree-review
kind: claim
title: Referee review of 453c3bacb1 and 7c66976316 — Proposition F applies Theorem D correctly at the level of vertices and survives at the level of shadows (repair supplied), but its claim for the host of W_Petersen * Z is unsupported, since Theorem D covers right-angled Coxeter groups only; the fixed-tree reduction for H_31 (cocycle lemma, the free generator is never singular, the degree computations) is correct
distinct_from:
  racg-generators-are-singular-over-their-wall-trees: that is the lane node 453c3bacb1 under review; this checks its use of Theorem D.
  generalized-triangle-group-hosts-reduce-to-fixed-trees: that is the lane node 7c66976316 under review; this checks its reduction step and the fixed-tree computations.
  one-sided-t2-periodically-closed-quotients-review: that reviews bh-ra-t2's lift-group node; this reviews bh-q12-kazhdan's two nodes.
---

**ESTABLISHED (referee bh-ref-c, 2026-09-19; review of two lane proofs by bh-q12-kazhdan).**
- 453c3bacb1 (`racg-generators-are-singular-over-their-wall-trees`): **PASS with repairs.**
- 7c66976316 (`generalized-triangle-group-hosts-reduce-to-fixed-trees`): **PASS.**

Read at source: Caprace–Conder–Kaluba–Witzel, arXiv:2011.09276 (ar5iv HTML), Theorem 1.2 and the text after it.
- The relations include `a^5, b^5, c^5, [a,c], [b,c,b], [b,c,c,b], [b,c,c,c]`.
- `⟨a,b⟩ ≅ PSL_2(31)`, `⟨c,a⟩ ≅ C_5 × C_5`, and `⟨b,c⟩` is a 5-Sylow subgroup of `Sp_4(5)`, of order `5^4`.
- The action on the CAT(−1) triangle complex is geometric and sharply transitive on triangles, with edge stabilizers
  cyclic of order 5.

## 453c3bacb1: Proposition F

### The Theorem D application at the level of vertices: PASS
- **Genericity.** `r_0 = s` and `g = s`, and `H_s` is the only wall separating `1` from `s`. So every `ζ ∈ ΛH_s`
  is generic, and `a = ℓ_s(σ_+) = 1`.
- **The ray.** Distinct involutions of the free product `W_(lk(s))` never commute, so the walls `C_i` are pairwise
  non-crossing, not only consecutive ones. They are nested, `u_j` is on the `1`-side of `H_s`, and
  `δ_1(C_(j+1)) = j + 1`. The walls `C_(j+1)` cross `H_s`, since `u_j` centralizes `s`.
- **The outer wall.** `x ∈ lk(t_j) ∖ {s}` lies outside `st(s)` (no triangle) and outside `lk(t_(j−1))` (no 4-cycle
  `s, t_(j−1), x, t_j`). Its reflection is `u_j x u_j^(-1)`.
  - It does not commute with `s`, so `O` does not cross `H_s`.
  - Conjugating the reflection of `C_j` by `u_j^(-1)` gives `t_(j−1)`, which does not commute with `x`. So `O`
    does not cross `C_j`.
  - `O` is a (+)-wall of depth `j + 1`, as claimed.
- **Two points.** `u_(j+1)x = u_j x t_j`, so `O` is dual to both edges. The disagreement sets with `σ_+` are
  `{C_(j+2), …}` for `u_(j+1)` and `{O, C_(j+2), …}` for `u_(j+1)x`, by symmetric difference. Both points lie in
  `Z'`.

### Repair A: witnesses at the level of shadows
Theorem D is a statement about shadows. `E_n` and `Z_m` are shadows of infinite atoms, and "cuts" has to mean that
both sides contain boundary points. The node exhibits vertices, and a bounded vertex-level cut does not change a
shadow. The needed witnesses exist.
- **(ii), every `|lk(s)|`.** Let `ρ = u_j x u_j^(-1)` be the reflection in `O`. Then `ρσ_+ ∈ Z'` lies on the far
  side of `O`.
  - Walls crossing `O` are preserved by `ρ`, with their sides. Their reflections commute with `ρ`, and each side
    contains a fixed point of `ρ` on `O`.
  - Walls lying on the near side of `O` and not crossing it are constant on all of `O^(¬1)`. They are satisfied
    there because `u_(j+1)x` satisfies them.
  - Walls inside `O^(¬1)` have depth `≥ j + 2`, so they are not constraints of `Z'`.
- **(i), when `|lk(s)| ≥ 3`.** Pick `t′ ∈ lk(s) ∖ {t_(j−1), t_j}` and follow the branch of `T_s` from `u_j`
  through `t′`. Its limit disagrees with `σ_+` only on walls of depth `≥ j + 1`. It lies in `Z_j(σ_+)` on the
  `u_j`-side of `C_(j+1)`, while `σ_+` is on the other side.
- **(i), when `|lk(s)| = 2`.** No witness is written down. The four-point count for the pentagon rests on the
  calibration against `gq-bh-finf-hyp-cone-matching-test.md`, which agrees.
- So the continuum conclusion for the Petersen graph, where `|lk(s)| = 3`, holds once these witnesses are added.

### Repair B: `W_Petersen ∗ Z` is not covered
- Theorem D and Proposition F are stated for a right-angled Coxeter group with its standard generators. The BBMZ
  host is built on `Γ ∗ Z`, which is not a right-angled Coxeter group; `Γ ∗ D_∞` is one, but it is a different
  group.
- So "(and of `W_Petersen ∗ Z`) is not bounded" needs a transfer lemma. It would say that, near points of the root
  copy of `∂Γ`, the atoms of `Γ ∗ Z` restrict to the wall cylinders of `Γ`, with the same depths.
- This is plausible, because offsets of `s ∈ S_Γ` depend only on the first `Γ`-syllable, as in Lemma 2 of
  7c66976316. It is not proved.
- **Repair:** prove it, or restrict the claim to the host of `W_Petersen` itself. This matters, because the host
  that counts is the one on `Γ ∗ Z`.

### Other points
- **The corrected SCC criterion** of Theorem E is not used. The continuum conclusion is consistent with it: it
  forces a reachable nontrivial component that is not a single cycle.
- **"`|lk(s)| ≤ 2` gives finite"** uses Theorem A together with finiteness of the fibers of `φ` for hyperbolic
  groups. The latter is recalled (Webster–Winchester); cite it.
- **The Menger-curve boundary** of `W_Petersen` is recalled and not load-bearing.

## 7c66976316: the reduction to fixed trees

- **Lemma 1 (cocycle): PASS.** Suppose `y` is regular for `h`. Then `h∂D = ∂D′` for the level-`n′` shadow
  containing `hy`, with `|n − n′| ≤ |h|` by Proposition C. Since `n′ → ∞`, regularity of `g` at `hy` applies to
  `D′`. The word form follows by induction, and so do the countable and finite forms.
- **Lemma 2 (`sing(t) = ∅`): PASS.** `d(t,v) − d(1,v) = −1` exactly when the normal form of `v` starts with a
  positive power of `t`, and `+1` otherwise. First syllables are eventually constant towards every point of `∂H`:
  - points of the boundaries of copies of `G`;
  - ends of the Bass–Serre tree;
  - `t^(±∞)`, where the sign is eventually constant.

  So `ℓ_t = lim f(x_k)` is constant on each fiber, `F'_t = ∅`, and Theorem A applies.
- **Corollary 3, the reduction step: PASS.** By Lemma 1, applied with the host's own generating set, an element
  with uncountable singular set exists iff some generator has one. `t^(±1)` are excluded by Lemma 2.
  - The same offset argument puts `F'_s`, for `s ∈ S_G`, inside the boundary of the root copy. This is consistent
    with Conjecture 5.
  - The reduction also holds with all nontrivial edge-group elements as generators.
- **Proposition 4: PASS.** I checked each count.
  - *Sylow 5-subgroups of `PSL_2(31)`.* They have order 5, since `|PSL_2(31)| = 2^5·3·5·31`, and sit in split tori
    of order 15. Their normalizer is `D_30`, so each of `⟨a⟩` and `⟨b⟩` contributes `30/5 = 6` fixed cosets.
  - *The group `B`, of order `5^4`.* It has class 3, with `γ_3 = ⟨[b,c,c]⟩`.
    - The class of `b` has size 5, so `|C_B(b)| = 125`.
    - The class of `c` is `cγ_2`, of size 25, since conjugation by `b` and by `[b,c]` move `c` in independent
      directions. So `|C_B(c)| = 25`.
    - `⟨x⟩ ∩ xγ_2 = {x}` gives `N_B(⟨x⟩) = C_B(x)`. The counts are 25 and 5.
  - *The group `C`.* It is abelian, which gives 5 fixed cosets and 0.
  - *Fixed sets.* The action is free on triangles and preserves types, so fixed sets lie in the 1-skeleton. They
    are convex, hence trees, and locally finite of minimum degree 5, so their boundaries are Cantor sets embedded
    in `∂X`.
- **"Why Proposition F does not transfer"** is labelled as resting on recalled facts: Niblo–Roller, and the
  cocompact-stabilizer step. That labelling is correct. It is motivation, not proof.

## Bottom line

- The reduction of the Kazhdan question to the three order-5 generators of `𝓗_31`, and to their Cantor fixed trees,
  is sound. Conjecture 5 is correctly posed.
- The Petersen control holds for the host of `W_Petersen` once Repair A's witnesses are added.
- The claim for the host of `W_Petersen ∗ Z` needs Repair B.
