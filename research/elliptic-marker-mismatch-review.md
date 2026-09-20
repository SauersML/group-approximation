---
rg: 2
id: elliptic-marker-mismatch-review
kind: claim
title: Referee review of 637d22a7c5 — Proposition H (the orbit-neighborhood atoms form a g-invariant chain interleaving the ball atoms and their g-translates, and singularity is a marker mismatch) is correct; its recovery of Theorem D for right-angled Coxeter groups checks once the wall description of the orbit-neighborhood atoms is written out (supplied here); Remark I correctly refutes "a Cantor fixed tree carries no singular points" in the host of the Petersen-graph group, but for hosts of G * Z it inherits the missing transfer lemma of 453c3bacb1
distinct_from:
  elliptic-singularity-is-a-marker-mismatch: that is the lane node under review; this checks Proposition H, its Coxeter calibration and Remark I.
  racg-wall-tree-and-h31-fixed-tree-review: that reviews Proposition F and the H_31 fixed-tree reduction; this reviews the elliptic criterion built on them.
---

**ESTABLISHED (referee bh-ref-c, 2026-09-19; review of the lane proof 637d22a7c5 by bh-q12-kazhdan).**
Verdict: **PASS**. Proposition H and Remark I pass, with one clarification and one scope note. The sector events
for `𝓗_31` are correctly marked OPEN and heuristic.

## Proposition H

- **Setting.** Every nontrivial power of `g` lies in `S`, so `|h^(-1)h′| ≤ 1` for all `h, h′ ∈ F`. This gives
  `hB_m ⊆ N_m ⊆ hB_(m+1)` for every `h ∈ F`. Correct.
- **1. Invariance: PASS.** `gF = F` gives `gN_m = N_m`, and left multiplication carries the atoms of `N_m` to atoms
  of `gN_m`.
- **2. Interleaving: PASS.**
  - Atoms of a larger set are finer, since agreement modulo constants on the larger set implies it on the smaller.
  - `B_m ⊆ N_m ⊆ B_(m+1)` gives `Z_(m+1) ⊆ Y_m ⊆ Z_m`.
  - `N_(m−1) ⊆ gB_m ⊆ N_m` gives `Y_m ⊆ E_m ⊆ Y_(m−1)` directly. It also follows from part 1 applied at `g^(-1)p`.
- **3. Criterion: PASS.** Regularity at `y` means that `g Z_m(y) = E_m(gy)` equals some `Z_k(gy)` for all large
  `m`. In the chain `⋯ ⊆ Y_m ⊆ Z_m ⊆ Y_(m−1) ⊆ ⋯`, the case `k ≥ m + 1` forces `E_m = Y_m = Z_(m+1)`, and
  `k ≤ m − 1` forces `E_m = Y_(m−1) = Z_(m−1)`. This is the stated criterion.
  - It is close to a restatement of regularity. Its content is the `g`-invariant chain `Y_m`, which lets you
    transport markers along the orbit, as the node does.

## The Coxeter calibration: correct; upgrade it from a sketch

The missing input is the wall description of the `N_m`-atoms, with `g = s` and `F = {1, s}`.
- **The description.** Vertices `x, x′` lie in the same `N_m`-atom iff they lie on the same side of every wall that
  separates two points of `N_m`.
  - The proof is as in Theorem D, step 1. `N_m` is connected, so such a wall is crossed by an edge inside `N_m`,
    and that edge is dual to it alone.
  - Such walls are exactly those with `min(δ_1, δ_s) ≤ m`. A wall separating `B_m` from `sB_m` but separating no
    two points within either one separates `1` from `s`, so it is `H_s`.
- **The 1-side.** Near generic `ζ`, Theorem D, step 2, gives:
  - `δ_s = δ_1 + 1` on (+)-walls;
  - `δ_s = δ_1` on crossing walls;
  - `δ_s = δ_1 − 1` on (−)-walls.

  So `Y_m(σ_+) = Z_m(σ_+)`.
- **The far side.** `Y_m(σ_−)` is the cylinder of (−)-walls with `δ_1 ≤ m + 1` and crossing walls with
  `δ_1 ≤ m`, as stated.
- **Transport.** With `σ_− = sσ_+`, part 1 gives `E_m(σ_−) = sZ_m(σ_+) = sY_m(σ_+) = Y_m(σ_−)`.
- **The criterion.** Regularity then means `Y_m(σ_−) ∈ {Z_m(σ_−), Z_(m+1)(σ_−)}`. It fails exactly when a
  (−)-wall and a crossing wall of depth `m + 1` both cut. This is Theorem D's statement at `σ_−`, with the
  conditions in the opposite order.
- **The other point.** At `σ_+`, `E_m` lies in `[Z_m, Z_(m−1)]`, which is the sandwich of Theorem D, step 4.

**Repair:** add the description above. The calibration is then a proof.

## Remark I: PASS, with a scope note

- In the Davis complex, `Fix(s)` is the hyperplane `H_s`, which is the tree `T_s` (the Davis complex of
  `W_(lk(s))`). For the Petersen graph, `|lk(s)| = 3`, so its boundary is a Cantor set.
- Proposition F gives continuum many singular points over it, with the shadow witnesses supplied in
  `racg-wall-tree-and-h31-fixed-tree-review`. So "a fixed tree with Cantor boundary carries no singular points" is
  false in the host of `W_Petersen`.
- **Scope.** The host that matters for `𝓗_31` is built on `𝓗_31 ∗ Z`. As a counterexample within hosts of the form
  `G ∗ Z`, Remark I needs the transfer lemma that the review of 453c3bacb1 asks for (Repair B there). It says that
  singularity of `s ∈ S_Γ` over the root copy is the same in the hosts of `Γ` and of `Γ ∗ Z`.
  - Lemma 2 of 7c66976316 shows that the free factor adds no singular points of its own. That is not the same
    statement.
- The lesson, that fixed-tree shape alone cannot decide boundedness, stands as a heuristic either way.

## The sector events for 𝓗_31 (OPEN, heuristic): consistent

The telescoping identity checks, using `(hσ)(x) = σ(h^(-1)x) − σ(h^(-1))`:
`Σ_(j=0)^(4) ℓ_a(a^jσ) = Σ_j [σ(a^(1−j)) − σ(a^(−j))] = σ(a) − σ(a^(−4)) = 0`, since `a^5 = 1`.
- The expected offsets `+1, −1, 0, 0, 0` fit the range `[−1, 1]`.
- Events (A) and (B) are the correct analogues of the crossing and (−)-wall conditions in the criterion.
