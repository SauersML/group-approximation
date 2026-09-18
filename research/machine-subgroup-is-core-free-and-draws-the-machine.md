---
rg: 2
id: machine-subgroup-is-core-free-and-draws-the-machine
kind: claim
title: The Aanderaa–Cohen machine subgroup T'_M ≤ K_M is core-free, and its Schreier graph contains a base sheet Z² on which r_i, l_j act by the machine's multiplicative maps and t has loops exactly over −H_0(M); the natural relative seed (sheet + transported fate bit) is isolated with stabilizer T'_M for total machines but is never quantum rigid once two unterminated components of the move graph sit 2D apart
requires:
  - aanderaa-cohen-tower-subgroups-are-decidable
  - relative-seeds-descend-to-quotients-and-consume-membership
distinct_from:
  aanderaa-cohen-tower-subgroups-are-decidable: that proves membership in T'_M is decidable (≡_T H_0(M)); this shows T'_M is core-free (so descent cannot simplify the rung), describes its Schreier graph, and tests the first relative-seed candidate against isolation, (S3) and rigidity.
  higman-clapham-towers-leave-the-seed-form-at-three-steps: that locates the halting HNN as a step of the tower; this analyses the relative seed that the step needs.
---

**ESTABLISHED** (lane proof, bh-free-56, 2026-09-18; not reviewed) for items 1–2 and the rigidity part of item 3.
The isolation and (S3) parts of item 3 are lane sketches. The notation is that of
`aanderaa-cohen-tower-subgroups-are-decidable` (Chiodo–Vyas, arXiv:1604.03788, §4.1):
- `z = x^r y^s ↔ (r, s) ∈ Z²`;
- `z^{-1} t(q) z = t(q + z)`;
- `D_i = K^{m,m}_{a_i,b_i}`, with lattice `Λ_i = mZ × mZ`;
- `φ_i(um, vm) = (um², v)`, with image lattice `Λ'_i = m²Z × Z`.

Type-L quadruples are symmetric throughout.

## Statement

1. **Core-free.** For every `1 ≠ n ∈ T'_M`, some conjugate of `n` by a power of `x` or of `y` lies
   outside `T'_M`. So `T'_M` contains no nontrivial normal subgroup of `K_M`. The descent of
   `relative-seeds-descend-to-quotients-and-consume-membership` gives nothing, and the rung
   `(K_M, T'_M)` is genuinely core-free.
2. **The base sheet.** The cosets `T'_M z` (`z ∈ Z²`) are pairwise distinct. Their Schreier edges are:
   - `x`, `y`: the grid of `Z²`;
   - `t`: a loop at `z` iff `−z ∈ H_0(M)`;
   - `r_i`: from `z` to `φ_i(z)` for `z ∈ Λ_i`, and off the sheet otherwise. `r_i^{-1}` goes from `z` to
     `φ_i^{-1}(z)` for `z ∈ Λ'_i`, and off the sheet otherwise.

   The move of quadruple `i`, `p = (um + a_i, vm + b_i) ↦ μ_i(p) = (um² + c_i, v)`, is the bounded word
   `x^{a_i} y^{b_i} r_i x^{-c_i}`. It joins the sheet points `−p` and `−μ_i(p)`. So the sheet is the
   machine's configuration graph, drawn with bounded steps, with loops exactly over its halting basin.
3. **First candidate.** Let `W` have the following layers:
   - on-sheet or off-sheet;
   - a `C_Z × C_Z` sign layer and residues mod `m³` on the sheet;
   - pointers toward the sheet elsewhere, as in the gluing of `relative-seeds-glue-graphs-of-groups-into-class-c`;
   - a fate bit `β` on the sheet.

   The bit has three rules: (T) `β(−p) = β(−μ_i(p))` along every move word; (H) `β = 1` at the origin; (N) `β = 0`
   at every non-origin terminal residue. The `t`-edge at a sheet point is a loop iff `β = 1`.
   - **(S1), (S2) (sketch).** If `M` is total, the seed at the identity forces every layer: the fate bit
     is forced along each finite run from its terminal. The stabilizer is `T'_M`.
   - **(S3) (sketch).** Density holds iff the machine satisfies (FS). (FS) says: every finite family of
     unterminated run germs at infinity, with fates constant along merges, is jointly realized by
     genuine configurations far from the origin.
   - **Rigidity fails.** Suppose some point of the base layers contains two unterminated components `A`, `C` of the
     move graph (maximal unions of runs joined by moves, with no terminal) that stay at distance `> 2D`. Then `W` is not `D`-quantum rigid. Such points exist, for
     example, whenever runs of unbounded length occur in two separated regions of one far window.

## Proof

**1.**
- *In `K`.* `T'_M ∩ K = T_M = F_{H_0}` with `H_0 ⊆ N²`. Let `1 ≠ n ∈ T_M`. Conjugation by `x^{-a}`
  shifts every letter index by `(−a, 0)` and keeps the word reduced. For `a` large, some index leaves
  `N²`, so the conjugate is not in `T_M`, and it lies in `K`.
- *Outside `K`.* Let `n ∈ T'_M ∖ K`. By goodness, its reduced form is
  `n = τ_0 s_1^{ε_1} τ_1 ⋯ s_k^{ε_k} τ_k` with `τ_j ∈ T_M` and `k ≥ 1`. Choose `w ∈ {x, y}` outside the
  lattice of `E_1` (`Λ_i`, `Λ'_i`, or its L-analogue; one of `x, y` always works since `m ≥ 2`).
  - Then `w n w^{-1} = (w τ_0) s_1^{ε_1} ⋯ (τ_k w^{-1})` is still reduced.
  - The first test of the good-subgroup algorithm fails: `w τ_0 ∈ T_M E_1` would force the
    `Z²`-part `w` of `w τ_0` into the lattice of `E_1`, because `T_M` has trivial `Z²`-part.
  - So `w n w^{-1} ∉ T'_M`.

**2.**
- *Distinct cosets.* `T'_M z = T'_M z'` iff `z' z^{-1} ∈ T'_M ∩ Z² ⊆ T ∩ Z² = 1`.
- *`t`-edges.* `T'_M z t = T'_M t(−z) z`, since `z t z^{-1} = t(−z)`. This equals `T'_M z` iff
  `t(−z) ∈ T'_M ∩ K = F_{H_0}`, iff `−z ∈ H_0`.
- *`r_i`-edges on the lattice.* For `z ∈ Λ_i`, `z ∈ D_i`, so `z r_i = r_i φ_i(z)` and
  `T'_M z r_i = T'_M φ_i(z)` because `r_i ∈ T'_M`.
- *`r_i`-edges off the lattice.* For `z ∉ Λ_i`, `z r_i z'^{-1}` is reduced with first test `z ∈ T_M D_i`.
  This fails on the `Z²`-part, so the edge leaves the sheet.
- *The move word.* `−p + (a_i, b_i) = −(um, vm) ∈ Λ_i`. Then `φ_i` sends it to `(−um², −v)`, and
  `x^{-c_i}` gives `−μ_i(p)`.

**3, rigidity.** Fix a classical point `y` of the base layers with components `A`, `C` as stated. On
`ℓ²`-space, let the base site projections be the scalars given by `y`. The bit at any site of a
terminated run is the forced scalar. Assign the bit projection `P` to every site of `A`, the projection
`Q` to every site of `C`, and `0` to the other unterminated components, with `PQ ≠ QP`.
- **Q1** holds at every site.
- **Q2 (commutation at distance `≤ 2D`)** holds, since `A` and `C` never come within `2D` and every
  other operator is a scalar.
- **Q3** holds, since every rule is killed in each classical specialization.
  - Rule (T) relates sites of one component only, and exact transport gives one projection per
    component.
  - Rules (H) and (N) never touch an unterminated component.
  - A forbidden pattern has diameter at most the rule radius, which is at most `2D`, so it never meets
    both `A` and `C`.
- So this is a non-commuting `D`-family, and `W` is not `D`-quantum rigid. `∎`

## What this says for CAP

**The rung is honest.**
- `T'_M` is core-free, finitely generated, and has membership `≡_T H_0(M)`.
- Its Schreier graph is the machine itself: a Baumslag–Solitar-type sheet whose multiplicative edges
  are the moves.
- Any rigid relative seed for it computes `H_0(M)`, and nothing can be pushed into a quotient.

**The minimal candidate fails exactly at infinity.**
- A transported fate bit is forced along finite runs, so isolation is fine. It is free along runs that
  never terminate inside the far field.
- Those runs are unavoidable once running time is unbounded, and that is the regime CAP cares about.
- Their bits are independent, and independent bits give non-commuting quantum families.

**What a rigid candidate must do.**
- (S3) needs both fates to occur as limits at infinity, while rigidity forbids independent fates on
  far-apart runs.
- So a rigid candidate must couple the fates of neighbouring runs by deterministic, permutive relations
  that genuine computations satisfy.
- In practice the layer must carry the computation itself, as a reversible permutive space-time layer
  (SYNTHESIS gate 4, as bh-star-a noted). A bit summarizing the computation's outcome is not enough.

## Lesson for general BH

Computing in a rigid seed cannot mean storing answers. It must mean storing the whole computation in a
layer that is deterministic in enough directions. The halting HNN of the Aanderaa–Cohen tower has an
honest, core-free relative-seed problem whose Schreier graph is the machine. The first candidate,
propagating the fate of each run as a bit, is isolated and has the right stabilizer. Rigidity
nevertheless fails on unterminated runs at infinity, because answers on runs that never meet are free.

So CAP is now a question about rigid, permutive encodings of unbounded computations coupled to a
Baumslag–Solitar-type sheet. There is a dichotomy:
- either such encodings exist, and they must realize both fates as limits (S3), so CAP is false;
- or the far field of every rigid seed is finite-state, and the forced point computes only what
  bounded local data decide.
