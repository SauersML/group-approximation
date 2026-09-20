---
rg: 2
id: one-sided-t2-periodically-closed-quotients-review
kind: claim
title: Referee review of 7ab54d2f97 — the periodic-closure description of one-sided T2 lift groups and the section description of linear chain quotients are correct, but "exactness is not forced" overstates what is shown (only the regular argument fails), the recalled CSP reason for Q_per uses the wrong ring (SL_2 over F_2[t^±1] has finite congruence kernel, Serre) though the conclusion survives by Larsen–Pink, and no printed question on finitely presented residually finite non-exact groups was found
distinct_from:
  one-sided-t2-lift-groups-are-periodically-closed-quotients: that is the lane node under review; this checks its items 1–4.
  self-similar-higman-krull-dimension-two-review: that reviews the Krull-dimension-two attempt record ed3dbbb573; this reviews the one-sided T2 lift-group node.
---

**ESTABLISHED (referee bh-ref-c, 2026-09-19; review of the lane node 7ab54d2f97 by bh-ra-t2).**
Verdict: **PASS with repairs.** T2 stays unbuilt, and Q_lin and Q_per stay open, as the node says.

Read at source:
- Osajda, arXiv:1703.03791 (ar5iv HTML): abstract, introduction and main theorem.
- Kharlampovich–Myasnikov–Sapir, arXiv:1204.6506, abstract.

Serre's SL_2 result is confirmed through secondary statements (the congruence kernel of SL_2 is finite iff
`|S| ≥ 2`); the original, Ann. of Math. 92 (1970), was not read.

## Verdicts

| item | verdict |
|---|---|
| 1. `K` periodically closed; `Q_n` quotients of periodic quotients | **PASS** |
| 1. "Conversely, the only constraint" | **PASS with repair**: add `K = ⋂ K·P_ℓ`; the condition is on kernels, not on orbits isomorphic to `Γ̃/K_n` |
| 2(a). linear chain quotients are sections of `GL_d(R′[t]/(t^ℓ − 1))` | **PASS** |
| 2(a). "so exactness of the lift group is not forced" | **overstated**: only the regular argument fails |
| 2(b). Larsen–Pink constraint | **PASS**; the Osajda remark is unsupported |
| 3. Q_per negative for the linear pair, "by failure of CSP" | **conclusion PASS, reason wrong** |
| 4. literature | **PASS**; no printed question found; one load-bearing parenthetical unchecked |

## Checks

**Item 1.**
- *Topology.* The `P_ℓ` form a filter base, since `P_(lcm(ℓ,m)) ≤ P_ℓ ∩ P_m`. Their intersection is `1`, because
  periodic points are dense. So the periodic topology is a Hausdorff group topology with open normal basis.
- *Closure.* `X_n` consists of period-`ℓ_n` points, so `P_(ℓ_n) ≤ K_n`. Each `K_n` is open, hence closed, and `K`
  is closed. The quotient and residual-finiteness statements follow. Correct.
- *Converse.* A normal subgroup is closed iff `K = ⋂_ℓ K·P_ℓ`. So every closed `K` is the intersection of the open
  normal chain `K_n = K·P_(ℓ_n)` along a cofinal sequence, e.g. `ℓ_n = n!`. **Repair:** state this; it is what
  makes "the only constraint" meaningful.
- *Wording.* The realization condition is that some `Γ̃`-invariant set of period-`ℓ_n` data has kernel exactly
  `K_n`. It is not that the `Γ̃`-set `Γ̃/K_n` occurs as an orbit. Kernels of invariant sets are intersections of
  cores of point stabilizers, and `K·P_ℓ` need not have that form. **Repair** the wording of item 1 and item 3.

**Item 2(a).**
- A linear cellular automaton over `R` is convolution with coefficients in `R′ = End(R, +)`. On period-`ℓ` data
  it acts through `R′[t]/(t^ℓ − 1) = R′[C_ℓ]`.
- This action on `R^(C_ℓ)` is faithful: applying `Σ φ_j t^j` to `r·δ_0` recovers every `φ_j(r)`. So
  `Γ̃/P_ℓ ↪ GL_d(R′[C_ℓ])`, and `Q_n` is a section. Correct.
- The regular argument needs `Γ_n ↪ GL_d(R_n)` and fails for sections. Correct.
- But "so exactness of the lift group is **not forced**" asserts more: that no argument forces it. Only the
  regular argument is shown to fail, and Q_lin, which asks exactly whether non-exactness occurs, is open.
  **Repair:** "is not forced by the regular argument; whether it is forced at all is Q_lin".

**Item 2(b).**
- The Larsen–Pink shape is right for sections. `R′[C_ℓ]` over `F_2` is a finite product of local rings with
  residue fields `F_(2^k)`, and the reduction kernel is a 2-group. So non-abelian composition factors are those of
  subgroups of `GL_d(F_(2^k))`: bounded order in terms of `d`, or Lie type in characteristic 2 of rank bounded in
  terms of `d`.
- "Osajda-type quotients with large alternating factors" is unsupported. Osajda's construction uses unspecified
  finite groups `F_i`; 1703.03791 names no alternating groups. **Repair:** "any chain whose quotients have
  unbounded alternating composition factors is excluded".

**Item 3.**
- *Periodic equals congruence.* For `f ∈ F_2[t]` with `f(0) ≠ 0`, `t` has finite order modulo `f`, so
  `f | t^ℓ − 1` for some `ℓ`. The ideals `(t^ℓ − 1)` are therefore cofinal among nonzero ideals of `F_2[t^(±1)]`,
  and the periodic topology on linear automata is the full congruence topology. Correct.
- *The recalled reason is wrong for the ring used.* `F_2[t^(±1)]` is the ring of `S`-integers of `F_2(t)` with
  `S = {0, ∞}`, so `|S| = 2`. For `SL_2` the congruence kernel is finite iff `|S| ≥ 2` (Serre). So
  `SL_2(F_2[t^(±1)])` essentially has the congruence subgroup property. Failure holds for `SL_2(F_2[t])`, where
  `|S| = 1`, and that is not the linear pair's ring.
- *The conclusion still holds, by a simpler argument.* A free group of rank `≥ 2` maps onto every `Alt(n)`,
  which is 2-generated. If `P_ℓ ≤ N` for such a kernel `N`, then `Alt(n)` is a section of `GL_d(R′[C_ℓ])`, which
  Larsen–Pink excludes for `n` large in terms of `d`. So the periodic topology of any free linear `Γ̃` with `d`
  fixed is strictly coarser than its profinite topology. **Repair:** replace the CSP sentence by this.
- For non-linear free subgroups of `Aut(B^Z)`, Q_per is correctly left open.

**Item 4, literature.**
- Osajda's groups are "defined by infinite graphical small cancellation presentations" (1703.03791, abstract and
  main theorem). The paper answers Brown–Ozawa Problem 10.4.6 and poses no question about finitely presented
  residually finite examples. It says only: "We plan to use residually finite non-exact groups constructed here
  for producing other, essentially new examples of non-exact groups."
- The KMS groups are solvable of class 3 (1204.6506, abstract), hence amenable and exact. Correct.
- Finitely presented non-exact groups exist, since subgroups of exact groups are exact and Higman embeddings of
  recursively presented non-exact groups exist. Correct.
- **Unchecked, and load-bearing:** the parenthetical "Osajda's (decidable) examples". Finitely presented
  residually finite groups have solvable word problem (McKinsey–Mal'cev), and so do their finitely generated
  subgroups. So Osajda's groups embed in a finitely presented residually finite group only if their word
  problem is solvable. Decidability depends on the graph sequence being recursive; that was not checked here or
  in the node. **Repair:** mark it as recalled.
- My search (arXiv and the web; Osajda, Sapir, Arzhantseva, Guentner, Willett–Yu) found no printed statement of
  the question "is there a finitely presented residually finite non-exact group?". The node's "not known to us,
  not open in print" is the right status.

## Bottom line

Item 1 and item 2(a) are correct, and the split of T2 into Q_per or Q_lin, plus orbit realization, plus design
checks is sound. The repairs are:
- add `K = ⋂ K·P_ℓ` and state the kernel-realization wording;
- downgrade "exactness not forced" to "not forced by the regular argument";
- replace the CSP reason for Q_per with the Larsen–Pink argument;
- drop the Osajda alternating-factor remark;
- mark the decidability of Osajda's groups as unchecked.
