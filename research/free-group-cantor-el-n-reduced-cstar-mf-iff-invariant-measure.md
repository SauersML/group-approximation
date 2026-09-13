---
rg: 2
id: free-group-cantor-el-n-reduced-cstar-mf-iff-invariant-measure
kind: claim
title: "Operator-algebra form of the dichotomy: is C*_r(EL_N/Z) over LC(X,F_q) ⋊ F_r MF for large N exactly when X carries an invariant measure?"
distinct_from:
  free-group-cantor-elementary-group-lef-iff-invariant-measure: that is the group-level flagship (LEF versus no MF quotient); this asks for the same dichotomy at the level of the reduced C*-algebra, where the measure side requires strong convergence.
  measure-free-steinberg-el-n-reduced-cstar-not-mf: that is the established paradox-side half (necessity); this is the full equivalence, whose sufficiency half is open.
  directly-finite-subshift-el-n-reduced-cstar-is-mf: that is the subshift instance of the sufficiency half at n >= 4; this is the free-group Cantor equivalence for large N.
artifacts:
  - research/artifacts/un-reduced-cstar-2026-09-13-part1.md
---

**OPEN.** Let `F_r ↷ X` (`r ≥ 1`) be a minimal topologically free action on the Cantor set with
`R = LC(X,F_q)⋊F_r` finitely generated, and `S_N = EL_N(R)/Z`. Is it true that `C*_r(S_N)` is MF for all
sufficiently large `N` ⟺ `X` carries an `F_r`-invariant probability measure?

**Status.**
- **(⇒) holds.** `measure-free-steinberg-el-n-reduced-cstar-not-mf` (necessity corollary): with no invariant
  measure, `C*_r` is not MF from rank `2n` on.
- **(⇐) is open.** For `r = 1` and a minimal subshift it would exhibit an infinite Kazhdan group with MF reduced
  algebra. So it is at least as hard as the root `infinite-kazhdan-group-with-mf-reduced-cstar`, and it feeds that root
  through `kazhdan-mf-reduced-from-measure-side-el-n`.
- **Tracial invariants don't separate.** `C*_r(S_N)` is separable, stably finite and has a unique trace on both sides.
  At the reduced level only MF can see the dichotomy.

## Attempts

- **Genuine representations (2026-09-13, un-reduced-cstar). Dead.** `S_N` has no nontrivial finite-dimensional
  unitary representations (`minimally-almost-periodic-groups-are-not-pmf`), so no PMF approach exists.
- **Ring-induced LEF models inside regular or permutation representations. Dead.** An exactly invariant column
  vector for a non-amenable stabilizer gives norm 1 against a Kesten norm below 1
  (`ring-model-permutation-vectors-block-strong-convergence`).
- **What survives.** Asymptotic representations with three properties at once:
  - normalized traces tending to `δ_e` (automatic for MF embeddings by BKKO, artifact Rem. 6);
  - no almost invariant vectors for non-amenable subgroups;
  - no norm outliers above `‖λ(z)‖`.

  The lower bound is automatic from trace convergence (artifact Prop. 5).
  - Candidate: cuspidal-type irreducible representations of the finite models `F_i ⊆ SL_{NN_i}(F_i)`, with character
    bounds for trace decay. Heuristic only.
  - The missing step is a deterministic no-outlier theorem. Random-permutation methods (Bordenave–Collins) apply only
    to free groups.
