---
rg: 2
id: coset-lifts-are-tube-sft-fixed-points-proof
kind: route
title: Sequential single-site lifts along <e> plus compactness give a nonempty tube set; freeness of <e> on the tube makes it a Z-SFT with e as shift; a phase-alternation tube shows the axioms give period 2 but not period 1
target: coset-lifts-are-tube-sft-fixed-points
requires:
  - post-surjective-sft-covers-admit-scheduled-sections
  - cover-pair-sections-localize-to-the-symmetric-locus
artifacts:
  - research/artifacts/coset-lift-tube-shifts-2026-09-20.md
  - experiments/coset-lift-tubes-2026-09-17/phase_tube.py
---

A complete, elementary proof. It is in Sections 1–3 of the artifact.

1. **Nonempty (T1).** Apply the translated single-site lifts `L_{e^j}` for `j = 0, 1, -1, 2, ...`. By Lemma 1 of
   the scheduled-sections artifact, quoted verbatim in artifact Section 0, each lift:
   - stays in `X`;
   - changes the point only on `e^jΦ`;
   - changes the output only at `e^j`.

   A limit point, which exists by compactness, lies in `Σ_Φ ⊆ Σ_K`.
2. **`e`-action (T2).** `x` and `F(x)` are `e`-invariant, and `e⟨e⟩K = ⟨e⟩K`.
3. **`Z`-SFT (T3).** If `e` has infinite order, `(j, r) ↦ e^j k_r` is a bijection `Z × R → ⟨e⟩K`.
   - Windows `gW` and memories `hM` that meet the tube read at most `D + 1` consecutive columns. The reason is that
     `e^n ∈ K W^-1 W K^-1 ∪ K M^-1 M K^-1` forces `|n| ≤ D`.
   - They come in finitely many types modulo `e`, and each type is translation invariant because `x ∈ Fix(e)`.
4. **Periods (T4).** A nonempty `Z`-SFT has a cycle in its `D`-block graph, which has at most `|A|^{D|K|}`
   vertices.
5. **Fixed points (T5).** Fixed points of the shift are constant sequences. Each block condition reads `x` on
   `K W^-1 W ∪ K M^-1 M`.
6. **Phase tube.** The case analysis is in artifact Section 3, and `phase_tube.py` checks it by machine.

Both prerequisites are ESTABLISHED.
- `post-surjective-sft-covers-admit-scheduled-sections` supplies Lemma 1, quoted verbatim.
- `cover-pair-sections-localize-to-the-symmetric-locus` supplies Theorem S and Corollary S4. These make the tube
  repair the residual step, and supply the identity (∗) used for the centralizer remark.
