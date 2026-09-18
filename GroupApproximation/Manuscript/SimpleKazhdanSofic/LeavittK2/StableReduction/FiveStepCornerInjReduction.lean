import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.FiveStepCornerInjRefine
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.FiveStepReduction
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.K2RankFourRefinement
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.K2Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVH2GL3.RankFive
import GroupApproximation.Meta.AxiomGuard

/-!
# Corner injectivity at rank five from a rank-four fixed-point statement (sk-leavitt-34c)

Write `L = L_{𝔽₂}(1,2)`, `σ_j = fiveStepCornerHom L j` and `D = refineHom L 0 : St_4 → St_5`.
Target: `BinaryLeavittFiveCornerInjectiveStatement` (`σ_{last 4}` is injective on `St_5(L)`).

## LOUD: no left inverse, so the target is not closed here

`σ` has **no** left-inverse homomorphism.  The generator-wise inverse `x_{rj}(a) ↦ x_{rj}(t₀ a)`,
`x_{ir}(a) ↦ x_{ir}(a s₀)` breaks the adjacent relation through `r`, since `s₀ t₀ ≠ 1`.  No other
left inverse exists either.  `σ` is not surjective on `E_5(L)`, because its `(r, j)` entries lie in
`s₀ L`.  With `K₂(5, L) = ⊥` (Khanh), a left inverse `ρ` and the relation `σ² = Ad(U) ∘ σ` would
make `σ = Ad(ρ U)` inner.  So the suggested left-inverse route is impossible.

## Proved here, unconditionally, for any ring with a Leavitt family

1. `σ_{e r} ∘ indexMap e = indexMap e ∘ σ_r` for any `e : Fin n ↪ Fin m`
   (`FiveStepCornerInjTransport`).  So a fixed-point property of `σ_p` on `K₂` moves to `σ_q`
   along the involution `indexMap (p q)` (`fiveStepCornerInj_fix_transfer`).
2. `σ_{castSucc j} ∘ D_r = D_r ∘ σ_j` for `j ≠ r` (`FiveStepCornerInjRefine`).  With
   `K₂(n+1) = D_r(K₂(n))` (`LeavittFP.K2_map_refineHom`), "σ fixes `K₂`" climbs one rank
   (`fiveStepCornerInj_fix_castSucc`).
3. `ker σ_r ≤ K₂`, so if `σ_r` fixes `K₂` pointwise then `σ_r` is injective
   (`fiveStepCornerInj_injective_of_fix`).

## The isolated gap

`FiveStepCornerInjRankFourFixStatement`: `σ_1` fixes `K₂(4, L)` pointwise, in `St_4(L)`.

* True: `K₂(4, L) = ⊥` (Khanh, arXiv:2609.08428, Thm 5.4) gives it
  (`fiveStepCornerInjRankFourFix_of_binaryLeavittSteinbergRankFourInjective`).
* Strictly weaker than the live rank-four gap `BinaryLeavittSteinbergRankFourInjectiveStatement`
  (`K₂(4, L) = ⊥`).  It is implied by that gap, and it only asks `σ_1` to act trivially on
  `K₂(4, L)`, not for `K₂(4, L)` to vanish.  It is a rank-four statement.  The rank change and
  the transposition to the index `last 4` are proved here.
* LOUD: it is **not** known to follow from the target.  It is a sufficient condition that sits
  below the rank-four gap, not a formal weakening of `BinaryLeavittFiveCornerInjectiveStatement`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup

variable {R : Type*} [Ring R] (L : LeavittFamily R) {n : ℕ}

/-- **Fixing `K₂` moves between corner indices.**  If `σ_p` fixes `K₂(m)` pointwise, so does `σ_q`:
conjugate by the involution `indexMap (p q)`, which preserves `K₂`. -/
theorem fiveStepCornerInj_fix_transfer {m : ℕ} (p q : Fin m)
    (hfix : ∀ w ∈ BooneHigman.SteinbergBasic.K2 (Fin m) R, fiveStepCornerHom L p w = w) :
    ∀ w ∈ BooneHigman.SteinbergBasic.K2 (Fin m) R, fiveStepCornerHom L q w = w := by
  intro w hw
  have hinv := fiveStepCornerInj_indexMap_swap_swap (R := R) p q
  have hu : indexMap (R := R) (Equiv.swap p q).toEmbedding w ∈
      BooneHigman.SteinbergBasic.K2 (Fin m) R :=
    (BooneHigman.SteinbergBasic.mem_K2_iff _).mpr
      (Full.LVH2GL3.projection_indexMap_eq_one _ ((BooneHigman.SteinbergBasic.mem_K2_iff w).mp hw))
  calc fiveStepCornerHom L q w
      = fiveStepCornerHom L q (indexMap (Equiv.swap p q).toEmbedding
          (indexMap (Equiv.swap p q).toEmbedding w)) := by rw [hinv w]
    _ = indexMap (Equiv.swap p q).toEmbedding
          (fiveStepCornerHom L p (indexMap (Equiv.swap p q).toEmbedding w)) :=
        fiveStepCornerInj_cornerHom_indexMap L _ p q (Equiv.swap_apply_left p q) _
    _ = indexMap (Equiv.swap p q).toEmbedding (indexMap (Equiv.swap p q).toEmbedding w) := by
        rw [hfix _ hu]
    _ = w := hinv w

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCornerInj_fix_transfer

/-- **Fixing `K₂` climbs one rank along the Leavitt refinement.**  If `σ_{j₀}` fixes `K₂(n)`
pointwise and `j₀ ≠ r`, then `σ_{castSucc j₀}` fixes `K₂(n+1) = D_r(K₂(n))` pointwise. -/
theorem fiveStepCornerInj_fix_castSucc (r j₀ : Fin n) (hj : j₀ ≠ r)
    (hfix : ∀ v ∈ BooneHigman.SteinbergBasic.K2 (Fin n) R, fiveStepCornerHom L j₀ v = v) :
    ∀ w ∈ BooneHigman.SteinbergBasic.K2 (Fin (n + 1)) R,
      fiveStepCornerHom L (Fin.castSucc j₀) w = w := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp ((LeavittFP.K2_map_refineHom L r j₀ hj).ge hw)
  rw [fiveStepCornerInj_cornerHom_refineHom L r j₀ hj v, hfix v hv]

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCornerInj_fix_castSucc

/-- **A corner endomorphism fixing `K₂` is injective**, because `ker σ_r ≤ K₂`. -/
theorem fiveStepCornerInj_injective_of_fix (r : Fin n)
    (hfix : ∀ w ∈ BooneHigman.SteinbergBasic.K2 (Fin n) R, fiveStepCornerHom L r w = w) :
    ∀ w : SteinbergGroup (Fin n) R, fiveStepCornerHom L r w = 1 → w = 1 := by
  intro w hw
  have hk : w ∈ BooneHigman.SteinbergBasic.K2 (Fin n) R :=
    (BooneHigman.SteinbergBasic.mem_K2_iff w).mpr
      (fiveStep_projection_eq_one_of_cornerHom_eq_one L r hw)
  exact (hfix w hk).symm.trans hw

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCornerInj_injective_of_fix

/-! ### The binary Leavitt algebra `L_{𝔽₂}(1,2)` -/

/-- **The isolated gap**: the corner endomorphism `σ_1` of `St_4(L)` fixes `K₂(4, L)` pointwise,
for `L = L_{𝔽₂}(1,2)`.

*Why it is true.*  `K₂(4, L) = ⊥` (Khanh, arXiv:2609.08428, Thm 5.4); see
`fiveStepCornerInjRankFourFix_of_binaryLeavittSteinbergRankFourInjective`.  Not proved in Lean.

*Why it is smaller.*  It is implied by `LeavittFP.BinaryLeavittSteinbergRankFourInjectiveStatement`
and asks less: only that `σ_1` acts trivially on `K₂(4, L)`.  The passage to rank five and to
the index `last 4` is proved (`binaryLeavittFiveCornerInjective_of_fiveStepCornerInjRankFourFix`).
LOUD: it is not known to follow from `BinaryLeavittFiveCornerInjectiveStatement`. -/
def FiveStepCornerInjRankFourFixStatement : Prop :=
  ∀ v ∈ BooneHigman.SteinbergBasic.K2 (Fin 4) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)),
    fiveStepCornerHom (BinaryLeavitt.family (ZMod 2)) (1 : Fin 4) v = v

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FiveStepCornerInjRankFourFixStatement

/-- **Corner injectivity at rank five from the rank-four fixed-point statement.**
The chain is `σ_1` fixes `K₂(4)`, then `σ_{castSucc 1}` fixes `K₂(5)` (refine `0`), then
`σ_{last 4}` fixes `K₂(5)` (transpose), and so `σ_{last 4}` is injective. -/
theorem binaryLeavittFiveCornerInjective_of_fiveStepCornerInjRankFourFix
    (h : FiveStepCornerInjRankFourFixStatement) : BinaryLeavittFiveCornerInjectiveStatement := by
  have h5 := fiveStepCornerInj_fix_castSucc (BinaryLeavitt.family (ZMod 2)) (n := 4)
    (0 : Fin 4) (1 : Fin 4) (by decide) h
  have hlast := fiveStepCornerInj_fix_transfer (BinaryLeavitt.family (ZMod 2))
    (Fin.castSucc (1 : Fin 4)) (Fin.last 4) h5
  exact fiveStepCornerInj_injective_of_fix (BinaryLeavitt.family (ZMod 2)) (Fin.last 4) hlast

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittFiveCornerInjective_of_fiveStepCornerInjRankFourFix

/-- **Truth check**: `K₂(4, L) = ⊥` gives the rank-four fixed-point statement. -/
theorem fiveStepCornerInjRankFourFix_of_binaryLeavittSteinbergRankFourInjective
    (h : LeavittFP.BinaryLeavittSteinbergRankFourInjectiveStatement) :
    FiveStepCornerInjRankFourFixStatement := by
  intro v hv
  rw [LeavittFP.BinaryLeavittSteinbergRankFourInjectiveStatement] at h
  rw [h] at hv
  rw [Subgroup.mem_bot.mp hv, map_one]

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCornerInjRankFourFix_of_binaryLeavittSteinbergRankFourInjective

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
