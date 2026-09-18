import GroupApproximation.BooneHigman.Metabelian.ElemFPNK2SliceLevel
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyFieldConst
import GroupApproximation.Meta.AxiomGuard

/-!
# The field building block at slice level `0`

Lane `bh-met-90u`, wiring module.  At level `n = 0`, the slice residual `nk2Slice_LevelStatement
(ZMod p) 0` concerns cube elements of `K₂(5, F_p[s_0])`.  One cube variable is the polynomial
ring in one variable.  So death at level `0` follows from `K₂(5, F_p[X]) = 0`, and by
`k2PolyField_K2_eq_bot_of_const` that follows from the residual `k2PolyField_ConstStatement
(ZMod p) 5` (module `ElemFPK2PolyFieldConst`).

* `k2PolyField_dies_zero_of_const`: residual at rank `5` ⟹ `nk2Slice_DiesStatement (ZMod p) 0`.
  In fact every element of `K₂(5, F_p[s_0])` is trivial, not only the cube elements.
* `k2PolyField_level_zero_of_const`: residual at rank `5` ⟹ `nk2Slice_LevelStatement (ZMod p) 0`
  (with `nk2Slice_level_of_dies`).

**LOUD strength note.** This does **not** reach `nk2Slice_CofinalStatement`, nor the full slice
residual `nk2Core_SliceStatement`.
* The cofinal statement asks, for every `n₀`, for some level `n ≥ n₀`.
* The descent `nk2Slice_dies_of_dies_succ` runs downward (level `n + 1` gives level `n`), so
  level `0` does not propagate upward.
* The higher levels involve `K₂` over `F_p[s_0..s_n]` with `n ≥ 1`, which is outside the
  one-variable field building block.

The level-`0` statement proved here from the residual is therefore strictly weaker than the
cofinal statement's `F_p` half, and it is true.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigman.Metabelian.ElemFP

/-- **Level `0` death from the field building block.**  If `K₂(5, F_p[X])` lies in the image of
`St(5, F_p)` (the residual), then every cube element of `K₂(5, F_p[s_0])` dies after padding.
Indeed, it is already trivial. -/
theorem k2PolyField_dies_zero_of_const
    (h : ∀ p : ℕ, p.Prime → k2PolyField_ConstStatement (ZMod p) 5) :
    ∀ p : ℕ, p.Prime → nk2Slice_DiesStatement (ZMod p) 0 := by
  intro p hp N hN v _
  have hN5 : N = 5 := by omega
  subst hN5
  haveI : Unique (Fin (0 + 1)) := Fin.instUnique
  have hv : v = 1 := k2PolyField_eq_one_of_unique hp le_rfl (h p hp) v
  refine ⟨5, le_rfl, ?_⟩
  rw [hv, map_one]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.k2PolyField_dies_zero_of_const

/-- **Level `0` of the slice residual over `F_p`, from the field building block.** -/
theorem k2PolyField_level_zero_of_const
    (h : ∀ p : ℕ, p.Prime → k2PolyField_ConstStatement (ZMod p) 5) :
    ∀ p : ℕ, p.Prime → nk2Slice_LevelStatement (ZMod p) 0 := fun p hp ↦
  nk2Slice_level_of_dies (ZMod p) (k2PolyField_dies_zero_of_const h p hp)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.k2PolyField_level_zero_of_const

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
