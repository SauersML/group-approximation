import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.KTheoryNonUnitalZero

/-!
# Every class in `K₀(J)` is a standard-picture class

Lane `TWWSch3d3-1D`, work order `WO-3d3-1D` (six-term exactness at `K_*(J)`).
Manuscript: `non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378).

M. Rørdam, F. Larsen, N. Laustsen, *An introduction to K-theory for C⋆-algebras*,
Proposition 4.2.2: every element of `K₀(J)` has the form `[p] - [s(p)]` for a projection `p`
over `J⁺`, where `s : J⁺ → J⁺` is the scalar projection. The proofs of exactness at `K₀(J)`
(RLL Proposition 9.1.4) start from this standard picture.

* `kZero_exists_mk_sub_mk`: every element of `K₀(R)` is a difference `[x] - [y]` of classes of
  projections (RLL Proposition 3.1.7 (i), in the projection picture of `KTheory.KZero`);
* `KZeroN.map_scalarProj_eq_zero`: the scalar projection kills `K₀(J) ⊆ K₀(J⁺)`;
* `KZeroN.eq_ofCycle_of_coe_eq`: if `g = [P] - [O]` in `K₀(J⁺)` with `O` scalar, then
  `g = KZeroN.ofCycle P`;
* `KZeroN.exists_ofCycle`: **every element of `K₀(J)` is `KZeroN.ofCycle P`** (RLL 4.2.2).
-/

namespace GroupApproximation
namespace Full
namespace TWWSchafhauser

noncomputable section

section Diff

variable (R : Type*) [NonUnitalSemiring R] [StarRing R]

/-- The subgroup of `K₀(R)` of differences `[x] - [y]` of classes of projections. -/
def kZeroDiffSubgroup : AddSubgroup (KTheory.KZero R) where
  carrier := {g | ∃ x y : KTheory.Cycle R, g = KTheory.KZero.mk x - KTheory.KZero.mk y}
  add_mem' := by
    rintro _ _ ⟨x, y, rfl⟩ ⟨x', y', rfl⟩
    exact ⟨x + x', y + y', by rw [KTheory.KZero.mk_add, KTheory.KZero.mk_add, sub_add_sub_comm]⟩
  zero_mem' := ⟨0, 0, (sub_self _).symm⟩
  neg_mem' := by
    rintro _ ⟨x, y, rfl⟩
    exact ⟨y, x, neg_sub _ _⟩

variable {R}

theorem mem_kZeroDiffSubgroup {g : KTheory.KZero R} :
    g ∈ kZeroDiffSubgroup R ↔
      ∃ x y : KTheory.Cycle R, g = KTheory.KZero.mk x - KTheory.KZero.mk y :=
  Iff.rfl

/-- **Every element of `K₀(R)` is a difference of classes of projections.** -/
theorem kZero_exists_mk_sub_mk (g : KTheory.KZero R) :
    ∃ x y : KTheory.Cycle R, g = KTheory.KZero.mk x - KTheory.KZero.mk y := by
  have h : QuotientAddGroup.mk' (kZeroDiffSubgroup R) = 0 :=
    KTheory.KZero.hom_ext fun x => by
      rw [QuotientAddGroup.mk'_apply, AddMonoidHom.zero_apply, QuotientAddGroup.eq_zero_iff]
      exact mem_kZeroDiffSubgroup.mpr ⟨x, 0, by rw [KTheory.KZero.mk_zero, sub_zero]⟩
  have hg := DFunLike.congr_fun h g
  rw [QuotientAddGroup.mk'_apply, AddMonoidHom.zero_apply, QuotientAddGroup.eq_zero_iff] at hg
  exact mem_kZeroDiffSubgroup.mp hg

end Diff

section Std

variable {J : Type} [NonUnitalCStarAlgebra J]

/-- The scalar projection `s : J⁺ → J⁺` kills `K₀(J) ⊆ K₀(J⁺)`. -/
theorem KZeroN.map_scalarProj_eq_zero (g : KZeroN J) :
    KTheory.KZero.map (starRingHomOf (scalarProj J)) g.1 = 0 := by
  have h : starRingHomOf (scalarProj J) =
      (starRingHomOf (unitHom J)).comp (starRingHomOf (scalarHom J)) :=
    NonUnitalStarRingHom.ext fun _ => rfl
  rw [h, KTheory.KZero.map_comp, AddMonoidHom.comp_apply, AddMonoidHom.mem_ker.mp g.2,
    _root_.map_zero]

/-- If `g = [P] - [O]` in `K₀(J⁺)` and `O` is fixed by the scalar projection, then `g` is the
standard-picture class of `P`. -/
theorem KZeroN.eq_ofCycle_of_coe_eq {g : KZeroN J} {P O : KTheory.Cycle (Unitization ℂ J)}
    (hO : O.map (starRingHomOf (scalarProj J)) = O)
    (hg : g.1 = KTheory.KZero.mk P - KTheory.KZero.mk O) : g = KZeroN.ofCycle P := by
  have h0 := KZeroN.map_scalarProj_eq_zero g
  rw [hg, map_sub, KTheory.KZero.map_mk, KTheory.KZero.map_mk, hO, sub_eq_zero] at h0
  refine Subtype.ext ?_
  show g.1 = KTheory.KZero.mk P - KTheory.KZero.mk (P.map (starRingHomOf (scalarProj J)))
  rw [hg, h0]

/-- **The standard picture of `K₀(J)` is surjective** (RLL Proposition 4.2.2): every element
of `K₀(J)` is `[P] - [s(P)]` for a projection `P` over `J⁺`. -/
theorem KZeroN.exists_ofCycle (g : KZeroN J) :
    ∃ P : KTheory.Cycle (Unitization ℂ J), g = KZeroN.ofCycle P := by
  obtain ⟨x, ⟨m, q, hq⟩, hxy⟩ := kZero_exists_mk_sub_mk g.1
  have hO : (⟨m, 1, IsStarProjection.one _⟩ : KTheory.Cycle (Unitization ℂ J)).map
      (starRingHomOf (scalarProj J)) = ⟨m, 1, IsStarProjection.one _⟩ := by
    show (⟨m, (1 : Matrix (Fin m) (Fin m) (Unitization ℂ J)).map (starRingHomOf (scalarProj J)),
        _⟩ : KTheory.Cycle (Unitization ℂ J)) = ⟨m, 1, IsStarProjection.one _⟩
    exact KTheory.Cycle.eq_of_proj_eq (Matrix.map_one _
      (_root_.map_zero (starRingHomOf (scalarProj J)))
      (by rw [starRingHomOf_apply, _root_.map_one]))
  have h1 : KTheory.KZero.mk (⟨m, q, hq⟩ : KTheory.Cycle (Unitization ℂ J)) +
      KTheory.KZero.mk (⟨m, 1 - q, hq.one_sub⟩ : KTheory.Cycle (Unitization ℂ J)) =
        KTheory.KZero.mk (⟨m, 1, IsStarProjection.one _⟩ : KTheory.Cycle (Unitization ℂ J)) := by
    rw [← KTheory.KZero.mk_add_of_mul_eq_zero hq hq.one_sub hq.mul_one_sub_self]
    exact congrArg KTheory.KZero.mk (KTheory.Cycle.eq_of_proj_eq (add_sub_cancel q 1))
  refine ⟨x + (⟨m, 1 - q, hq.one_sub⟩ : KTheory.Cycle (Unitization ℂ J)),
    KZeroN.eq_ofCycle_of_coe_eq hO ?_⟩
  rw [hxy, KTheory.KZero.mk_add, ← h1, add_sub_add_right_eq_sub]

end Std

end

end TWWSchafhauser
end Full
end GroupApproximation
