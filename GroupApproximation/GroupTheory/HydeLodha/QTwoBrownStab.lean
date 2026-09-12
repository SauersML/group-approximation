import Mathlib.GroupTheory.QuotientGroup.Basic
import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationDefs
import GroupApproximation.GroupTheory.HydeLodha.GammaTwoStabilizer
import GroupApproximation.GroupTheory.DoubleCosetFinitePresentation
import GroupApproximation.GroupTheory.FinitePresentationExtension
import GroupApproximation.GroupTheory.FGAbelianFinitePresentation
import GroupApproximation.Meta.AxiomGuard

/-!
# Vertex and edge stabilizers for Hyde–Lodha's Theorem 4.8

Hyde–Lodha, Theorem 4.8: "We consider the actions of `Γ, Γ_n` on `X = ℤ[1/η_n]/ℤ`, and the natural
extension of this action to that on the simplicial complex whose `k`-simplices are the `(k+1)`-element
subsets of `X`.  For each nonempty finite set `K ⊂ X`, `Γ_{K,1}` is an extension of `Γ_{K+ℤ}` by a
cyclic (trivial or infinite cyclic) group."

For `Q₂ ≤ Γ ≤ Γ₂` the finite-presentation criterion of `DoubleCosetFinitePresentation` is applied to
the vertex `0 + ℤ`:

* `classStab Γ x`: the stabilizer in `Γ` of the class `x + ℤ` (`mem_classStab_iff`);
* `vertexH Γ = classStab Γ 0`, and the edge stabilizers `edgeStab (vertexH Γ) t` are the stabilizers of
  `0 + ℤ` and `t 0 + ℤ` (`mem_edgeStab_vertexH_iff`);
* `isFinitelyPresented_of_hom_int`: an extension of a finitely presented group by a subgroup of `ℤ`
  is finitely presented;
* `isFinitelyPresented_vertexH`: `Γ_{{0},1}` is finitely presented when `Γ_{{0}}` is
  (`zeroShift : g ↦ g 0 ∈ ℤ` has kernel `stabK Γ {0}`);
* `fg_edgeStab_vertexH`: `Γ_{{0, t 0},1}` is finitely generated when `Γ_{{0, t 0}}` is finitely presented.
-/

namespace GroupApproximation
namespace HydeLodha

open HigmanThompson DoubleCosetPresentation

/-! ## Extensions by subgroups of `ℤ` -/

/-- **An extension of a finitely presented group by a subgroup of `ℤ` is finitely presented.** -/
theorem isFinitelyPresented_of_hom_int {H : Type*} [Group H] (φ : H →* Multiplicative ℤ)
    [Group.IsFinitelyPresented φ.ker] : Group.IsFinitelyPresented H := by
  haveI : Group.FG (Multiplicative ℤ) := ProductFinitePresentation.fg_of_isFinitelyPresented _
  haveI : Group.IsFinitelyPresented φ.range :=
    FGAbelianFinitePresentation.isFinitelyPresented_subgroup_of_commGroup φ.range
  haveI : Group.IsFinitelyPresented (H ⧸ φ.ker) :=
    Group.IsFinitelyPresented.equiv (QuotientGroup.quotientKerEquivRange φ).symm
  exact FinitePresentationExtension.isFinitelyPresented_of_normal φ.ker

/-! ## Stabilizers of classes mod `ℤ` -/

variable (Γ : Subgroup (Equiv.Perm ℚ))

/-- The stabilizer in `Γ` of the class `x + ℤ`. -/
def classStab (x : ℚ) : Subgroup ↥Γ where
  carrier := {g | ∀ k : ℤ, (∃ j : ℤ, (g : Equiv.Perm ℚ) (x + k) = x + j) ∧
    ∃ j : ℤ, (g : Equiv.Perm ℚ)⁻¹ (x + k) = x + j}
  one_mem' := fun k => ⟨⟨k, by simp⟩, ⟨k, by simp⟩⟩
  mul_mem' := by
    intro g h hg hh k
    obtain ⟨⟨j₁, hj₁⟩, ⟨i₁, hi₁⟩⟩ := hh k
    obtain ⟨⟨j₂, hj₂⟩, -⟩ := hg j₁
    obtain ⟨-, ⟨i₂, hi₂⟩⟩ := hg k
    obtain ⟨-, ⟨i₃, hi₃⟩⟩ := hh i₂
    refine ⟨⟨j₂, ?_⟩, ⟨i₃, ?_⟩⟩
    · show (g : Equiv.Perm ℚ) ((h : Equiv.Perm ℚ) (x + k)) = x + j₂
      rw [hj₁, hj₂]
    · show ((g : Equiv.Perm ℚ) * (h : Equiv.Perm ℚ))⁻¹ (x + k) = x + i₃
      rw [mul_inv_rev, Equiv.Perm.mul_apply, hi₂, hi₃]
  inv_mem' := by
    intro g hg k
    obtain ⟨⟨j, hj⟩, ⟨i, hi⟩⟩ := hg k
    refine ⟨⟨i, ?_⟩, ⟨j, ?_⟩⟩
    · show (g : Equiv.Perm ℚ)⁻¹ (x + k) = x + i
      exact hi
    · show ((g : Equiv.Perm ℚ)⁻¹)⁻¹ (x + k) = x + j
      rw [inv_inv]
      exact hj

variable {Γ}

theorem mem_classStab_iff (hΓ : Γ ≤ gammaTwo) {x : ℚ} {g : ↥Γ} :
    g ∈ classStab Γ x ↔ ∃ j : ℤ, (g : Equiv.Perm ℚ) x = x + j := by
  constructor
  · intro hg
    obtain ⟨⟨j, hj⟩, -⟩ := hg 0
    exact ⟨j, by simpa using hj⟩
  · rintro ⟨j, hj⟩ k
    have hgΓ := hΓ g.2
    refine ⟨⟨j + k, ?_⟩, ⟨k - j, ?_⟩⟩
    · rw [gammaTwo_add_int hgΓ, hj]
      push_cast
      ring
    · have e : x + ((k : ℤ) : ℚ) = (g : Equiv.Perm ℚ) (x + ((k - j : ℤ) : ℚ)) := by
        rw [gammaTwo_add_int hgΓ, hj]
        push_cast
        ring
      rw [e]
      exact perm_inv_apply_self _ _

variable (Γ)

/-- The stabilizer of the vertex `0 + ℤ` of `X = ℤ[1/6]/ℤ`. -/
def vertexH : Subgroup ↥Γ := classStab Γ 0

variable {Γ}

theorem mem_vertexH_iff (hΓ : Γ ≤ gammaTwo) {g : ↥Γ} :
    g ∈ vertexH Γ ↔ ∃ j : ℤ, (g : Equiv.Perm ℚ) 0 = 0 + j :=
  mem_classStab_iff hΓ

/-- The edge stabilizers of the vertex `0 + ℤ` fix the class `t 0 + ℤ`. -/
theorem mem_edgeStab_vertexH_iff (hΓ : Γ ≤ gammaTwo) (t : ↥Γ) (h : ↥(vertexH Γ)) :
    h ∈ edgeStab (vertexH Γ) t ↔
      ∃ j : ℤ, ((h : ↥Γ) : Equiv.Perm ℚ) ((t : Equiv.Perm ℚ) 0) = (t : Equiv.Perm ℚ) 0 + j := by
  rw [mem_edgeStab, mem_vertexH_iff hΓ]
  have ht := hΓ t.2
  constructor
  · rintro ⟨j, hj⟩
    have hj' : (t : Equiv.Perm ℚ)⁻¹ (((h : ↥Γ) : Equiv.Perm ℚ) ((t : Equiv.Perm ℚ) 0)) = 0 + j := hj
    refine ⟨j, ?_⟩
    have e := congrArg (t : Equiv.Perm ℚ) hj'
    rw [perm_apply_inv_self, gammaTwo_add_int ht] at e
    exact e
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    show (t : Equiv.Perm ℚ)⁻¹ (((h : ↥Γ) : Equiv.Perm ℚ) ((t : Equiv.Perm ℚ) 0)) = 0 + j
    rw [hj, ← gammaTwo_add_int ht, perm_inv_apply_self]

/-! ## The vertex stabilizer -/

variable (Γ)

/-- `g ↦ g 0 ∈ ℤ` on the vertex stabilizer. -/
noncomputable def zeroShift (hΓ : Γ ≤ gammaTwo) : ↥(vertexH Γ) →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd ⌊((g : ↥Γ) : Equiv.Perm ℚ) 0⌋
  map_one' := by simp
  map_mul' g h := by
    show Multiplicative.ofAdd ⌊(((g * h : ↥(vertexH Γ)) : ↥Γ) : Equiv.Perm ℚ) 0⌋ =
      Multiplicative.ofAdd ⌊((g : ↥Γ) : Equiv.Perm ℚ) 0⌋ *
        Multiplicative.ofAdd ⌊((h : ↥Γ) : Equiv.Perm ℚ) 0⌋
    obtain ⟨j, hj⟩ := (mem_vertexH_iff hΓ).mp h.2
    have hg := hΓ (g : ↥Γ).2
    have hadd := gammaTwo_add_int hg 0 j
    rw [zero_add] at hadd
    have e : (((g * h : ↥(vertexH Γ)) : ↥Γ) : Equiv.Perm ℚ) 0 =
        ((g : ↥Γ) : Equiv.Perm ℚ) 0 + j := by
      show ((g : ↥Γ) : Equiv.Perm ℚ) (((h : ↥Γ) : Equiv.Perm ℚ) 0) = _
      rw [hj, zero_add, hadd]
    rw [e, Int.floor_add_intCast, hj, zero_add, Int.floor_intCast, ofAdd_add]

theorem zeroShift_apply (hΓ : Γ ≤ gammaTwo) (g : ↥(vertexH Γ)) :
    zeroShift Γ hΓ g = Multiplicative.ofAdd ⌊((g : ↥Γ) : Equiv.Perm ℚ) 0⌋ := rfl

variable {Γ}

theorem apply_zero_of_mem_ker (hΓ : Γ ≤ gammaTwo) {g : ↥(vertexH Γ)}
    (hg : zeroShift Γ hΓ g = 1) : ((g : ↥Γ) : Equiv.Perm ℚ) 0 = 0 := by
  obtain ⟨j, hj⟩ := (mem_vertexH_iff hΓ).mp g.2
  rw [zeroShift_apply, ofAdd_eq_one, hj, zero_add, Int.floor_intCast] at hg
  rw [hj, hg]
  simp

variable (Γ)

/-- The kernel of `zeroShift` is `Γ_{{0}}`. -/
noncomputable def kerZeroShiftEquiv (hΓ : Γ ≤ gammaTwo) :
    ↥(stabK Γ {0}) ≃* ↥(zeroShift Γ hΓ).ker where
  toFun f := ⟨⟨⟨f, (mem_stabK.mp f.2).1⟩, (mem_vertexH_iff hΓ).mpr ⟨0, by
      show (f : Equiv.Perm ℚ) 0 = 0 + ((0 : ℤ) : ℚ)
      rw [(mem_stabK.mp f.2).2 0 rfl]
      simp⟩⟩, by
      rw [MonoidHom.mem_ker, zeroShift_apply]
      show Multiplicative.ofAdd ⌊(f : Equiv.Perm ℚ) 0⌋ = 1
      rw [(mem_stabK.mp f.2).2 0 rfl]
      simp⟩
  invFun g := ⟨((g : ↥(vertexH Γ)) : ↥Γ), mem_stabK.mpr ⟨((g : ↥(vertexH Γ)) : ↥Γ).2,
    fun k hk => by
      rw [Set.mem_singleton_iff] at hk
      rw [hk]
      exact apply_zero_of_mem_ker hΓ (MonoidHom.mem_ker.mp g.2)⟩⟩
  left_inv f := rfl
  right_inv g := rfl
  map_mul' f g := rfl

/-- **`Γ_{{0},1}` is finitely presented when `Γ_{{0}}` is.** -/
theorem isFinitelyPresented_vertexH (hΓ : Γ ≤ gammaTwo)
    [Group.IsFinitelyPresented ↥(stabK Γ {0})] : Group.IsFinitelyPresented ↥(vertexH Γ) := by
  haveI : Group.IsFinitelyPresented ↥(zeroShift Γ hΓ).ker :=
    Group.IsFinitelyPresented.equiv (kerZeroShiftEquiv Γ hΓ)
  exact isFinitelyPresented_of_hom_int (zeroShift Γ hΓ)

/-! ## Edge stabilizers -/

/-- `zeroShift` on an edge stabilizer. -/
noncomputable def edgeShift (hΓ : Γ ≤ gammaTwo) (t : ↥Γ) :
    ↥(edgeStab (vertexH Γ) t) →* Multiplicative ℤ :=
  (zeroShift Γ hΓ).comp (edgeStab (vertexH Γ) t).subtype

/-- The kernel of `edgeShift` is `Γ_{{0, t 0}}`. -/
noncomputable def kerEdgeShiftEquiv (hΓ : Γ ≤ gammaTwo) (t : ↥Γ) :
    ↥(stabK Γ {0, (t : Equiv.Perm ℚ) 0}) ≃* ↥(edgeShift Γ hΓ t).ker where
  toFun f := ⟨⟨⟨⟨f, (mem_stabK.mp f.2).1⟩, (mem_vertexH_iff hΓ).mpr ⟨0, by
      show (f : Equiv.Perm ℚ) 0 = 0 + ((0 : ℤ) : ℚ)
      rw [(mem_stabK.mp f.2).2 0 (Set.mem_insert _ _)]
      simp⟩⟩, (mem_edgeStab_vertexH_iff hΓ t _).mpr ⟨0, by
      show (f : Equiv.Perm ℚ) ((t : Equiv.Perm ℚ) 0) = (t : Equiv.Perm ℚ) 0 + ((0 : ℤ) : ℚ)
      rw [(mem_stabK.mp f.2).2 _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))]
      simp⟩⟩, by
      rw [MonoidHom.mem_ker]
      show Multiplicative.ofAdd ⌊(f : Equiv.Perm ℚ) 0⌋ = 1
      rw [(mem_stabK.mp f.2).2 0 (Set.mem_insert _ _)]
      simp⟩
  invFun g := ⟨(((g : ↥(edgeStab (vertexH Γ) t)) : ↥(vertexH Γ)) : ↥Γ),
    mem_stabK.mpr ⟨(((g : ↥(edgeStab (vertexH Γ) t)) : ↥(vertexH Γ)) : ↥Γ).2, fun k hk => by
      have h0 : (((g : ↥(edgeStab (vertexH Γ) t)) : ↥(vertexH Γ)) : Equiv.Perm ℚ) 0 = 0 :=
        apply_zero_of_mem_ker hΓ (MonoidHom.mem_ker.mp g.2)
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
      rcases hk with rfl | rfl
      · exact h0
      · obtain ⟨j, hj⟩ := (mem_edgeStab_vertexH_iff hΓ t _).mp
          (g : ↥(edgeStab (vertexH Γ) t)).2
        have hfl := floor_apply_of_fix_zero
          (hΓ (((g : ↥(edgeStab (vertexH Γ) t)) : ↥(vertexH Γ)) : ↥Γ).2) h0
          ((t : Equiv.Perm ℚ) 0)
        rw [hj, Int.floor_add_intCast] at hfl
        have hj0 : j = 0 := by omega
        rw [hj, hj0]
        simp⟩⟩
  left_inv f := rfl
  right_inv g := rfl
  map_mul' f g := rfl

/-- **`Γ_{{0, t 0},1}` is finitely generated when `Γ_{{0, t 0}}` is finitely presented.** -/
theorem fg_edgeStab_vertexH (hΓ : Γ ≤ gammaTwo) (t : ↥Γ)
    [Group.IsFinitelyPresented ↥(stabK Γ {0, (t : Equiv.Perm ℚ) 0})] :
    Group.FG ↥(edgeStab (vertexH Γ) t) := by
  haveI : Group.IsFinitelyPresented ↥(edgeShift Γ hΓ t).ker :=
    Group.IsFinitelyPresented.equiv (kerEdgeShiftEquiv Γ hΓ t)
  haveI := isFinitelyPresented_of_hom_int (edgeShift Γ hΓ t)
  exact ProductFinitePresentation.fg_of_isFinitelyPresented _

#audit_axioms GroupApproximation.HydeLodha.isFinitelyPresented_of_hom_int
#audit_axioms GroupApproximation.HydeLodha.isFinitelyPresented_vertexH
#audit_axioms GroupApproximation.HydeLodha.fg_edgeStab_vertexH

end HydeLodha
end GroupApproximation
