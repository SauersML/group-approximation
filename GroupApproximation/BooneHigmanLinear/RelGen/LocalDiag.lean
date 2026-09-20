import GroupApproximation.BooneHigmanLinear.RelGen.TorusInduct
import GroupApproximation.BooneHigmanLinear.RelGen.SteinCell2
import GroupApproximation.Meta.AxiomGuard

/-!
# Diagonal and `L`-scalar elements of `St_I(R)`

Lane bh-pal-wire, k2-poly H.L1 (ii). Over a commutative ring:

* `diagGroup I R`: the elements acting on `R^I` by a diagonal of units. It contains `H̄(R, J)`
  (`hBar_le_diagGroup`).
* `lscalGroup I R L`: the elements `g` with `g e_L = l e_L` and `(g w)_L = r w_L` for units `l, r`.
  It contains `diagGroup` and the roots off `L`, hence `qGroup J K` for `L ∉ K`
  (`qGroup_le_lscal`).
* `rootGroup_le_rootSpan`: a root group over an ideal lies in the root span of its roots.
-/

namespace GroupApproximation.BooneHigmanLinear.RelGen

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (h)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan act unitVec
  unitVec_apply act_mul act_one act_x_apply x_mem_rootSpan)

variable (I : Type*) [Fintype I] [DecidableEq I] (R : Type*) [CommRing R]

/-- The elements acting on `R^I` by a diagonal of units. -/
def diagGroup : Subgroup (SteinbergGroup I R) where
  carrier := {g | ∃ d : I → Rˣ, ∀ (w : I → R) (k : I), act g w k = (d k : R) * w k}
  one_mem' := ⟨fun _ => 1, fun w k => by
    show act 1 w k = ((1 : Rˣ) : R) * w k
    rw [act_one, Units.val_one, one_mul]⟩
  mul_mem' := by
    rintro a b ⟨d, hd⟩ ⟨e, he⟩
    refine ⟨fun k => d k * e k, fun w k => ?_⟩
    show act (a * b) w k = ((d k * e k : Rˣ) : R) * w k
    rw [act_mul, hd, he, Units.val_mul, mul_assoc]
  inv_mem' := by
    rintro a ⟨d, hd⟩
    refine ⟨fun k => (d k)⁻¹, fun w k => ?_⟩
    show act a⁻¹ w k = (((d k)⁻¹ : Rˣ) : R) * w k
    have e : w k = (d k : R) * act a⁻¹ w k := by
      rw [← hd, ← act_mul, mul_inv_cancel, act_one]
    rw [e, ← mul_assoc, Units.inv_mul, one_mul]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.diagGroup

/-- The elements scaling `e_L` and the row `L` by units. -/
def lscalGroup (L : I) : Subgroup (SteinbergGroup I R) where
  carrier := {g | (∃ l : Rˣ, act g (unitVec L) = (l : R) • unitVec L) ∧
    ∃ r : Rˣ, ∀ w : I → R, act g w L = (r : R) * w L}
  one_mem' := ⟨⟨1, by rw [act_one, Units.val_one, one_smul]⟩,
    ⟨1, fun w => by rw [act_one, Units.val_one, one_mul]⟩⟩
  mul_mem' := by
    rintro a b ⟨⟨la, hla⟩, ⟨ra, hra⟩⟩ ⟨⟨lb, hlb⟩, ⟨rb, hrb⟩⟩
    refine ⟨⟨lb * la, ?_⟩, ⟨ra * rb, fun w => ?_⟩⟩
    · rw [act_mul, hlb, act_smul', hla, smul_smul, Units.val_mul]
    · rw [act_mul, hra, hrb, Units.val_mul, mul_assoc]
  inv_mem' := by
    rintro a ⟨⟨l, hl⟩, ⟨r, hr⟩⟩
    refine ⟨⟨l⁻¹, ?_⟩, ⟨r⁻¹, fun w => ?_⟩⟩
    · have e : act a⁻¹ (unitVec L) = ((l⁻¹ : Rˣ) : R) • act a⁻¹ ((l : R) • unitVec L) := by
        rw [act_smul', smul_smul, Units.inv_mul, one_smul]
      rw [e, ← hl, ← act_mul, inv_mul_cancel, act_one]
    · have e : w L = (r : R) * act a⁻¹ w L := by
        rw [← hr, ← act_mul, mul_inv_cancel, act_one]
      rw [e, ← mul_assoc, Units.inv_mul, one_mul]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.lscalGroup

variable {I R}

theorem h_mem_diagGroup (i j : I) (hij : i ≠ j) (u : Rˣ) : h i j hij u ∈ diagGroup I R := by
  refine ⟨fun k => if k = i then u else if k = j then u⁻¹ else 1, fun w k => ?_⟩
  show act (h i j hij u) w k = ((if k = i then u else if k = j then u⁻¹ else 1 : Rˣ) : R) * w k
  rw [act_h_apply]
  by_cases hi : k = i
  · rw [if_pos hi, if_pos hi]
  · by_cases hj : k = j
    · rw [if_neg hi, if_neg hi, if_pos hj, if_pos hj]
    · rw [if_neg hi, if_neg hi, if_neg hj, if_neg hj, Units.val_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.h_mem_diagGroup

theorem mem_diagGroup_of_mem_symGroup {z : SteinbergGroup I R} (hz : z ∈ symGroup I R) :
    z ∈ diagGroup I R :=
  ⟨fun _ => 1, fun w k => by
    show act z w k = ((1 : Rˣ) : R) * w k
    rw [act_of_mem_symGroup hz, Units.val_one, one_mul]⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.mem_diagGroup_of_mem_symGroup

theorem hBar_le_diagGroup (J : Ideal R) : hBar I J ≤ diagGroup I R := by
  refine (Subgroup.closure_le _).mpr (Set.union_subset ?_ ?_)
  · rintro _ ⟨i, j, hij, u, -, rfl⟩
    exact h_mem_diagGroup i j hij u
  · rintro _ ⟨i, j, hij, u, v, -, rfl⟩
    exact mem_diagGroup_of_mem_symGroup (csym_mem_symGroup hij u v)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.hBar_le_diagGroup

theorem diag_act_unitVec {g : SteinbergGroup I R} {d : I → Rˣ}
    (hd : ∀ (w : I → R) (k : I), act g w k = (d k : R) * w k) (L : I) :
    act g (unitVec L) = ((d L : Rˣ) : R) • unitVec (R := R) L := by
  funext k
  rw [hd, Pi.smul_apply, smul_eq_mul, unitVec_apply]
  by_cases hk : k = L
  · rw [hk]
  · rw [if_neg hk, mul_zero, mul_zero]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.diag_act_unitVec

theorem diag_le_lscal (L : I) : diagGroup I R ≤ lscalGroup I R L := by
  rintro g ⟨d, hd⟩
  exact ⟨⟨d L, diag_act_unitVec hd L⟩, ⟨d L, fun w => hd w L⟩⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.diag_le_lscal

theorem x_mem_lscalGroup {i j L : I} (hij : i ≠ j) (hiL : i ≠ L) (hjL : j ≠ L) (s : R) :
    x i j hij s ∈ lscalGroup I R L := by
  refine ⟨⟨1, ?_⟩, ⟨1, fun w => ?_⟩⟩
  · funext k
    rw [act_x_apply, unitVec_apply L j, if_neg hjL, mul_zero, ite_self, add_zero, Units.val_one,
      one_smul]
  · rw [act_x_apply, if_neg (Ne.symm hiL), add_zero, Units.val_one, one_mul]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.x_mem_lscalGroup

theorem qGroup_le_lscal {J : Ideal R} {K : Finset I} {L : I} (hLK : L ∉ K) :
    qGroup J K ≤ lscalGroup I R L := by
  refine sup_le ((Subgroup.closure_le _).mpr ?_) ((hBar_le_diagGroup J).trans (diag_le_lscal L))
  rintro _ ⟨i, j, hij, s, ⟨hi, hj⟩, -, rfl⟩
  exact x_mem_lscalGroup hij (fun e => hLK (by rw [← e]; exact hi))
    (fun e => hLK (by rw [← e]; exact hj)) s

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.qGroup_le_lscal

theorem rootGroup_le_rootSpan {J : Ideal R} {P Q : I → I → Prop} (hPQ : ∀ i j, P i j → Q i j) :
    rootGroup I J P ≤ rootSpan (R := R) Q := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨i, j, hij, s, hP, -, rfl⟩
  exact x_mem_rootSpan hij s (hPQ i j hP)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.rootGroup_le_rootSpan

end GroupApproximation.BooneHigmanLinear.RelGen
