import GroupApproximation.BooneHigmanLinear.CharZero.BTri.StepLocal
import GroupApproximation.BooneHigmanLinear.CharZero.BTri.Lifting
import GroupApproximation.Meta.AxiomGuard

/-!
# The twisted one-prime step (Z1-base, piece Z.6, part 3)

Let `A` be a commutative ring, `p ∈ A`, `B = A[1/p]`, and let `SL₃(B)` act on the building. Assume:
* `hA`, the action is a triangle action (piece Z.3);
* `hconn` and `hsc`, the building is connected and simply connected (piece Z.4);
* `hstab0`, `hSL` and `hinj`, as in `BTri/StepLocal.lean`;
* `hfg`, the three edge groups `Pᵢ ∩ Pⱼ` are finitely generated.

Then (`twisted_step`) `K₂(3, B)` lies in the normal closure of a set made of two parts:
* the three twists `δᵢ(ι(K₂(3, A)))`;
* finitely many elements of `K₂(3, B)`, the discrepancies of the local lifts on generators of
  the edge groups.

Proof. The local homomorphisms `localHom N i` agree on the edge groups: they agree on
generators, by the choice of `N`. The colimit theorem (`exists_extension`) extends them to
`ψ : SL₃(B) →* St₃(B)/N`.
Then `ψ ∘ π` and the quotient map agree on the generators `δᵢ(ι(St₃(A)))` of `St₃(B)`
(`twist_closure_eq_top`), so they are equal, and they kill `K₂(3, B)`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace BTri

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigman.Metabelian

section Main

variable {A : Type*} [CommRing A] {p : A}
  (hinj : Function.Injective (algebraMap A (Localization.Away p)))
  (hstab0 : ∀ γ : SL3 (Localization.Away p), γ • stdVertex A p 0 = stdVertex A p 0 ↔
    ∀ k l, (γ : Matrix (Fin 3) (Fin 3) (Localization.Away p)) k l ∈
      Set.range (algebraMap A (Localization.Away p)))
  (hSL : Absorption.SpecialLinearInElementary A 3)

theorem slConj_injective (D : Matrix.GeneralLinearGroup (Fin 3) (Localization.Away p)) :
    Function.Injective (slConj D) := by
  intro γ δ h
  have h' := congrArg (fun g : SL3 (Localization.Away p) =>
    Matrix.SpecialLinearGroup.toGL g) h
  simp only [toGL_slConj, mul_left_inj, mul_right_inj] at h'
  exact Matrix.SpecialLinearGroup.toGL_injective h'

#audit_axioms slConj_injective

include hstab0 in
/-- The lift projects to the original element. -/
theorem elemToSL_projection_liftI (i : Fin 3) (γ : vstab (A := A) (p := p) i) :
    elemToSL (projection (liftI hinj hstab0 hSL i γ)) = γ := by
  apply slConj_injective (stdMat A p i)
  apply Subtype.ext
  set w := (projection_surjective (slToE hSL (toA hinj hstab0 (toStab0 i γ)))).choose with hw
  have hpw : projection w = slToE hSL (toA hinj hstab0 (toStab0 i γ)) :=
    (projection_surjective (slToE hSL (toA hinj hstab0 (toStab0 i γ)))).choose_spec
  change ((slConj (stdMat A p i) (elemToSL (projection
      (twist A p i (ringMap (algebraMap A (Localization.Away p)) w)))) : SL3 _) :
    Matrix (Fin 3) (Fin 3) (Localization.Away p)) = _
  rw [slConj_twist, hpw, ← coe_toStab0, ← map_toA hinj hstab0 (toStab0 i γ)]
  rfl

#audit_axioms elemToSL_projection_liftI

theorem elemToSL_injective {R : Type*} [CommRing R] :
    Function.Injective (elemToSL (R := R)) := by
  intro e f h
  exact Subtype.ext (Units.ext (congrArg Subtype.val h))

#audit_axioms elemToSL_injective

/-- The discrepancy of the two local lifts of an element of `Pᵢ ∩ Pⱼ`. -/
noncomputable def disc (i j : Fin 3)
    (γ : (vstab (A := A) (p := p) i ⊓ vstab (A := A) (p := p) j : Subgroup _)) :
    SteinbergGroup (Fin 3) (Localization.Away p) :=
  (liftI hinj hstab0 hSL i ⟨γ, (Subgroup.mem_inf.mp γ.2).1⟩)⁻¹ *
    liftI hinj hstab0 hSL j ⟨γ, (Subgroup.mem_inf.mp γ.2).2⟩

theorem disc_mem_K2 (i j : Fin 3)
    (γ : (vstab (A := A) (p := p) i ⊓ vstab (A := A) (p := p) j : Subgroup _)) :
    disc hinj hstab0 hSL i j γ ∈ K2 (Fin 3) (Localization.Away p) := by
  rw [mem_K2_iff, disc, map_mul, map_inv, inv_mul_eq_one]
  apply elemToSL_injective
  rw [elemToSL_projection_liftI, elemToSL_projection_liftI]

#audit_axioms disc_mem_K2

variable (N : Subgroup (SteinbergGroup (Fin 3) (Localization.Away p))) [N.Normal]
  (hN : ∀ i : Fin 3, ∀ k ∈ K2 (Fin 3) A,
    twist A p i (ringMap (algebraMap A (Localization.Away p)) k) ∈ N)

/-- **The local homomorphisms are compatible** once `N` contains the discrepancies of a
generating set of each edge group. -/
theorem localHom_compat
    (T : ∀ i j : Fin 3, Set (vstab (A := A) (p := p) i ⊓ vstab (A := A) (p := p) j : Subgroup _))
    (hT : ∀ i j, Subgroup.closure (T i j) = ⊤)
    (hdisc : ∀ i j, ∀ γ ∈ T i j, disc hinj hstab0 hSL i j γ ∈ N)
    (i j : Fin 3) (a : vstab (A := A) (p := p) i) (b : vstab (A := A) (p := p) j)
    (hab : (a : SL3 (Localization.Away p)) = b) :
    localHom hinj hstab0 hSL N hN i a = localHom hinj hstab0 hSL N hN j b := by
  have heq : (localHom hinj hstab0 hSL N hN i).comp (Subgroup.inclusion inf_le_left) =
      (localHom hinj hstab0 hSL N hN j).comp (Subgroup.inclusion inf_le_right) := by
    refine MonoidHom.eq_of_eqOn_dense (hT i j) fun γ hγ => ?_
    change localHom hinj hstab0 hSL N hN i ⟨γ, (Subgroup.mem_inf.mp γ.2).1⟩ =
      localHom hinj hstab0 hSL N hN j ⟨γ, (Subgroup.mem_inf.mp γ.2).2⟩
    rw [localHom_eq_mk_liftI, localHom_eq_mk_liftI, QuotientGroup.eq]
    exact hdisc i j γ hγ
  have hb : (a : SL3 (Localization.Away p)) ∈ vstab (A := A) (p := p) j := hab ▸ b.2
  have h := DFunLike.congr_fun heq ⟨a, Subgroup.mem_inf.mpr ⟨a.2, hb⟩⟩
  change localHom hinj hstab0 hSL N hN i a =
    localHom hinj hstab0 hSL N hN j ⟨a, hb⟩ at h
  rw [h]
  congr 1
  exact Subtype.ext hab

#audit_axioms localHom_compat

variable {τ : Vertex A (Localization.Away p) p → Fin 3}
  (hA : TriangleAction (SL3 (Localization.Away p)) (buildingGraph A (Localization.Away p) p)
    (stdVertex A p) τ)
  (hconn : (buildingGraph A (Localization.Away p) p).Connected)
  (hsc : TriSimplyConnected (buildingGraph A (Localization.Away p) p) (stdVertex A p 0))

include hA hconn hsc in
/-- **`K₂(3, B)` dies modulo `N`** once the local homomorphisms are compatible. -/
theorem K2_le_of_compat
    (hcompat : ∀ (i j : Fin 3) (a : vstab (A := A) (p := p) i) (b : vstab (A := A) (p := p) j),
      (a : SL3 (Localization.Away p)) = b →
        localHom hinj hstab0 hSL N hN i a = localHom hinj hstab0 hSL N hN j b) :
    K2 (Fin 3) (Localization.Away p) ≤ N := by
  obtain ⟨ψ, hψ⟩ := exists_extension hA hconn hsc (localHom hinj hstab0 hSL N hN) hcompat
  have hgen : ∀ (i : Fin 3) (u : SteinbergGroup (Fin 3) A),
      ψ (elemToSL (projection (twist A p i (ringMap (algebraMap A (Localization.Away p)) u)))) =
        (twist A p i (ringMap (algebraMap A (Localization.Away p)) u) :
          SteinbergGroup (Fin 3) (Localization.Away p) ⧸ N) := by
    intro i u
    have h := hψ i ⟨_, twist_proj_mem hstab0 i u⟩
    rw [localHom_twist] at h
    exact h
  have hall : ψ.comp (elemToSL.comp projection) = QuotientGroup.mk' N := by
    apply MonoidHom.ext
    intro u
    have hu : u ∈ twistSpan A p := by rw [twist_closure_eq_top]; exact Subgroup.mem_top u
    have hle : twistSpan A p ≤ MonoidHom.eqLocus (ψ.comp (elemToSL.comp projection))
        (QuotientGroup.mk' N) := by
      rw [twistSpan, Subgroup.closure_le]
      intro v hv
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
      obtain ⟨_, ⟨u, rfl⟩, rfl⟩ := hi
      exact hgen i u
    exact hle hu
  intro u hu
  have h1 : QuotientGroup.mk' N u = 1 := by
    rw [← hall, MonoidHom.comp_apply, MonoidHom.comp_apply, (mem_K2_iff u).mp hu, map_one,
      map_one]
  exact (QuotientGroup.eq_one_iff u).mp h1

#audit_axioms K2_le_of_compat

end Main

/-- The twisted images of `K₂(3, A)` in `St₃(A[1/p])`. -/
noncomputable def twistedK2 (A : Type*) [CommRing A] (p : A) :
    Set (SteinbergGroup (Fin 3) (Localization.Away p)) :=
  ⋃ i : Fin 3, twist A p i '' (ringMap (algebraMap A (Localization.Away p)) ''
    (K2 (Fin 3) A : Set (SteinbergGroup (Fin 3) A)))

section Step

variable {A : Type*} [CommRing A] {p : A}
  (hinj : Function.Injective (algebraMap A (Localization.Away p)))
  (hstab0 : ∀ γ : SL3 (Localization.Away p), γ • stdVertex A p 0 = stdVertex A p 0 ↔
    ∀ k l, (γ : Matrix (Fin 3) (Fin 3) (Localization.Away p)) k l ∈
      Set.range (algebraMap A (Localization.Away p)))
  (hSL : Absorption.SpecialLinearInElementary A 3)
  {τ : Vertex A (Localization.Away p) p → Fin 3}
  (hA : TriangleAction (SL3 (Localization.Away p)) (buildingGraph A (Localization.Away p) p)
    (stdVertex A p) τ)
  (hconn : (buildingGraph A (Localization.Away p) p).Connected)
  (hsc : TriSimplyConnected (buildingGraph A (Localization.Away p) p) (stdVertex A p 0))

include hinj hstab0 hSL hA hconn hsc in
/-- **The twisted one-prime step.** -/
theorem twisted_step
    (hfg : ∀ i j : Fin 3,
      Group.FG (vstab (A := A) (p := p) i ⊓ vstab (A := A) (p := p) j : Subgroup _)) :
    ∃ s : Set (SteinbergGroup (Fin 3) (Localization.Away p)), s.Finite ∧
      s ⊆ K2 (Fin 3) (Localization.Away p) ∧
      K2 (Fin 3) (Localization.Away p) ≤ Subgroup.normalClosure (twistedK2 A p ∪ s) := by
  choose T hT using fun i j => (hfg i j).out
  let s : Set (SteinbergGroup (Fin 3) (Localization.Away p)) :=
    ⋃ i : Fin 3, ⋃ j : Fin 3, disc hinj hstab0 hSL i j '' (T i j : Set _)
  refine ⟨s, ?_, ?_, ?_⟩
  · exact Set.finite_iUnion fun i => Set.finite_iUnion fun j => (T i j).finite_toSet.image _
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hi
    obtain ⟨γ, -, rfl⟩ := hj
    exact disc_mem_K2 hinj hstab0 hSL i j γ
  · have hN : ∀ i : Fin 3, ∀ k ∈ K2 (Fin 3) A,
        twist A p i (ringMap (algebraMap A (Localization.Away p)) k) ∈
          Subgroup.normalClosure (twistedK2 A p ∪ s) := fun i k hk =>
      Subgroup.subset_normalClosure
        (Or.inl (Set.mem_iUnion.mpr ⟨i, _, ⟨k, hk, rfl⟩, rfl⟩))
    refine K2_le_of_compat hinj hstab0 hSL _ hN hA hconn hsc ?_
    exact localHom_compat hinj hstab0 hSL _ hN (fun i j => (T i j : Set _)) hT
      fun i j γ hγ => Subgroup.subset_normalClosure
        (Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, γ, hγ, rfl⟩⟩))

#audit_axioms twisted_step

end Step

end BTri
end BooneHigmanLinear
end GroupApproximation
