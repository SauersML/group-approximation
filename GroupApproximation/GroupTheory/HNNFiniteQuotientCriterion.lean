import GroupApproximation.GroupTheory.FiniteHNNResiduallyFinite
import GroupApproximation.Algebra.HNNSubextension

/-!
# A finite-quotient criterion for residual finiteness of HNN extensions

For residual finiteness it is enough that every finite Britton-reduced
spelling admit one finite quotient of the base in which

* the two edge images are still isomorphic compatibly with the original edge
  map, and
* that particular spelling remains Britton reduced.

The resulting word survives in an HNN extension of a finite group, and those
finite-base HNN extensions are residually finite.  This formulation isolates
the exact finite synchronization datum needed by the final rope edge.
-/

namespace GroupApproximation
namespace HNNFiniteQuotientCriterion

noncomputable section

universe u

variable {G : Type u} [Group G] {A B : Subgroup G} (φ : A ≃* B)

/-- Compatibility of a quotient edge equivalence with the original edge
equivalence. -/
def IntertwinesQuotient {Q : Type} [Group Q] (q : G →* Q)
    (φq : A.map q ≃* B.map q) : Prop :=
  ∀ a : A,
    ((φq ⟨q (a : G), ⟨a, a.2, rfl⟩⟩ : B.map q) : Q) =
      q ((φ a : B) : G)

/-- The exact wordwise finite-quotient synchronization hypothesis. -/
def HasCompatibleFiniteQuotients : Prop :=
  ∀ (g : G) (l : List (ℤˣ × G)), HNNBritton.NoPinch A B l →
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (q : G →* Q)
      (φq : A.map q ≃* B.map q),
      (g ≠ 1 → q g ≠ 1) ∧ IntertwinesQuotient φ q φq ∧
        HNNBritton.NoPinch (A.map q) (B.map q)
          (HNNSubextension.mapList q l)

/-- Map an HNN extension to a compatible HNN extension of a quotient base. -/
def mapHNN {Q : Type} [Group Q] (q : G →* Q)
    (φq : A.map q ≃* B.map q) (hcompat : IntertwinesQuotient φ q φq) :
    HNNExtension G A B φ →* HNNExtension Q (A.map q) (B.map q) φq :=
  HNNExtension.lift
    ((HNNExtension.of : Q →* HNNExtension Q (A.map q) (B.map q) φq).comp q)
    HNNExtension.t (by
      intro a
      let aq : A.map q := ⟨q (a : G), ⟨a, a.2, rfl⟩⟩
      have hconj := HNNExtension.equiv_eq_conj (φ := φq) aq
      have hgoal :
          HNNExtension.of (q ((φ a : B) : G)) =
            (HNNExtension.t : HNNExtension Q (A.map q) (B.map q) φq) *
              HNNExtension.of (q (a : G)) * HNNExtension.t⁻¹ := by
        rw [← hcompat a]
        exact hconj
      exact mul_inv_eq_iff_eq_mul.mp hgoal.symm)

@[simp] theorem mapHNN_of {Q : Type} [Group Q] (q : G →* Q)
    (φq : A.map q ≃* B.map q) (hcompat : IntertwinesQuotient φ q φq)
    (g : G) :
    mapHNN φ q φq hcompat (HNNExtension.of g) = HNNExtension.of (q g) := by
  simp [mapHNN, HNNExtension.lift_of]

@[simp] theorem mapHNN_t {Q : Type} [Group Q] (q : G →* Q)
    (φq : A.map q ≃* B.map q) (hcompat : IntertwinesQuotient φ q φq) :
    mapHNN φ q φq hcompat (HNNExtension.t : HNNExtension G A B φ) =
      (HNNExtension.t : HNNExtension Q (A.map q) (B.map q) φq) := by
  simp [mapHNN, HNNExtension.lift_t]

theorem mapHNN_wordProd {Q : Type} [Group Q] (q : G →* Q)
    (φq : A.map q ≃* B.map q) (hcompat : IntertwinesQuotient φ q φq)
    (g : G) (l : List (ℤˣ × G)) :
    mapHNN φ q φq hcompat (HNNBritton.wordProd φ g l) =
      HNNBritton.wordProd φq (q g) (HNNSubextension.mapList q l) := by
  apply HNNSubextension.map_wordProd
  exact
    { map_of := mapHNN_of φ q φq hcompat
      map_t := mapHNN_t φ q φq hcompat }

/-- The finite-compatible-quotient criterion for HNN residual finiteness. -/
theorem residuallyFinite (hsync : HasCompatibleFiniteQuotients φ) :
    Group.ResiduallyFinite (HNNExtension G A B φ) := by
  classical
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro z hz
  obtain ⟨g, l, hred, hword⟩ := HNNBritton.exists_hasSpelling φ z
  obtain ⟨Q, hQgroup, hQfinite, q, φq, hqg, hcompat, hmapred⟩ :=
    hsync g l hred
  letI : Group Q := hQgroup
  letI : Finite Q := hQfinite
  letI : Fintype Q := Fintype.ofFinite Q
  let E := HNNExtension Q (A.map q) (B.map q) φq
  let Ψ : HNNExtension G A B φ →* E := mapHNN φ q φq hcompat
  have hΨz : Ψ z ≠ 1 := by
    rw [← hword]
    rw [mapHNN_wordProd]
    by_cases hnil : l = []
    · subst l
      rw [HNNSubextension.mapList_nil, HNNBritton.wordProd_nil]
      apply HNNExtension.of_injective.ne
      apply hqg
      intro hg
      subst g
      apply hz
      simpa using hword.symm
    · exact HNNBritton.wordProd_ne_one φq
        (HNNSubextension.mapList_ne_nil q hnil) hmapred
  letI : Group.ResiduallyFinite E :=
    FiniteHNNFreeLabelAction.finiteBaseHNN_residuallyFinite (phi := φq)
  obtain ⟨N, hN⟩ := Group.exists_finiteIndexNormalSubgroup_notMem (Ψ z) hΨz
  letI := N.isNormal'
  letI := N.isFiniteIndex'
  let R := E ⧸ N.toSubgroup
  haveI : Finite R := Subgroup.finite_quotient_of_finiteIndex
  let r : E →* R := QuotientGroup.mk' N.toSubgroup
  let liftR : R →* ULift.{u} R :=
    (MulEquiv.ulift (α := R)).symm.toMonoidHom
  refine ⟨ULift.{u} R, inferInstance, inferInstance,
    liftR.comp (r.comp Ψ), ?_⟩
  intro hr
  apply hN
  have hr' : r (Ψ z) = 1 := by
    have := congrArg (MulEquiv.ulift (α := R)) hr
    simpa [liftR] using this
  exact (QuotientGroup.eq_one_iff (Ψ z)).mp hr'

end

end HNNFiniteQuotientCriterion
end GroupApproximation
