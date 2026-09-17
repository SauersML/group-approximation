import GroupApproximation.BooneHigman.Metabelian.ElemFPKMRoots
import GroupApproximation.Meta.AxiomGuard

/-!
# `KMGroup X d ≅ St_{d+5}(ℤ⟨X⟩)`, so `St_{d+5}(ℤ⟨X⟩)` is finitely presented

Rank-`d + 5` generalisation of
`GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.SteinbergIso`.  The root maps
`psiRoot X d i j hij` satisfy the three Steinberg relator families, so they define
`ψ : St_{d+5}(ℤ⟨X⟩) → KMGroup X d`.  On generators, `ψ ∘ φ = id` and `φ ∘ ψ = id` (the latter by
induction over `ℤ⟨X⟩`, using `phi_word` on monomials).  Hence `kmEquiv X d`, and for a finite
alphabet `X` the Steinberg group `St_{d+5}(ℤ⟨X⟩)` is finitely presented
(`steinbergFreeAlgebra_isFinitelyPresented`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open scoped commutatorElement
open FreeAlgebraDegree
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP (comm_mul_right)

noncomputable section

variable (X : Type*) (d : ℕ)

/-- The adjacent Steinberg relation for the root maps. -/
theorem psiRoot_adjacent (i j k : Fin (d + 5)) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : FreeAlgebra ℤ X) :
    ⁅psiRoot X d i j hij a, psiRoot X d j k hjk b⁆ = psiRoot X d i k hik (a * b) := by
  refine freeAlgebra_induction X ?_ ?_ ?_ b
  · intro q r hq hr
    rw [psiRoot_add X d j k hjk q r, comm_mul_right, hq, hr,
      mul_assoc (psiRoot X d i k hik (a * q)) (psiRoot X d j k hjk q)
        (psiRoot X d i k hik (a * r)),
      (psiRoot_commute X d j k i k hjk hik (Ne.symm hik) hjk q (a * r)).eq, ← mul_assoc,
      mul_inv_cancel_right, mul_add, psiRoot_add X d i k hik (a * q) (a * r)]
  · intro q hq
    rw [psiRoot_neg X d j k hjk q, commutatorElement_inv_right, ← commutatorElement_inv, hq,
      (psiRoot_commute X d j k i k hjk hik (Ne.symm hik) hjk q (a * q)).inv_right.inv_left.eq,
      inv_mul_cancel_right, mul_neg, psiRoot_neg X d i k hik (a * q)]
  · intro w
    rw [psiRoot_monomial X d j k hjk w]
    have h := adj_word X d i j k hij hjk hik (FreeMonoid.toList w) a
    rwa [FreeMonoid.ofList_toList] at h

/-- Images of the Steinberg generators. -/
def psiGen (g : SteinbergGenerator (Fin (d + 5)) (FreeAlgebra ℤ X)) : KMGroup X d :=
  psiRoot X d g.row g.column g.row_ne_column g.coefficient

theorem psi_rels : ∀ r ∈ SteinbergGroup.relations (I := Fin (d + 5)) (R := FreeAlgebra ℤ X),
    FreeGroup.lift (psiGen X d) r = 1 := by
  intro r hr
  change SteinbergGroup.IsRelation r at hr
  cases hr with
  | add i j hij a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      exact mul_inv_eq_one.mpr (psiRoot_add X d i j hij a b).symm
  | commute i j k l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of]
      exact (psiRoot_commute X d i j k l hij hkl hjk (Ne.symm hli) a b).commutator_eq
  | adjacent i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
      exact mul_inv_eq_one.mpr (psiRoot_adjacent X d i j k hij hjk hik a b)

/-- The homomorphism `ψ : St_{d+5}(ℤ⟨X⟩) → KMGroup X d`. -/
def psi : SteinbergGroup (Fin (d + 5)) (FreeAlgebra ℤ X) →* KMGroup X d :=
  PresentedGroup.toGroup (psi_rels X d)

theorem psi_x (i j : Fin (d + 5)) (h : i ≠ j) (a : FreeAlgebra ℤ X) :
    psi X d (SteinbergGroup.x i j h a) = psiRoot X d i j h a := by
  exact PresentedGroup.toGroup.of (psi_rels X d)

theorem psi_comp_phi : (psi X d).comp (phi X d) = MonoidHom.id (KMGroup X d) := by
  apply PresentedGroup.ext
  rintro ⟨i, j, s⟩
  change psi X d (phi X d (gen X d i j s)) = gen X d i j s
  by_cases h : i = j
  · subst h
    rw [gen_diag, map_one, map_one]
  · rw [phi_gen X d i j s h, psi_x]
    cases s with
    | none =>
        have h1 := psiRoot_monomial X d i j h 1
        rw [wordMonomial_one, FreeMonoid.toList_one, word_nil] at h1
        exact h1
    | some a =>
        have h1 := psiRoot_monomial X d i j h (FreeMonoid.of a)
        rw [wordMonomial_of, FreeMonoid.toList_of, word_cons, word_nil,
          gen_adj_some X d i (spare i j) j a (spare_ne_left i j).symm (spare_ne_right i j) h]
          at h1
        exact h1

theorem phi_psiRoot (i j : Fin (d + 5)) (h : i ≠ j) (p : FreeAlgebra ℤ X) :
    phi X d (psiRoot X d i j h p) = SteinbergGroup.x i j h p := by
  refine freeAlgebra_induction X ?_ ?_ ?_ p
  · intro q r hq hr
    rw [psiRoot_add, map_mul, hq, hr, SteinbergGroup.x_mul]
  · intro q hq
    rw [psiRoot_neg, map_inv, hq, SteinbergGroup.x_neg]
  · intro w
    rw [psiRoot_monomial, phi_word X d (FreeMonoid.toList w) i j h, FreeMonoid.ofList_toList]

theorem phi_comp_psi :
    (phi X d).comp (psi X d) =
      MonoidHom.id (SteinbergGroup (Fin (d + 5)) (FreeAlgebra ℤ X)) := by
  apply PresentedGroup.ext
  rintro ⟨i, j, h, a⟩
  change phi X d (psi X d (SteinbergGroup.x i j h a)) = SteinbergGroup.x i j h a
  rw [psi_x]
  exact phi_psiRoot X d i j h a

/-- `KMGroup X d ≅ St_{d+5}(ℤ⟨X⟩)`. -/
def kmEquiv : KMGroup X d ≃* SteinbergGroup (Fin (d + 5)) (FreeAlgebra ℤ X) :=
  MonoidHom.toMulEquiv (phi X d) (psi X d) (psi_comp_phi X d) (phi_comp_psi X d)

/-- For a finite alphabet `X`, the Steinberg group `St_{d+5}(ℤ⟨X⟩)` is finitely presented. -/
theorem steinbergFreeAlgebra_isFinitelyPresented [Finite X] :
    Group.IsFinitelyPresented (SteinbergGroup (Fin (d + 5)) (FreeAlgebra ℤ X)) := by
  haveI := kmGroup_isFinitelyPresented X d
  exact Group.IsFinitelyPresented.equiv (kmEquiv X d)

end

end GroupApproximation.BooneHigman.Metabelian.ElemFP

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.psiRoot_adjacent
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.psiGen
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.psi_rels
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.psi
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.psi_x
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.psi_comp_phi
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.phi_psiRoot
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.phi_comp_psi
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.kmEquiv
#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.steinbergFreeAlgebra_isFinitelyPresented
