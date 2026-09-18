import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.RootExtension
import GroupApproximation.Meta.AxiomGuard

/-!
# `KMGroup X ≅ St_5(ℤ⟨X⟩)`, so `St_5(ℤ⟨X⟩)` is finitely presented

The root maps `psiRoot X i j hij` satisfy the three Steinberg relator families (`psiRoot_add`,
`psiRoot_commute`, `psiRoot_adjacent`).  So they define a homomorphism
`ψ : St_5(ℤ⟨X⟩) → KMGroup X`.  Checking on generators gives:

* `ψ ∘ φ = id`, because `ψ` sends `x_{ij}(1)` and `x_{ij}(a)` to `g(i, j, none)` and
  `g(i, j, some a)`;
* `φ ∘ ψ = id`, because `φ (ψ_{ij}(p)) = x_{ij}(p)` by induction over `p` (`phi_word` on
  monomials).

Hence `kmEquiv X : KMGroup X ≃* St_5(ℤ⟨X⟩)`, and for a finite alphabet `X` the Steinberg group
`St_5(ℤ⟨X⟩)` is finitely presented (`steinbergFreeAlgebra_isFinitelyPresented`).  This is the
special case of the Krstić–McCool theorem used in `LeavittFP.Endpoints`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP

open scoped commutatorElement
open FreeAlgebraDegree

noncomputable section

variable (X : Type*)

/-- Images of the Steinberg generators. -/
def psiGen (g : SteinbergGenerator (Fin 5) (FreeAlgebra ℤ X)) : KMGroup X :=
  psiRoot X g.row g.column g.row_ne_column g.coefficient

theorem psi_rels : ∀ r ∈ SteinbergGroup.relations (I := Fin 5) (R := FreeAlgebra ℤ X),
    FreeGroup.lift (psiGen X) r = 1 := by
  intro r hr
  change SteinbergGroup.IsRelation r at hr
  cases hr with
  | add i j hij a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      exact mul_inv_eq_one.mpr (psiRoot_add X i j hij a b).symm
  | commute i j k l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of]
      exact (psiRoot_commute X i j k l hij hkl hjk (Ne.symm hli) a b).commutator_eq
  | adjacent i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
      exact mul_inv_eq_one.mpr (psiRoot_adjacent X i j k hij hjk hik a b)

/-- The homomorphism `ψ : St_5(ℤ⟨X⟩) → KMGroup X`. -/
def psi : SteinbergGroup (Fin 5) (FreeAlgebra ℤ X) →* KMGroup X :=
  PresentedGroup.toGroup (psi_rels X)

theorem psi_x (i j : Fin 5) (h : i ≠ j) (a : FreeAlgebra ℤ X) :
    psi X (SteinbergGroup.x i j h a) = psiRoot X i j h a := by
  exact PresentedGroup.toGroup.of (psi_rels X)

theorem psi_comp_phi : (psi X).comp (phi X) = MonoidHom.id (KMGroup X) := by
  apply PresentedGroup.ext
  rintro ⟨i, j, s⟩
  change psi X (phi X (gen X i j s)) = gen X i j s
  by_cases h : i = j
  · subst h
    rw [gen_diag, map_one, map_one]
  · rw [phi_gen X i j s h, psi_x]
    cases s with
    | none =>
        have h1 := psiRoot_monomial X i j h 1
        rw [wordMonomial_one, FreeMonoid.toList_one, word_nil] at h1
        exact h1
    | some a =>
        have h1 := psiRoot_monomial X i j h (FreeMonoid.of a)
        rw [wordMonomial_of, FreeMonoid.toList_of, word_cons, word_nil,
          gen_adj_some X i (spare i j) j a (spare_ne_left i j).symm (spare_ne_right i j) h] at h1
        exact h1

theorem phi_psiRoot (i j : Fin 5) (h : i ≠ j) (p : FreeAlgebra ℤ X) :
    phi X (psiRoot X i j h p) = SteinbergGroup.x i j h p := by
  refine freeAlgebra_induction X ?_ ?_ ?_ p
  · intro q r hq hr
    rw [psiRoot_add, map_mul, hq, hr, SteinbergGroup.x_mul]
  · intro q hq
    rw [psiRoot_neg, map_inv, hq, SteinbergGroup.x_neg]
  · intro w
    rw [psiRoot_monomial, phi_word X (FreeMonoid.toList w) i j h, FreeMonoid.ofList_toList]

theorem phi_comp_psi :
    (phi X).comp (psi X) = MonoidHom.id (SteinbergGroup (Fin 5) (FreeAlgebra ℤ X)) := by
  apply PresentedGroup.ext
  rintro ⟨i, j, h, a⟩
  change phi X (psi X (SteinbergGroup.x i j h a)) = SteinbergGroup.x i j h a
  rw [psi_x]
  exact phi_psiRoot X i j h a

/-- `KMGroup X ≅ St_5(ℤ⟨X⟩)`. -/
def kmEquiv : KMGroup X ≃* SteinbergGroup (Fin 5) (FreeAlgebra ℤ X) :=
  MonoidHom.toMulEquiv (phi X) (psi X) (psi_comp_phi X) (phi_comp_psi X)

/-- For a finite alphabet `X`, the Steinberg group `St_5(ℤ⟨X⟩)` is finitely presented. -/
theorem steinbergFreeAlgebra_isFinitelyPresented [Finite X] :
    Group.IsFinitelyPresented (SteinbergGroup (Fin 5) (FreeAlgebra ℤ X)) := by
  haveI := kmGroup_isFinitelyPresented X
  exact Group.IsFinitelyPresented.equiv (kmEquiv X)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.steinbergFreeAlgebra_isFinitelyPresented

end

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.psiGen
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.psi_rels
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.psi
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.psi_x
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.psi_comp_phi
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.phi_psiRoot
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.phi_comp_psi
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.kmEquiv
