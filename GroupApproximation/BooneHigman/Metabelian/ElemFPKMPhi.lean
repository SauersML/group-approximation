import GroupApproximation.BooneHigman.Metabelian.ElemFPKMGroup
import GroupApproximation.PropertyT.FreeAlgebraDegree
import GroupApproximation.Meta.AxiomGuard

/-!
# The homomorphism `KMGroup X d → St_{d+5}(ℤ⟨X⟩)`

Rank-`d + 5` generalisation of the second half of
`GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.FreePresentation`.  The generators
`g(i, j, s)` are sent to the Steinberg generators `x_{ij}(coef s)`, and `φ` is computed on the
iterated commutator words `word X d u i j`: they represent `x_{ij}` of the monomial `u`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open scoped commutatorElement
open FreeAlgebraDegree

noncomputable section

variable (X : Type*) (d : ℕ)

/-! ## The homomorphism to `St_{d+5}(ℤ⟨X⟩)` -/

/-- The coefficient of a generator. -/
def coef : Option X → FreeAlgebra ℤ X
  | none => 1
  | some a => FreeAlgebra.ι ℤ a

theorem coef_none : coef X none = 1 := rfl

theorem coef_some (a : X) : coef X (some a) = FreeAlgebra.ι ℤ a := rfl

/-- Images of the generators. -/
def phiGen (g : Gen X d) : SteinbergGroup (Fin (d + 5)) (FreeAlgebra ℤ X) :=
  if h : g.1 = g.2.1 then 1 else SteinbergGroup.x g.1 g.2.1 h (coef X g.2.2)

theorem phiGen_diag (i : Fin (d + 5)) (s : Option X) : phiGen X d (i, i, s) = 1 := by
  unfold phiGen
  exact dif_pos rfl

theorem phiGen_of_ne (i j : Fin (d + 5)) (s : Option X) (h : i ≠ j) :
    phiGen X d (i, j, s) = SteinbergGroup.x i j h (coef X s) := by
  unfold phiGen
  exact dif_neg h

theorem phi_rels : ∀ r ∈ rels X d, FreeGroup.lift (phiGen X d) r = 1 := by
  intro r hr
  rcases hr with ((⟨⟨i, s⟩, rfl⟩ | ⟨⟨⟨⟨i, j, s⟩, ⟨k, l, t⟩⟩, hij, hkl, hjk, hil⟩, rfl⟩) |
      ⟨⟨⟨i, j, k, t⟩, hij, hjk, hik⟩, rfl⟩) | ⟨⟨⟨i, j, k, a⟩, hij, hjk, hik⟩, rfl⟩
  · change FreeGroup.lift (phiGen X d) (FreeGroup.of ((i, i, s) : Gen X d)) = 1
    rw [FreeGroup.lift_apply_of]
    exact phiGen_diag X d i s
  · change FreeGroup.lift (phiGen X d)
      ⁅FreeGroup.of ((i, j, s) : Gen X d), FreeGroup.of ((k, l, t) : Gen X d)⁆ = 1
    simp only [map_commutatorElement, FreeGroup.lift_apply_of]
    rw [phiGen_of_ne X d i j s hij, phiGen_of_ne X d k l t hkl]
    exact (SteinbergGroup.x_commute_of_ne i j k l hij hkl hjk (Ne.symm hil) _ _).commutator_eq
  · change FreeGroup.lift (phiGen X d)
      (⁅FreeGroup.of ((i, j, none) : Gen X d), FreeGroup.of ((j, k, t) : Gen X d)⁆ *
        (FreeGroup.of ((i, k, t) : Gen X d))⁻¹) = 1
    simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
    rw [phiGen_of_ne X d i j none hij, phiGen_of_ne X d j k t hjk, phiGen_of_ne X d i k t hik,
      SteinbergGroup.x_commutator i j k hij hjk hik, coef_none, one_mul (coef X t),
      mul_inv_cancel]
  · change FreeGroup.lift (phiGen X d)
      (⁅FreeGroup.of ((i, j, some a) : Gen X d), FreeGroup.of ((j, k, none) : Gen X d)⁆ *
        (FreeGroup.of ((i, k, some a) : Gen X d))⁻¹) = 1
    simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
    rw [phiGen_of_ne X d i j (some a) hij, phiGen_of_ne X d j k none hjk,
      phiGen_of_ne X d i k (some a) hik, SteinbergGroup.x_commutator i j k hij hjk hik,
      coef_none, mul_one (coef X (some a)), mul_inv_cancel]

/-- The homomorphism `φ : KMGroup X d → St_{d+5}(ℤ⟨X⟩)`. -/
def phi : KMGroup X d →* SteinbergGroup (Fin (d + 5)) (FreeAlgebra ℤ X) :=
  PresentedGroup.toGroup (phi_rels X d)

theorem phi_gen (i j : Fin (d + 5)) (s : Option X) (h : i ≠ j) :
    phi X d (gen X d i j s) = SteinbergGroup.x i j h (coef X s) := by
  change PresentedGroup.toGroup (phi_rels X d) (PresentedGroup.of ((i, j, s) : Gen X d)) = _
  rw [PresentedGroup.toGroup.of]
  exact phiGen_of_ne X d i j s h

/-- `φ` sends the word of `u` to the Steinberg generator of the monomial `u`. -/
theorem phi_word (u : List X) (i j : Fin (d + 5)) (h : i ≠ j) :
    phi X d (word X d u i j) =
      SteinbergGroup.x i j h (wordMonomial X ℤ (FreeMonoid.ofList u)) := by
  induction u generalizing i j with
  | nil =>
      rw [word_nil, phi_gen X d i j none h, coef_none, FreeMonoid.ofList_nil, wordMonomial_one]
  | cons a u ih =>
      have hip : i ≠ spare i j := (spare_ne_left i j).symm
      have hpj : spare i j ≠ j := spare_ne_right i j
      rw [word_cons, map_commutatorElement, phi_gen X d i (spare i j) (some a) hip,
        ih (spare i j) j hpj, SteinbergGroup.x_commutator i (spare i j) j hip hpj h, coef_some,
        FreeMonoid.ofList_cons, ← wordMonomial_mul, wordMonomial_of]

end

end GroupApproximation.BooneHigman.Metabelian.ElemFP

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.coef
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.coef_none
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.coef_some
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.phiGen
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.phiGen_diag
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.phiGen_of_ne
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.phi_rels
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.phi
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.phi_gen
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.phi_word
