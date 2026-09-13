import GroupApproximation.Sofic.AffineHNNBaseRealization
import GroupApproximation.Sofic.CommutingLampCollapse
import GroupApproximation.Sofic.CliffordWitnessDirectDefect
import GroupApproximation.Sofic.CDEOperatorMF
import GroupApproximation.Manuscript.NonMFSentences.IntroConventionSentences
import GroupApproximation.Meta.AxiomGuard

/-!
# Introduction: every MF homomorphism of `W` kills `ε`

`non_mf_groups_exist.tex`, tex line 134, census key `9930600167a4`:

> Every homomorphism from $W$ to an MF group kills $\varepsilon$
> (Section~\ref{sec:amenable-nonqd}).

`W = Cl(X) ⋊ V` is the literal group of the preceding sentence, `IntroConventionSentences.PrintedW`
(census key `651e122a919e`).  There `Γ = ℤ³ ⋊ SL₃(ℤ)` is `AffineSL3Doubling.Gamma`,
`α(v,A) = (2v,A)` is `AffineSL3Doubling.alpha`, and `ε` is the central Clifford sign
`inl (sign X)`.

Section `sec:amenable-nonqd` proves the sentence as `prop:clifford-self-embedding`.  Lean proves
that proposition for every countable group with property (T) and an injective endomorphism missing
some element: `CliffordWitnessDirectDefect.manuscriptMapSignEqOneOfIsOperatorMFTarget`.  This
module applies it at the literal instance and proves each hypothesis there.

* `α` is injective, and `a = (e₁, 1)` is not in its image (`AffineSL3Doubling.alpha_injective`,
  `AffineSL3Doubling.a_not_mem_range`).
* `Γ` has property (T).  The repository proves (T) for the matrix group
  `ExplicitLinearModel.gammaBar ≤ GL₄(ℚ)` (`CommutingLampCollapse.gammaBar_hasKazhdanPropertyT`).
  `gammaEquiv : AffineSL3Doubling.Gamma ≃* gammaBar` sends `(v, A)` to `[[A, v], [0, 1]]`:
  * it is a homomorphism because `[[A,0],[0,1]] [[1,v],[0,1]] [[A,0],[0,1]]⁻¹ = [[1,Av],[0,1]]`;
  * it is injective because the entries determine `v` and `A`;
  * it is surjective by the affine normal form `AffineHNNBase.gammaBar_affUnit_form`.

  (T) transfers along it by `HasKazhdanPropertyT.of_mulEquiv`.
* `Γ` is countable, through the same equivalence.

The printed "MF group" is the Introduction's definition for countable groups (tex lines 86–99,
`IsCDEOperatorMF`).  The named proposition states the sentence for those targets, and also for
every operator-MF group, countable or not.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences
namespace IntroWitnessSignSentence

open ExplicitLinearModel (Mat gammaBar)
open LiteralBaseCompleteness (transMat transUnit transUnit_mul blockEmbed4
  blockEmbed4_val_explicit)
open LiteralP13MatrixModel (SL3)
open AffineHNNBase (affUnit affUnit_val affUnit_mem_gammaBar gammaBar_affUnit_form)
open IntroConventionSentences (PrintedW PrintedX)

universe v

noncomputable section

/-! ## `ℤ³ ⋊ SL₃(ℤ)` is the affine matrix group `Γ̄` -/

/-- `SL₃(ℤ)` acts on `ℤ³` by the matrix-vector product. -/
theorem action_toAdd (A : AffineSL3Doubling.Linear)
    (v : Multiplicative AffineSL3Doubling.Lattice) :
    Multiplicative.toAdd (AffineSL3Doubling.action A v) =
      Matrix.mulVec (A : Matrix (Fin 3) (Fin 3) ℤ) (Multiplicative.toAdd v) :=
  rfl

set_option linter.unusedSimpArgs false in
/-- The translation part `v ↦ [[1, v], [0, 1]]`. -/
def translationHom : Multiplicative AffineSL3Doubling.Lattice →* Matˣ where
  toFun v := transUnit (Multiplicative.toAdd v 0 : ℚ) (Multiplicative.toAdd v 1 : ℚ)
    (Multiplicative.toAdd v 2 : ℚ)
  map_one' := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    fin_cases i <;> fin_cases j <;>
      norm_num [transUnit, transMat, Matrix.one_apply, toAdd_one]
  map_mul' v w := by
    simp only [toAdd_mul, Pi.add_apply, Int.cast_add, transUnit_mul]

theorem translationHom_val (v : Multiplicative AffineSL3Doubling.Lattice) :
    ((translationHom v : Matˣ) : Mat) =
      transMat (Multiplicative.toAdd v 0 : ℚ) (Multiplicative.toAdd v 1 : ℚ)
        (Multiplicative.toAdd v 2 : ℚ) :=
  rfl

set_option linter.unusedSimpArgs false in
/-- Conjugating `[[1, v], [0, 1]]` by `[[A, 0], [0, 1]]` gives `[[1, Av], [0, 1]]`. -/
theorem translationHom_conj (A : AffineSL3Doubling.Linear) :
    translationHom.comp (AffineSL3Doubling.action A).toMonoidHom =
      (MulAut.conj (blockEmbed4 A)).toMonoidHom.comp translationHom := by
  refine MonoidHom.ext fun v => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [eq_mul_inv_iff_mul_eq]
  calc translationHom (AffineSL3Doubling.action A v) * blockEmbed4 A
      = affUnit A (fun i => (Multiplicative.toAdd (AffineSL3Doubling.action A v) i : ℚ)) :=
        rfl
    _ = blockEmbed4 A * translationHom v := by
      refine Units.ext ?_
      rw [affUnit_val, Units.val_mul, blockEmbed4_val_explicit, translationHom_val,
        action_toAdd]
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        norm_num [transMat, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.mulVec, dotProduct,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]

/-- `(v, A) ↦ [[A, v], [0, 1]]`, the universal-property extension of the translation part and the
block embedding of `SL₃(ℤ)`. -/
def affineHom : AffineSL3Doubling.Gamma →* Matˣ :=
  SemidirectProduct.lift translationHom blockEmbed4 translationHom_conj

theorem affineHom_apply (g : AffineSL3Doubling.Gamma) :
    affineHom g = affUnit g.right (fun i => (Multiplicative.toAdd g.left i : ℚ)) :=
  rfl

theorem affineHom_mem (g : AffineSL3Doubling.Gamma) : affineHom g ∈ gammaBar := by
  rw [affineHom_apply]
  exact affUnit_mem_gammaBar (Multiplicative.toAdd g.left) g.right

/-- The upper-left `3 × 3` block of `[[A, q], [0, 1]]` is `A`. -/
theorem affUnit_val_castSucc (A : SL3) (q : Fin 3 → ℚ) (i j : Fin 3) :
    ((affUnit A q : Matˣ) : Mat) i.castSucc j.castSucc =
      ((A : Matrix (Fin 3) (Fin 3) ℤ) i j : ℚ) := by
  rw [affUnit_val]
  fin_cases i <;> fin_cases j <;> rfl

/-- The last column of `[[A, q], [0, 1]]` is `q`. -/
theorem affUnit_val_last (A : SL3) (q : Fin 3 → ℚ) (i : Fin 3) :
    ((affUnit A q : Matˣ) : Mat) i.castSucc (Fin.last 3) = q i := by
  rw [affUnit_val]
  fin_cases i <;> rfl

theorem affineHom_injective : Function.Injective affineHom := by
  intro g h hgh
  have hval : ((affineHom g : Matˣ) : Mat) = affineHom h := by rw [hgh]
  rw [affineHom_apply, affineHom_apply] at hval
  refine SemidirectProduct.ext ?_ ?_
  · refine Multiplicative.toAdd.injective (funext fun i => ?_)
    have e := congrFun (congrFun hval i.castSucc) (Fin.last 3)
    rw [affUnit_val_last, affUnit_val_last] at e
    exact_mod_cast e
  · refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    have e := congrFun (congrFun hval i.castSucc) j.castSucc
    rw [affUnit_val_castSucc, affUnit_val_castSucc] at e
    exact_mod_cast e

/-- `ℤ³ ⋊ SL₃(ℤ) → Γ̄`. -/
def gammaHom : AffineSL3Doubling.Gamma →* gammaBar :=
  affineHom.codRestrict gammaBar affineHom_mem

theorem gammaHom_injective : Function.Injective gammaHom := fun _ _ hgh =>
  affineHom_injective (congrArg Subtype.val hgh)

theorem gammaHom_surjective : Function.Surjective gammaHom := by
  rintro ⟨u, hu⟩
  obtain ⟨w, A, rfl⟩ := gammaBar_affUnit_form hu
  exact ⟨⟨Multiplicative.ofAdd w, A⟩, Subtype.ext rfl⟩

/-- **`ℤ³ ⋊ SL₃(ℤ) ≅ Γ̄`**: `AffineSL3Doubling.Gamma` is isomorphic to the affine matrix group
`ExplicitLinearModel.gammaBar`, by `(v, A) ↦ [[A, v], [0, 1]]`. -/
def gammaEquiv : AffineSL3Doubling.Gamma ≃* gammaBar :=
  MulEquiv.ofBijective gammaHom ⟨gammaHom_injective, gammaHom_surjective⟩

theorem gammaEquiv_apply (g : AffineSL3Doubling.Gamma) :
    ((gammaEquiv g : gammaBar) : Matˣ) =
      affUnit g.right (fun i => (Multiplicative.toAdd g.left i : ℚ)) :=
  rfl

/-- `ℤ³ ⋊ SL₃(ℤ)` has property (T): it is isomorphic to `Γ̄`, which has (T). -/
theorem gamma_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} AffineSL3Doubling.Gamma :=
  HasKazhdanPropertyT.of_mulEquiv gammaEquiv CommutingLampCollapse.gammaBar_hasKazhdanPropertyT

theorem gamma_countable : Countable AffineSL3Doubling.Gamma :=
  gammaEquiv.injective.countable

/-! ## tex line 134, `9930600167a4`: MF homomorphisms of `W` kill `ε` -/

/-- **Printed sentence** (tex line 134, census key `9930600167a4`).

> Every homomorphism from $W$ to an MF group kills $\varepsilon$
> (Section~\ref{sec:amenable-nonqd}).

`W = PrintedW = Cl(X) ⋊ V` and `ε = inl (sign X)`, literally as in
`IntroConventionSentences.manuscriptSentence_cliffordWitnessGroup`.  The first clause covers
every operator-MF target group.  The second covers countable targets that are MF in the printed
sense of the Introduction (tex lines 86–99, `IsCDEOperatorMF`). -/
def PrintedWitnessMFHomKillsSign : Prop :=
  (∀ (M : Type v) [Group M], IsOperatorMF M →
    ∀ f : PrintedW →* M, f (SemidirectProduct.inl (CliffordLamp.sign PrintedX)) = 1) ∧
  (∀ (M : Type v) [Group M] [Countable M], IsCDEOperatorMF M →
    ∀ f : PrintedW →* M, f (SemidirectProduct.inl (CliffordLamp.sign PrintedX)) = 1)

theorem manuscriptSentence_witnessMFHomKillsSign : PrintedWitnessMFHomKillsSign.{v} := by
  haveI : Countable AffineSL3Doubling.Gamma := gamma_countable
  refine ⟨fun M _ hM f => ?_, fun M _ _ hM f => ?_⟩
  · exact CliffordWitnessDirectDefect.manuscriptMapSignEqOneOfIsOperatorMFTarget
      AffineSL3Doubling.Gamma AffineSL3Doubling.alpha AffineSL3Doubling.alpha_injective
      AffineSL3Doubling.a_not_mem_range gamma_hasKazhdanPropertyT M hM f
  · exact CliffordWitnessDirectDefect.manuscriptMapSignEqOneOfIsOperatorMFTarget
      AffineSL3Doubling.Gamma AffineSL3Doubling.alpha AffineSL3Doubling.alpha_injective
      AffineSL3Doubling.a_not_mem_range gamma_hasKazhdanPropertyT M
      ((isCDEOperatorMF_iff_isOperatorMF M).1 hM) f

end

end IntroWitnessSignSentence
end NonMFSentences
end Manuscript
end GroupApproximation

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.IntroWitnessSignSentence.manuscriptSentence_witnessMFHomKillsSign
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.IntroWitnessSignSentence.PrintedWitnessMFHomKillsSign
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.IntroWitnessSignSentence.gammaEquiv
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.IntroWitnessSignSentence.gamma_hasKazhdanPropertyT
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.IntroWitnessSignSentence.gamma_countable
