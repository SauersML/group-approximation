import GroupApproximation.Manuscript.NonMF.RelatedTWW.Definitions
import GroupApproximation.Analysis.AsymptoticModelMFEmbedding
import GroupApproximation.Analysis.MatrixCoronaDedekindFinite
import GroupApproximation.Analysis.MFAlgebraDimensionNormalization
import GroupApproximation.Analysis.UCPContractiveMatrix
import GroupApproximation.Sofic.MFTraceCoronaBridge
import GroupApproximation.Manuscript.NinetyNineProblems.ProblemXImpliesIX
import GroupApproximation.Manuscript.NinetyNineProblems.StablyFinite
import GroupApproximation.Meta.AxiomGuard

/-!
# Related work (Tikuisis--White--Winter): the elementary implications

Census row `82cac0c03a39`, `non_mf_groups_exist.tex` L315--318:

> It also asked whether every separable nuclear stably finite $C^*$-algebra is
> quasidiagonal; for algebras that satisfy the universal coefficient theorem
> and have a faithful trace, the theorem of Tikuisis, White, and Winter recalled
> above answers this~\cite{TWW}.

The theorem recalled above, at L279--281:

> Tikuisis, White, and Winter proved that faithful traces on separable nuclear
> $C^*$-algebras satisfying the universal coefficient theorem are
> quasidiagonal~\cite{TWW}

Everything in this module is proved with no hypothesis beyond the printed ones.

## Proof route

1. *Quasidiagonal ⇒ MF.* The quasidiagonal models are exactly linear and
   star-preserving, so they form an asymptotic star model
   (`QuasidiagonalModel.toAsymptoticModel`). Its corona homomorphism is faithful
   because of the limsup norm recovery
   (`AsymptoticModelMFEmbedding.coronaHom_injective_of_normRecovery`). The
   strictly increasing dimensions of `HasMFEmbedding` come from
   `MFAlgebraDimension.hasMFEmbedding_iff`.
2. *MF ⇒ stably finite.* This is
   `MatrixCoronaFinite.cstarMatrix_mul_star_eq_one_of_hasMFEmbedding`.
3. *Faithful trace ⇒ stably finite.* This is
   `NinetyNineProblems.isStablyFiniteCStarAlgebra_of_faithfulTracialState`,
   consumed directly by `RelatedTWW.Sentence`.
4. *Faithful quasidiagonal trace ⇒ quasidiagonal algebra* (Brown's argument).
   * Cut off the finitely many empty models (`MFTraceModel.eventually_card_pos`).
   * The corona homomorphism of the tail is injective, because the faithful
     trace kills its kernel (`NinetyNineProblems.coronaHom_injective_of_faithful`).
     An injective star homomorphism of C⋆-algebras is isometric, and the corona
     norm is the limsup of the coordinate norms, so the models recover every
     norm.
   * Each model is unital and completely positive, hence contractive
     (`Quasidiagonal.ucp_norm_le`) and star-preserving (`Quasidiagonal.ucp_map_star`).
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace RelatedTWW

open Filter
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

/-! ## Quasidiagonal ⇒ MF ⇒ stably finite -/

/-- A quasidiagonal model is an asymptotic star model with identically zero
additive, scalar and adjoint defects. -/
def QuasidiagonalModel.toAsymptoticModel (Q : QuasidiagonalModel A) :
    NormCoronaAsymptoticLift.Model (X := Q.space) A where
  map n := ⇑(Q.map n)
  tendsto_mul a b := Q.tendsto_mul a b
  tendsto_add a b := ShulmanTrace.tendsto_zero_of_eq_zero fun n ↦ by
    simp only [map_add, sub_self, norm_zero]
  tendsto_smul c a := ShulmanTrace.tendsto_zero_of_eq_zero fun n ↦ by
    simp only [map_smul, sub_self, norm_zero]
  tendsto_star a := ShulmanTrace.tendsto_zero_of_eq_zero fun n ↦ by
    simp only [Q.map_star, Matrix.star_eq_conjTranspose, sub_self, norm_zero]
  bounded a := ⟨‖a‖, fun n ↦ Q.norm_le n a⟩

/-- **A quasidiagonal model gives an MF embedding.** -/
theorem QuasidiagonalModel.hasMFEmbedding (Q : QuasidiagonalModel A) :
    HasMFEmbedding A := by
  letI : ∀ n, Nonempty (Q.space n) := Q.nonempty
  exact (MFAlgebraDimension.hasMFEmbedding_iff A).mpr
    ⟨Q.space, Q.nonempty, fun n ↦ Fintype.card_pos_iff.mpr (Q.nonempty n),
      AsymptoticModelMFEmbedding.coronaHom Q.toAsymptoticModel,
      AsymptoticModelMFEmbedding.coronaHom_injective_of_normRecovery
        Q.toAsymptoticModel Q.limsup_norm⟩

/-- **Quasidiagonal algebras are MF algebras.** -/
theorem isMFAlgebra_of_isQuasidiagonalCStarAlgebra
    (h : IsQuasidiagonalCStarAlgebra A) : IsMFAlgebra A := by
  obtain ⟨hsep, ⟨Q⟩⟩ := h
  exact ⟨hsep, Q.hasMFEmbedding⟩

/-- **MF embeddability forces stable finiteness.** -/
theorem isStablyFiniteCStarAlgebra_of_hasMFEmbedding (hA : HasMFEmbedding A) :
    IsStablyFiniteCStarAlgebra A :=
  fun k _ hv ↦
    GroupApproximation.MatrixCoronaFinite.cstarMatrix_mul_star_eq_one_of_hasMFEmbedding
      hA (Fin (k + 1)) hv

/-- **Quasidiagonal algebras are stably finite.** So the Blackadar--Kirchberg
question asks only for the converse. -/
theorem isStablyFiniteCStarAlgebra_of_isQuasidiagonalCStarAlgebra
    (h : IsQuasidiagonalCStarAlgebra A) : IsStablyFiniteCStarAlgebra A :=
  isStablyFiniteCStarAlgebra_of_hasMFEmbedding
    (isMFAlgebra_of_isQuasidiagonalCStarAlgebra h).2

/-! ## A faithful quasidiagonal trace makes the algebra quasidiagonal -/

/-- The tail, from index `N` on, of the MF-trace model attached to a
quasidiagonal trace model. -/
def quasidiagonalTraceTail {τ : A → ℂ}
    (M : Quasidiagonal.QuasidiagonalTraceModel τ) (N : ℕ) :
    ShulmanTrace.MFTraceModel τ :=
  (M.toMFTraceModel Quasidiagonal.ucpContractive).shift N

/-- **Brown's argument.** A separable C⋆-algebra with a faithful quasidiagonal
tracial state is quasidiagonal. -/
theorem isQuasidiagonalCStarAlgebra_of_faithful_quasidiagonalTrace
    (hsep : TopologicalSpace.SeparableSpace A) (τ : FaithfulTracialState A)
    (hqd : Quasidiagonal.IsQuasidiagonalTrace (fun a : A ↦ τ a)) :
    IsQuasidiagonalCStarAlgebra A := by
  obtain ⟨M⟩ := hqd
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((M.toMFTraceModel Quasidiagonal.ucpContractive).eventually_card_pos
      τ.apply_one)
  have hne : ∀ n : ℕ, Nonempty (M.space (n + N)) := fun n ↦
    Fintype.card_pos_iff.mp (hN (n + N) (Nat.le_add_left N n))
  letI : ∀ n : ℕ, Nonempty ((quasidiagonalTraceTail M N).space n) := hne
  have hinj : Function.Injective (quasidiagonalTraceTail M N).coronaHom :=
    GroupApproximation.NinetyNineProblems.coronaHom_injective_of_faithful τ
      (quasidiagonalTraceTail M N)
  have hrec : ∀ a : A,
      Filter.limsup (fun n ↦ ‖M.map (n + N) a‖) atTop = ‖a‖ := by
    intro a
    calc
      Filter.limsup (fun n ↦ ‖M.map (n + N) a‖) atTop =
          ‖normMatrixCStarCoronaMk (fun n ↦ (quasidiagonalTraceTail M N).space n)
            ((quasidiagonalTraceTail M N).seq a)‖ := by
            change Filter.limsup
                (fun n ↦ ‖(quasidiagonalTraceTail M N).seq a n‖) atTop =
              ‖Ideal.Quotient.mk
                (nullMatrixSequenceIdeal
                  (fun n ↦ (quasidiagonalTraceTail M N).space n) cofinite)
                ((quasidiagonalTraceTail M N).seq a)‖
            simpa only [Nat.cofinite_eq_atTop] using
              (norm_filterMatrixCorona_mk_eq_limsup
                (fun n ↦ (quasidiagonalTraceTail M N).space n) cofinite
                ((quasidiagonalTraceTail M N).seq a)).symm
      _ = ‖(quasidiagonalTraceTail M N).coronaHom a‖ := by
            rw [ShulmanTrace.MFTraceModel.coronaHom_apply,
              ShulmanTrace.coronaQuotient_apply]
      _ = ‖a‖ := by
            simpa only [map_zero, dist_zero_right] using
              (NonUnitalStarAlgHom.isometry
                (quasidiagonalTraceTail M N).coronaHom hinj).dist_eq a 0
  exact ⟨hsep, ⟨{
    space := fun n ↦ M.space (n + N)
    nonempty := hne
    map := fun n ↦ M.map (n + N)
    completelyPositive := fun n ↦ M.completelyPositive (n + N)
    norm_le := fun n a ↦
      Quasidiagonal.ucp_norm_le (M.map (n + N)) (M.map_one (n + N))
        (M.completelyPositive (n + N)) a
    map_star := fun n a ↦
      Quasidiagonal.ucp_map_star (M.map (n + N)) (M.map_one (n + N))
        (M.completelyPositive (n + N)) a
    tendsto_mul := fun a b ↦ (M.tendsto_mul a b).comp (tendsto_add_atTop_nat N)
    limsup_norm := hrec }⟩⟩

end

end RelatedTWW
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.RelatedTWW

#audit_axioms QuasidiagonalModel.hasMFEmbedding
#audit_axioms isMFAlgebra_of_isQuasidiagonalCStarAlgebra
#audit_axioms isStablyFiniteCStarAlgebra_of_hasMFEmbedding
#audit_axioms isStablyFiniteCStarAlgebra_of_isQuasidiagonalCStarAlgebra
#audit_axioms isQuasidiagonalCStarAlgebra_of_faithful_quasidiagonalTrace
