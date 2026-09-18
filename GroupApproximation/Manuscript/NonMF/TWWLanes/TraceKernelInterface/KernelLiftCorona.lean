import GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.Predicates
import GroupApproximation.Manuscript.NonMFSentences.FactorizationTraceCoronaProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-31, part 1: quasidiagonal traces give trace-compatible corona homomorphisms

This file proves the step from quasidiagonality to the conclusion of
`TraceKernelLiftStatement`, with no hypothesis at all:

```text
τ 1 = 1,  τ quasidiagonal  ⟹  HasTraceCompatibleCoronaHom τ.
```

Let `φₙ : A → M_{kₙ}` be quasidiagonal models of `τ`. First drop finitely many models so that
every `kₙ ≥ 1` (`FactorizationTraceCoronaProof.exists_models_card_pos`, which uses `τ 1 = 1`).
Then `a ↦ [(φₙ(a))ₙ]` is a `⋆`-homomorphism into `ℓ∞(M_{kₙ}) / c₀(M_{kₙ})`
(`FactorizationTraceCoronaProof.coronaMap`), and it is unital. Here it is upgraded to a
`StarAlgHom` (`kernelLiftCoronaHom`). Along any nonprincipal ultrafilter `ω`, the ultratrace of
its trace-kernel image is `lim_ω tr(φₙ(a)) = τ(a)`, because `tr(φₙ(a)) → τ(a)` along `atTop`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace TraceKernelInterface

open Filter

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A] {τ : A → ℂ}

/-- The unital `⋆`-homomorphism `a ↦ [(φₙ(a))ₙ]` of a quasidiagonal model with nonempty
coordinate spaces. It is `FactorizationTraceCoronaProof.coronaMap M` with unitality and
`ℂ`-linearity packaged as a `StarAlgHom`. -/
def kernelLiftCoronaHom (M : Quasidiagonal.QuasidiagonalTraceModel τ)
    [∀ n, Nonempty (M.space n)] :
    A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ M.space n) where
  toFun a := FactorizationTraceCoronaProof.coronaMap M a
  map_one' := FactorizationTraceCoronaProof.coronaMap_one M
  map_mul' a b := map_mul (FactorizationTraceCoronaProof.coronaMap M) a b
  map_zero' := map_zero (FactorizationTraceCoronaProof.coronaMap M)
  map_add' a b := map_add (FactorizationTraceCoronaProof.coronaMap M) a b
  commutes' z := by
    calc FactorizationTraceCoronaProof.coronaMap M (algebraMap ℂ A z)
        = FactorizationTraceCoronaProof.coronaMap M (z • (1 : A)) := by
          rw [Algebra.algebraMap_eq_smul_one z]
      _ = z • FactorizationTraceCoronaProof.coronaMap M 1 :=
          map_smul (FactorizationTraceCoronaProof.coronaMap M) z 1
      _ = z • (1 : NormMatrixCStarCorona (fun n ↦ M.space n)) := by
          rw [FactorizationTraceCoronaProof.coronaMap_one]
      _ = algebraMap ℂ (NormMatrixCStarCorona (fun n ↦ M.space n)) z :=
          (Algebra.algebraMap_eq_smul_one z).symm
  map_star' a := map_star (FactorizationTraceCoronaProof.coronaMap M) a

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.kernelLiftCoronaHom

/-- `kernelLiftCoronaHom M a` is the corona class of the model sequence `(φₙ(a))ₙ`. -/
theorem kernelLiftCoronaHom_apply (M : Quasidiagonal.QuasidiagonalTraceModel τ)
    [∀ n, Nonempty (M.space n)] (a : A) :
    kernelLiftCoronaHom M a =
      normMatrixCStarCoronaMk (fun n ↦ M.space n) (FactorizationTraceCoronaProof.modelSeq M a) :=
  rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.kernelLiftCoronaHom_apply

/-- **The corona homomorphism of a quasidiagonal model is trace-compatible.** Along every
nonprincipal ultrafilter `ω`, the ultratrace of the trace-kernel image of
`kernelLiftCoronaHom M a` is `τ a`. -/
theorem kernelLiftCoronaHom_ultratrace (M : Quasidiagonal.QuasidiagonalTraceModel τ)
    [∀ n, Nonempty (M.space n)] (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite) (a : A) :
    TracialUltraproduct.ultratrace M.space ω
      (TracialUltraproduct.normMatrixCStarCoronaToTracialMatrixQuotient M.space ω hω
        (kernelLiftCoronaHom M a)) = τ a := by
  have hle : (ω : Filter ℕ) ≤ atTop := hω.trans Nat.cofinite_eq_atTop.le
  have hlim : Tendsto (fun n ↦ normTrace (M.space n) (M.map n a)) (ω : Filter ℕ)
      (nhds (τ a)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine Tendsto.mono_left ?_ hle
    refine (M.tendsto_trace a).congr fun n ↦ ?_
    exact norm_sub_rev _ _
  rw [kernelLiftCoronaHom_apply,
    TracialUltraproduct.normMatrixCStarCoronaToTracialMatrixQuotient_mk,
    TracialUltraproduct.ultratrace_mk]
  exact tendsto_nhds_unique
    (TracialUltraproduct.tendsto_seqUltratrace M.space ω
      (FactorizationTraceCoronaProof.modelSeq M a)) hlim

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.kernelLiftCoronaHom_ultratrace

/-- **Quasidiagonal unital traces have trace-compatible corona homomorphisms.** The models are
those of a quasidiagonal model with an initial segment dropped, and the ultrafilter is
`Filter.hyperfilter ℕ`. No `KK`, UCT or nuclearity input is used. -/
theorem kernelLift_hasTraceCompatibleCoronaHom_of_isQuasidiagonalTrace (hone : τ 1 = 1)
    (h : Quasidiagonal.IsQuasidiagonalTrace τ) : HasTraceCompatibleCoronaHom τ := by
  obtain ⟨M⟩ := h
  obtain ⟨M', hcard⟩ := FactorizationTraceCoronaProof.exists_models_card_pos M hone
  letI hne : ∀ n, Nonempty (M'.space n) := fun n ↦ Fintype.card_pos_iff.mp (hcard n)
  exact ⟨M'.space, hne, Filter.hyperfilter ℕ, Filter.hyperfilter_le_cofinite,
    kernelLiftCoronaHom M', kernelLiftCoronaHom_ultratrace M' _ _⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.kernelLift_hasTraceCompatibleCoronaHom_of_isQuasidiagonalTrace

end

end TraceKernelInterface
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
