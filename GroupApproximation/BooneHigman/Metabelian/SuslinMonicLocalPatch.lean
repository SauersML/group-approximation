import GroupApproximation.BooneHigman.Metabelian.SuslinMonicLocalEndpoint
import Mathlib.RingTheory.Localization.AtPrime.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Local monic theorem + patching ⟹ the global monic Statement

Lane `bh-met-93i`.  `suslinMonic_PatchStatement` is Suslin's local-global principle (Quillen
patching) for stably elementary `SL₂`-blocks in rank `3`, stated only for the matrices that
`suslinCongInd_MonicStab` is about.  It is a `def ... : Prop`, NOT proved here, and it is not a
hypothesis of any root theorem.  `suslinMonicLocal_monicStatement_of_patch` shows that it,
together with the unconditional local theorem `suslinMonicLocal_stab_map`
(`SuslinMonicLocalEndpoint.lean`), gives `suslinCongInd_MonicStatement`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- **QUILLEN–SUSLIN PATCHING, OPEN IN THIS REPOSITORY.**  (LOUD.)  For `τ ∈ SL₂(R[X])` with
`lc τ₀₀ ∈ Rˣ` and `diag(τ(0), 1) ∈ E₃(R)`: if the image of `diag(τ, 1)` lies in
`E₃(R_𝔪[X])` for every maximal ideal `𝔪`, then `diag(τ, 1) ∈ E₃(R[X])`.

TRUE: put `σ = diag(τ, 1) · diag(τ(0), 1)⁻¹ ∈ GL₃(R[X])`.  Then `σ(0) = 1`, and `σ` is locally
elementary because `diag(τ(0), 1) ∈ E₃(R)` maps into every `E₃(R_𝔪[X])`.  Suslin's local-global
principle for `E_n`, `n ≥ 3` (Quillen patching) gives `σ ∈ E₃(R[X])`, hence `diag(τ, 1) ∈
E₃(R[X])`.  This is the ONLY remaining gap between the unconditional local theorem
(`suslinMonicLocal_monicStab`, `suslinMonicLocal_stab_map`) and
`suslinCongInd_MonicStatement`.  It is NOT proved here, NOT a hypothesis of any root theorem,
and NOT an equivalent restatement of the monic Statement: the patching argument (the
`X ↦ X + a Y` / `s`-power trick) is a separate proof. -/
def suslinMonic_PatchStatement : Prop :=
  ∀ (R : Type) [CommRing R] (τ : (Matrix (Fin 2) (Fin 2) R[X])ˣ),
    Matrix.det (τ : Matrix (Fin 2) (Fin 2) R[X]) = 1 →
    IsUnit ((τ : Matrix (Fin 2) (Fin 2) R[X]) 0 0).leadingCoeff →
    stabilizeUnit (R := R) (κ := Unit)
        (elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.constantCoeff (R := R)) τ) ∈
      elementaryGroup (Fin 2 ⊕ Unit) R →
    (∀ (𝔪 : Ideal R) (_ : 𝔪.IsMaximal),
      stabilizeUnit (R := Polynomial (Localization.AtPrime 𝔪)) (κ := Unit)
          (elementaryMatrixUnitMap (ι := Fin 2)
            (Polynomial.mapRingHom (algebraMap R (Localization.AtPrime 𝔪))) τ) ∈
        elementaryGroup (Fin 2 ⊕ Unit) (Polynomial (Localization.AtPrime 𝔪))) →
    stabilizeUnit (R := R[X]) (κ := Unit) τ ∈ elementaryGroup (Fin 2 ⊕ Unit) R[X]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_PatchStatement

/-- **Endpoint (target 3).**  Patching, together with the unconditional local theorem, gives
the global monic `SL₂`-block Statement. -/
theorem suslinMonicLocal_monicStatement_of_patch (hP : suslinMonic_PatchStatement) :
    suslinCongInd_MonicStatement := by
  intro R _ τ hdet hlc hconst
  exact hP R τ hdet hlc hconst fun 𝔪 _ ↦
    suslinMonicLocal_stab_map (algebraMap R (Localization.AtPrime 𝔪)) τ hdet hlc

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicLocal_monicStatement_of_patch

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
