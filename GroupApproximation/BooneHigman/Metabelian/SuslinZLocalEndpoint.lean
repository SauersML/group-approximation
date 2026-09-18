import GroupApproximation.BooneHigman.Metabelian.SuslinZLocalStab
import GroupApproximation.Meta.AxiomGuard

/-!
# The `ℤ[1/m]` stable-local residual, minus the transvection-witness cases

Lane `bh-met-93u`.  **`suslinZHalf_BadStatement` is NOT closed here.**  This module isolates
the residual `suslinZLocal_BadStatement` and proves three things.
* It implies the three endpoints: `SuslinBase3StabLocal` for `Chain.SIntPoly m k`
  (`suslinZLocal_stabLocal_sInt_of_bad`), `SuslinBase3GlobalStatement`
  (`suslinZLocal_global_of_bad`) and `SuslinR2IndBaseStatement` (`suslinZLocal_indBase_of_bad`).
* It follows from `suslinZHalf_BadStatement` (`suslinZLocal_bad_of_halfBad`).

**The residual.**  It is `suslinZHalf_BadStatement` with two changes.  The hypothesis
`¬ suslinZHalf_Witness σ` becomes the stronger `¬ suslinZLocal_Witness σ`.  There is also a new
per-`𝔪` hypothesis `¬ suslinZLocal_Witness σ_𝔪` over the LOCAL ring `A_𝔪`.  Witnesses now take
multipliers in `G = ⟨E₂, 1 + v wᵀ (wᵀ v = 0)⟩` (`suslinZLocal_Group`).  So the residual must
be proved only for pairs `(σ, 𝔪)` where
1. no automorphism `φ` of `A[X]` and no `ε, ε' ∈ G(A[X])` make `lc φ(ε σ ε')₀₀` a unit of `A`;
2. no automorphism of `A_𝔪[X]` and no `ε, ε' ∈ G(A_𝔪[X])` make `lc(...)₀₀` lie outside `𝔪 A_𝔪`.

This excludes every `σ ∈ G(A[X])`.  That includes every Cohn matrix `[[1 + ab, a²], [-b², 1 - ab]]`,
in particular the lane-93p counterexample `a = 2sX`, `b = 4X`.

**LOUD: logical strength.**  `suslinZLocal_halfBad_of_bad` proves the converse implication too,
through the endpoints.  So the two residuals are logically EQUIVALENT modulo proven reductions.
This is unavoidable for any residual that has an `_of_` reduction to a true target and is
implied by it.  The progress is in proof content: the set of `(σ, 𝔪)` still to treat is a
subset of the old one.  STRICTNESS of that inclusion is NOT proven.  It would need a `σ` that has
a transvection witness but no two-sided elementary witness.  Whether the 93p Cohn `σ` has a
two-sided elementary witness `ε σ ε'` is open.  The one-sided case is refuted in
`SuslinZHalfEndpoint`, and a random local two-sided search at `(2, s)` found none.

**LOUD: route (b) (split by residue characteristic) is vacuous.**  `A = ℤ[1/m][x₁,…,x_k]` is
a finitely generated `ℤ`-algebra, so every residue field `A/𝔪` is finite.  Hence
`𝔪 ∩ ℤ = pℤ` with `p ∤ m`.  No maximal ideal has residue characteristic `0`.

**Why local automorphisms add nothing (paper, not formalized).**  For a local domain `B`, every
element of `B` is a sum of two units, and `B[X]ˣ = Bˣ`.  So a ring automorphism of `B[X]` maps
`B` to `B`, and sends `X` to `uX + c` with `u ∈ Bˣ`.  This preserves degrees and whether the
leading coefficient is a unit.  Condition 2 therefore only uses the multipliers.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- **The residual.**  For `A = ℤ[1/m][x₁,…,x_k]` with `SL_N(A) = E_N(A)` for `N ≥ 3`, take any
`σ ∈ SL₂(A[X])` with `σ(0) = 1` and no transvection monic witness.  Then for every maximal
`𝔪` at which `σ_𝔪` has no transvection monic witness over `A_𝔪`, `diag(σ_𝔪, 1) ∈ E₃(A_𝔪[X])`. -/
def suslinZLocal_BadStatement : Prop :=
  ∀ (m k : ℕ), (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') →
    ∀ σ : Matrix.GeneralLinearGroup (Fin 2) (Polynomial (Chain.SIntPoly m k)),
      Matrix.det (σ : Matrix (Fin 2) (Fin 2) (Polynomial (Chain.SIntPoly m k))) = 1 →
      elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.constantCoeff (R := Chain.SIntPoly m k))
          σ = 1 →
      ¬ suslinZLocal_Witness σ →
      ∀ (𝔪 : Ideal (Chain.SIntPoly m k)) (_ : 𝔪.IsMaximal),
        ¬ suslinZLocal_Witness (elementaryMatrixUnitMap (ι := Fin 2)
            (Polynomial.mapRingHom (algebraMap (Chain.SIntPoly m k)
              (Localization.AtPrime 𝔪))) σ) →
        stabilizeUnit (R := Polynomial (Localization.AtPrime 𝔪)) (κ := Unit)
            (elementaryMatrixUnitMap (ι := Fin 2)
              (Polynomial.mapRingHom (algebraMap (Chain.SIntPoly m k)
                (Localization.AtPrime 𝔪))) σ) ∈
          elementaryGroup (Fin 2 ⊕ Unit) (Polynomial (Localization.AtPrime 𝔪))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZLocal_BadStatement

/-- **The target from the residual.**  Globally witnessed `σ` are handled by
`suslinZLocal_stab_of_globalWitness`.  Locally witnessed `σ_𝔪` are handled by
`suslinZLocal_stab_of_localWitness`.  The rest are handled by `hB`. -/
theorem suslinZLocal_stabLocal_sInt_of_bad (hB : suslinZLocal_BadStatement) (m k : ℕ)
    (hA : ∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') :
    SuslinBase3StabLocal (Chain.SIntPoly m k) 2 := by
  intro σ hdet h0 𝔪 h𝔪
  by_cases hW : suslinZLocal_Witness σ
  · rw [← suslinBase3_map_stabilize (κ := Unit)]
    exact elementaryGroup_map_le
      (Polynomial.mapRingHom (algebraMap (Chain.SIntPoly m k) (Localization.AtPrime 𝔪)))
      (Subgroup.mem_map_of_mem _
        (suslinZLocal_stab_of_globalWitness (hA 3 le_rfl) σ hdet hW))
  · by_cases hL : suslinZLocal_Witness (elementaryMatrixUnitMap (ι := Fin 2)
        (Polynomial.mapRingHom (algebraMap (Chain.SIntPoly m k) (Localization.AtPrime 𝔪))) σ)
    · exact suslinZLocal_stab_of_localWitness _ (suslinZLocal_det_map _ σ hdet) hL
    · exact hB m k hA σ hdet h0 hW 𝔪 h𝔪 hL

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZLocal_stabLocal_sInt_of_bad

/-- `SuslinBase3GlobalStatement` from the residual. -/
theorem suslinZLocal_global_of_bad (hB : suslinZLocal_BadStatement) :
    SuslinBase3GlobalStatement :=
  suslinMonicPatch_global (suslinZLocal_stabLocal_sInt_of_bad hB)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZLocal_global_of_bad

/-- `SuslinR2IndBaseStatement` from the residual. -/
theorem suslinZLocal_indBase_of_bad (hB : suslinZLocal_BadStatement) :
    SuslinR2IndBaseStatement :=
  suslinMonicPatch_indBase (suslinZLocal_stabLocal_sInt_of_bad hB)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZLocal_indBase_of_bad

/-- **Weakness certificate.**  The old residual implies the new one, because an elementary
witness is a transvection witness. -/
theorem suslinZLocal_bad_of_halfBad (hB : suslinZHalf_BadStatement) :
    suslinZLocal_BadStatement := by
  intro m k hA σ hdet h0 hW 𝔪 h𝔪 _
  exact hB m k hA σ hdet h0 (fun h ↦ hW (suslinZLocal_witness_of_halfWitness h)) 𝔪 h𝔪

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZLocal_bad_of_halfBad

/-- **LOUD: the converse.**  Through the endpoints, the new residual implies the old one.  So
the two are equivalent modulo proven reductions, and the progress is in proof content only. -/
theorem suslinZLocal_halfBad_of_bad (hB : suslinZLocal_BadStatement) :
    suslinZHalf_BadStatement := by
  intro m k hA σ hdet h0 _ 𝔪 h𝔪
  exact suslinZLocal_stabLocal_sInt_of_bad hB m k hA σ hdet h0 𝔪 h𝔪

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZLocal_halfBad_of_bad

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
