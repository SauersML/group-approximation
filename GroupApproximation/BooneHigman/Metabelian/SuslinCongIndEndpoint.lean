import GroupApproximation.BooneHigman.Metabelian.SuslinCongIndNagata
import GroupApproximation.BooneHigman.Metabelian.SuslinR1FinNagata
import GroupApproximation.BooneHigman.Metabelian.SuslinBase3CongEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# The characteristic-`p` half of the rank-3 base from the monic `SL₂`-block Statement

Lane `bh-met-93c`.  Endpoints, for `A = Chain.CharPPoly p k = (ZMod p)[s_0,…,s_{k-1}]`:
* `suslinCongInd_stab_mem_charP`: `diag(σ, 1) ∈ E₃(A[X])` for EVERY `σ ∈ SL₂(A[X])` (global,
  no normalization, no localization), from `suslinCongInd_MonicStatement` and `SL₃(A) = E₃(A)`;
* `suslinCongInd_stabLocal_charP`: `SuslinBase3StabLocal A 2`;
* `suslinCongInd_powStab_charP`: `SuslinBase3CongPowStab A 2` (the lane target);
* `suslinCongInd_global_of_monic`: `SuslinBase3GlobalStatement`, from the monic Statement and the
  `ℤ[1/m]` half `hZ` (kept as an explicit, separate hypothesis; see below);
* `suslinCongInd_indBase_of_monic`: `SuslinR2IndBaseStatement`, likewise.

The family hypothesis is used ONLY at level `k` and only at rank `3` (`SL₃(A) = E₃(A)`, for
the constant term `diag(ρ(0), 1)`); nothing at level `k + 1` is assumed, so this is not the
circular `SL = E at k + 1` route of `SuslinBase3FamLift`.  The route uses neither regularity of
`A_𝔪` nor `NK₁`.  The input `1 ≤ k` of the family Statement is not needed.

**The `ℤ[1/m]` half is NOT covered.**  Nagata over `ℤ[1/m][s]` only produces a leading
coefficient `c ∈ ℤ[1/m] \ {0}`, which is not a unit in general, so the monic Statement does not
apply; `hZ` is literally the second conjunct of `SuslinBase3GlobalStatement` (LOUD).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- **Global stable elementarity of `SL₂(A[X])`** for `A = (ZMod p)[s_0,…,s_{k-1}]`, from the
monic `SL₂`-block Statement and `SL₃(A) = E₃(A)`. -/
theorem suslinCongInd_stab_mem_charP (hM : suslinCongInd_MonicStatement) (p : ℕ) [Fact p.Prime]
    (k : ℕ) (hA : SpecialLinearInElementary (Chain.CharPPoly p k) 3)
    (σ : (Matrix (Fin 2) (Fin 2) (Chain.CharPPoly p k)[X])ˣ)
    (hdet : Matrix.det (σ : Matrix (Fin 2) (Fin 2) (Chain.CharPPoly p k)[X]) = 1) :
    stabilizeUnit (R := (Chain.CharPPoly p k)[X]) (κ := Unit) σ ∈
      elementaryGroup (Fin 2 ⊕ Unit) (Chain.CharPPoly p k)[X] :=
  suslinCongInd_stab_mem_of_nagata (A := MvPolynomial (Fin k) (ZMod p))
    (fun g hg ↦ suslinR1Fin_nagata (k := ZMod p) g hg) hA (hM _) σ hdet

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongInd_stab_mem_charP

/-- **`SuslinBase3StabLocal` in characteristic `p`** from the monic Statement and the family
hypothesis at level `k`. -/
theorem suslinCongInd_stabLocal_charP (hM : suslinCongInd_MonicStatement) (p : ℕ) [Fact p.Prime]
    (k : ℕ) (hA : ∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.CharPPoly p k) N') :
    SuslinBase3StabLocal (Chain.CharPPoly p k) 2 :=
  suslinCongInd_stabLocal_of_global (suslinCongInd_stab_mem_charP hM p k (hA 3 le_rfl))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongInd_stabLocal_charP

/-- **The lane target in characteristic `p`**: `SuslinBase3CongPowStab (Chain.CharPPoly p k) 2`
from the monic Statement and the family hypothesis at level `k`. -/
theorem suslinCongInd_powStab_charP (hM : suslinCongInd_MonicStatement) (p : ℕ) [Fact p.Prime]
    (k : ℕ) (hA : ∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.CharPPoly p k) N') :
    SuslinBase3CongPowStab (Chain.CharPPoly p k) 2 :=
  suslinBase3Cong_powStab_of_core
    (suslinBase3Core_core_of_stabLocal (suslinCongInd_stabLocal_charP hM p k hA))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongInd_powStab_charP

/-- **The family residual** from the monic Statement and the `ℤ[1/m]` half `hZ` (LOUD: `hZ` is
the second conjunct of `SuslinBase3GlobalStatement` verbatim; only the first is discharged). -/
theorem suslinCongInd_global_of_monic (hM : suslinCongInd_MonicStatement)
    (hZ : ∀ (m k : ℕ),
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') →
        SuslinBase3StabLocal (Chain.SIntPoly m k) 2) :
    SuslinBase3GlobalStatement :=
  ⟨fun p _ k _ hA ↦ suslinCongInd_stabLocal_charP hM p k hA, hZ⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongInd_global_of_monic

/-- The rank-3 base of R2 from the monic Statement and the `ℤ[1/m]` half. -/
theorem suslinCongInd_indBase_of_monic (hM : suslinCongInd_MonicStatement)
    (hZ : ∀ (m k : ℕ),
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') →
        SuslinBase3StabLocal (Chain.SIntPoly m k) 2) :
    SuslinR2IndBaseStatement :=
  suslinBase3_indBase_of_global (suslinCongInd_global_of_monic hM hZ)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongInd_indBase_of_monic

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
