import GroupApproximation.BooneHigman.Metabelian.SuslinBase3CongEndpoint
import Mathlib.Algebra.MvPolynomial.Equiv
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-3 base of R2 from `SL₃ = E₃` over a coefficient ring: the lifting lemmas

Lane `bh-met-91p`.  Target: `SuslinBase3CongGlobalStatement` / `SuslinBase3CoreGlobalStatement`
(`SuslinBase3CongEndpoint.lean`, `SuslinBase3CoreEndpoint.lean`) for the two families
`A = Chain.CharPPoly p k` (`k ≥ 1`) and `A = Chain.SIntPoly m k`, under the family hypothesis
`∀ N' ≥ 3, SL_{N'}(A) = E_{N'}(A)`.

**Proved here (every commutative ring).**
* `suslinBase3Fam_stab_mem`: if `SL_{n+1}(B) = E_{n+1}(B)` and `det τ = 1`, `τ ∈ GL_n(B)`, then
  `diag(τ, 1) ∈ E_{n+1}(B)` (reindex `Fin n ⊕ Unit ≃ Fin (n + 1)`).
* `suslinBase3Fam_stab_map_mem`: the same after any ring map `f : B → S`.
* `suslinBase3Fam_stabLocal_of_slPoly`, `suslinBase3Fam_powStab_of_slPoly`: if
  `SL₃(A[X]) = E₃(A[X])` then `SuslinBase3StabLocal A 2` (hence the cores): `diag(σ, 1)` lies in
  `SL₃(A[X]) = E₃(A[X])` and maps into `E₃(A_𝔪[X])`.

**The strengthened-hypothesis variant (LOUD: CIRCULAR, not a closure).**
`SuslinBase3FamSuccGlobalStatement` is `SuslinBase3GlobalStatement` with the family hypothesis
moved from `k` to `k + 1` (`SL_{N'}(Chain _ (k + 1)) = E_{N'}`, and `Chain _ (k + 1) ≅ A[X]`).
It is PROVED here outright (`suslinBase3Fam_succGlobal`), but the consumer can NOT discharge its
hypothesis.  The only consumer is the Suslin chain
`SuslinBase3GlobalStatement → SuslinR2IndBaseStatement → SuslinLocalHorrocksStatement →
SuslinPatchingStatement → SuslinOneVariableStatement → PolynomialSuslinStatement`, whose last
arrow (`polynomialSuslin_of_oneVariable`) is an induction on `k`: the family hypothesis at `k` is
the INDUCTION HYPOTHESIS, and `SL_N((Chain _ k)[X]) = E_N`, i.e. `SL = E` at `k + 1`, is exactly the
CONCLUSION of the step being proved.  Feeding it back is circular.  The formal witness is
`suslinBase3Fam_global_of_polynomialSuslin : PolynomialSuslinStatement →
SuslinBase3GlobalStatement`: this route derives the base from the end product of the chain that
the base feeds.  The genuine (non-circular) use of the family hypothesis AT LEVEL `k` is in
`SuslinBase3FamGen.lean`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- **`diag(τ, 1)` is elementary** when `SL_{n+1}(B) = E_{n+1}(B)` and `det τ = 1`. -/
theorem suslinBase3Fam_stab_mem {B : Type*} [CommRing B] {n : ℕ}
    (hSL : SpecialLinearInElementary B (n + 1)) (τ : (Matrix (Fin n) (Fin n) B)ˣ)
    (hdet : Matrix.det (τ : Matrix (Fin n) (Fin n) B) = 1) :
    stabilizeUnit (R := B) (κ := Unit) τ ∈ elementaryGroup (Fin n ⊕ Unit) B := by
  obtain ⟨e⟩ : Nonempty (Fin n ⊕ Unit ≃ Fin (n + 1)) :=
    ⟨((finSuccEquiv' (0 : Fin (n + 1))).trans (Equiv.optionEquivSumPUnit (Fin n))).symm⟩
  have hdT : Matrix.det ((elementaryReindexUnitEquiv (R := B) e
      (stabilizeUnit (R := B) (κ := Unit) τ) : (Matrix (Fin (n + 1)) (Fin (n + 1)) B)ˣ) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) B) = 1 := by
    change Matrix.det ((Matrix.reindexRingEquiv B e)
      (Matrix.fromBlocks (τ : Matrix (Fin n) (Fin n) B) 0 0 1)) = 1
    rw [Matrix.coe_reindexRingEquiv, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_one, mul_one]
    exact hdet
  have hmem := hSL _ hdT
  rw [← elementaryReindexGroup_map (R := B) e, Subgroup.mem_map] at hmem
  obtain ⟨x, hx, hxe⟩ := hmem
  have hxe' : elementaryReindexUnitEquiv (R := B) e x =
      elementaryReindexUnitEquiv (R := B) e (stabilizeUnit (R := B) (κ := Unit) τ) := hxe
  rwa [(elementaryReindexUnitEquiv (R := B) e).injective hxe'] at hx

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Fam_stab_mem

/-- **`diag(f τ, 1)` is elementary** over `S`, for any ring map `f : B → S`, when
`SL_{n+1}(B) = E_{n+1}(B)` and `det τ = 1`. -/
theorem suslinBase3Fam_stab_map_mem {B S : Type*} [CommRing B] [CommRing S] {n : ℕ}
    (hSL : SpecialLinearInElementary B (n + 1)) (f : B →+* S)
    (τ : (Matrix (Fin n) (Fin n) B)ˣ) (hdet : Matrix.det (τ : Matrix (Fin n) (Fin n) B) = 1) :
    stabilizeUnit (R := S) (κ := Unit) (elementaryMatrixUnitMap f τ) ∈
      elementaryGroup (Fin n ⊕ Unit) S := by
  rw [← suslinBase3_map_stabilize (κ := Unit) f τ]
  exact elementaryGroup_map_le f
    (Subgroup.mem_map_of_mem _ (suslinBase3Fam_stab_mem hSL τ hdet))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Fam_stab_map_mem

/-- Entrywise coefficient maps compose. -/
theorem suslinBase3Fam_map_comp {R S T ι : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Fintype ι] [DecidableEq ι] (f : S →+* T) (g : R →+* S) (u : (Matrix ι ι R)ˣ) :
    elementaryMatrixUnitMap f (elementaryMatrixUnitMap g u) =
      elementaryMatrixUnitMap (f.comp g) u := by
  apply Units.ext
  ext i j
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Fam_map_comp

/-- **`SL₃(A[X]) = E₃(A[X])` gives the stabilized normalized residual** at rank `2`, for every
commutative ring `A` (normalization at `X = 0` is not even used). -/
theorem suslinBase3Fam_stabLocal_of_slPoly {A : Type*} [CommRing A]
    (h : SpecialLinearInElementary A[X] 3) : SuslinBase3StabLocal A 2 :=
  fun σ hdet _ 𝔪 _ ↦ suslinBase3Fam_stab_map_mem (n := 2) h
    (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) σ hdet

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Fam_stabLocal_of_slPoly

/-- `SL₃(A[X]) = E₃(A[X])` gives the deep-congruence core (with `N = 0`). -/
theorem suslinBase3Fam_powStab_of_slPoly {A : Type*} [CommRing A]
    (h : SpecialLinearInElementary A[X] 3) : SuslinBase3CongPowStab A 2 :=
  fun 𝔪 _ ↦ ⟨0, fun σ hdet _ _ ↦ suslinBase3Fam_stab_map_mem (n := 2) h
    (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) σ hdet⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Fam_powStab_of_slPoly
