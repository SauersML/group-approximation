import GroupApproximation.BooneHigman.Metabelian.SuslinMonicLocalCaseB
import Mathlib.Algebra.Polynomial.Eval.Degree
import GroupApproximation.Meta.AxiomGuard

/-!
# The monic `SL₂`-block Statement over a LOCAL ring (unconditional)

Lane `bh-met-93i`.  Main result: `suslinMonicLocal_monicStab R : suslinCongInd_MonicStab R`
for EVERY commutative LOCAL ring `R` (`[IsLocalRing R]`), with no further hypothesis; in fact
the constant-term hypothesis of `suslinCongInd_MonicStab` is not used.  Stronger form
(`suslinMonicLocal_good`): every `τ ∈ SL₂(R[X])` whose `(0,0)` entry has a unit leading
coefficient has `diag(τ, 1) ∈ E₃(R[X])`.

**Route** (induction on `n ≥ deg f`, `f = τ₀₀`, `F = lc(f)⁻¹ f` monic):
* `deg f = 0`: `f` is a unit constant; unit pivot.
* `deg f = n + 1`: a column move replaces `g = τ₀₁` by `g mod F`.  The constant terms of
  `f τ₁₁ - (g mod F) τ₁₀ = 1` give `f(0) k(0) + (g mod F)(0) (-c(0)) = 1`; by locality one
  summand is a unit: case A (`(g mod F)(0) ∈ Rˣ`, `SuslinMonicLocalCaseA.lean`) or case B
  (`f(0) ∈ Rˣ`, `SuslinMonicLocalCaseB.lean`).  Both use the induction hypothesis only in
  degree `≤ n`, plus the Mennicke product rule of lane `bh-met-92r`.

`suslinMonicLocal_stab_map`: the same conclusion after base change to any local ring (used
for the patching reduction in `SuslinMonicLocalPatch.lean`).
Truth check: scratch `bh-met-93i/check.py` replays this exact route (every matrix, determinant,
equation and unit claim) on 900 random `τ` over `ZMod 4`, `ZMod 9`, `𝔽₂[ε]/(ε²)`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- **The induction step** in degree `n + 1`, over a local ring. -/
theorem suslinMonicLocal_step {R : Type*} [CommRing R] [IsLocalRing R] {n : ℕ}
    (hIH : ∀ f g : R[X], IsUnit f.leadingCoeff → f.natDegree ≤ n → suslinMonicLocal_Good f g)
    {f g : R[X]} (hlc : IsUnit f.leadingCoeff) (hd : f.natDegree = n + 1) :
    suslinMonicLocal_Good f g := by
  obtain ⟨v, hv⟩ := hlc
  obtain ⟨F, hF⟩ : ∃ F : R[X], F = C ((v⁻¹ : Rˣ) : R) * f := ⟨_, rfl⟩
  have hFm : F.Monic := by
    rw [hF]
    exact monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [← hv, Units.inv_mul])
  have hFdeg : F.natDegree = f.natDegree := by
    rw [hF]
    exact natDegree_C_mul_of_isUnit (Units.isUnit _) f
  have hF1 : F ≠ 1 := by
    intro h
    rw [h, natDegree_one] at hFdeg
    omega
  have hmd := modByMonic_add_div g F
  refine suslinMonicLocal_good_of_col_right (g' := g %ₘ F) (-(C ((v⁻¹ : Rˣ) : R) * (g /ₘ F)))
    ?_ (by linear_combination hmd - (g /ₘ F) * hF)
  intro τ hdet h0 h1
  obtain ⟨c, hc⟩ : ∃ c : R[X], (τ : Matrix (Fin 2) (Fin 2) R[X]) 1 0 = c := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : R[X], (τ : Matrix (Fin 2) (Fin 2) R[X]) 1 1 = k := ⟨_, rfl⟩
  have hrel : f * k - g %ₘ F * c = 1 := by
    have h := hdet
    rw [Matrix.det_fin_two, h0, h1, hc, hk] at h
    exact h
  have hc0 : f.coeff 0 * k.coeff 0 + (g %ₘ F).coeff 0 * (-c.coeff 0) = 1 := by
    have h : (f * k - g %ₘ F * c).coeff 0 = (1 : R[X]).coeff 0 := by rw [hrel]
    rw [coeff_sub, mul_coeff_zero, mul_coeff_zero, coeff_one_zero] at h
    linear_combination h
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hc0 with hu | hu
  · exact suslinMonicLocal_caseB hIH ⟨v, hv⟩ hd (isUnit_of_mul_isUnit_left hu) hrel
      τ hdet h0 h1
  · exact suslinMonicLocal_caseA hIH ⟨v, hv⟩ hd
      (by rw [← hFdeg]; exact natDegree_modByMonic_lt g hFm hF1)
      (isUnit_of_mul_isUnit_left hu) τ hdet h0 h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicLocal_step

/-- **Local monic theorem, strong form.**  Over a local ring, every first row `(f, g)` with
`lc f ∈ Rˣ` is good: every `τ ∈ SL₂(R[X])` with first row `(f, g)` is stably elementary. -/
theorem suslinMonicLocal_good {R : Type*} [CommRing R] [IsLocalRing R] (n : ℕ) :
    ∀ f g : R[X], IsUnit f.leadingCoeff → f.natDegree ≤ n → suslinMonicLocal_Good f g := by
  induction n with
  | zero =>
    intro f g hlc hle
    have hf := eq_C_of_natDegree_le_zero hle
    rw [Polynomial.leadingCoeff, Nat.le_zero.mp hle] at hlc
    rw [hf]
    exact suslinMonicLocal_good_of_isUnit g (hlc.map C)
  | succ n ih =>
    intro f g hlc hle
    rcases Nat.lt_or_ge f.natDegree (n + 1) with h | h
    · exact ih f g hlc (by omega)
    · exact suslinMonicLocal_step ih hlc (by omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicLocal_good

/-- **Endpoint (target 1).**  The monic `SL₂`-block Statement holds over every commutative
LOCAL ring, unconditionally. -/
theorem suslinMonicLocal_monicStab (R : Type*) [CommRing R] [IsLocalRing R] :
    suslinCongInd_MonicStab R := by
  intro τ hdet hlc _
  exact suslinMonicLocal_good _ _ _ hlc le_rfl τ hdet rfl rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicLocal_monicStab

/-- **Base change to a local ring.**  If `τ ∈ SL₂(R[X])` has `lc τ₀₀ ∈ Rˣ` and `φ : R → S` with
`S` local, the image of `τ` in `SL₂(S[X])` is stably elementary. -/
theorem suslinMonicLocal_stab_map {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing S]
    (φ : R →+* S) (τ : (Matrix (Fin 2) (Fin 2) R[X])ˣ)
    (hdet : Matrix.det (τ : Matrix (Fin 2) (Fin 2) R[X]) = 1)
    (hlc : IsUnit ((τ : Matrix (Fin 2) (Fin 2) R[X]) 0 0).leadingCoeff) :
    stabilizeUnit (R := S[X]) (κ := Unit)
        (elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.mapRingHom φ) τ) ∈
      elementaryGroup (Fin 2 ⊕ Unit) S[X] := by
  have hval : ((elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.mapRingHom φ) τ :
      (Matrix (Fin 2) (Fin 2) S[X])ˣ) : Matrix (Fin 2) (Fin 2) S[X]) =
      (Polynomial.mapRingHom φ).mapMatrix (τ : Matrix (Fin 2) (Fin 2) R[X]) := rfl
  have h00 : ((elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.mapRingHom φ) τ :
      (Matrix (Fin 2) (Fin 2) S[X])ˣ) : Matrix (Fin 2) (Fin 2) S[X]) 0 0 =
      ((τ : Matrix (Fin 2) (Fin 2) R[X]) 0 0).map φ := rfl
  have hdet' : Matrix.det ((elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.mapRingHom φ) τ :
      (Matrix (Fin 2) (Fin 2) S[X])ˣ) : Matrix (Fin 2) (Fin 2) S[X]) = 1 := by
    rw [hval, ← RingHom.map_det, hdet, map_one]
  have hlc' : IsUnit (((τ : Matrix (Fin 2) (Fin 2) R[X]) 0 0).map φ).leadingCoeff := by
    rw [leadingCoeff_map_of_leadingCoeff_ne_zero φ (hlc.map φ).ne_zero]
    exact hlc.map φ
  exact suslinMonicLocal_good _ (((τ : Matrix (Fin 2) (Fin 2) R[X]) 0 0).map φ) _ hlc' le_rfl
    _ hdet' h00 rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicLocal_stab_map

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
