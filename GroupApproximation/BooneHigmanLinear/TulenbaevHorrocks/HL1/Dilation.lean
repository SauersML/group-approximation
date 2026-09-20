import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.HL1.DilFrame
import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.HL1.Statement
import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Reductions
import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.TulVdKElt

/-!
# Tulenbaev's Lemma 3.2: the dilation `St(R, 𝔄R) → St(B)` (k2-poly H.L1, step L1a)

`dil TX h5 : St(R, 𝔄R) →* St(B)` sends the generator `X_{v,w}` to `dgen TX (v, w)`, i.e.
`X_{T⁻ᵐ v, Tᵐ⁺ⁿ w}(T⁻ⁿ)` for large `m, n`. It is well defined by relations (1.1)–(1.3)
(`dgen_add`, `dgen_conj`, `dgen_frame`).

On generators over `B` and over `A[T]` (via `T ↦ T⁻¹`), the pair `(0, 0)` is valid, so the value is
`X_{v,w}(1)` (`dgen_map_subtype`, `dgen_map_neg`). With Tulenbaev's elements from van der Kallen's
(`TulElem.tulX`, `TulElem.tulX_X_one`), `X_{v,w}(1)` is van der Kallen's `X(v, w)`. That gives
`dilationAt : DilationAt A N hB hP` for a local ring `A`, `N ≥ 5`, and the elements
`VdK.elements` over `B` and `A[T]`: T Lemma 3.2 in the form `stHorrBInjAt_of_steps` uses.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

namespace GroupApproximation
namespace BooneHigmanLinear
namespace TulenbaevHorrocks
namespace HL1

open Matrix LaurentPolynomial
open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.PaninAffine (TulX AdmRow coordIdeal orthSub pMat)
open GroupApproximation.BooneHigmanLinear.K2Found
open GroupApproximation.BooneHigmanLinear.K2Found.RelPres (RMem IsEColumn RGen IsRel RelSt X can)
open GroupApproximation.BooneHigmanLinear.Tulenbaev (toLaurentNeg)

section Dil

variable {A : Type} [CommRing A] {𝔄 : Ideal A} {N : ℕ} (TX : TulX N)

/-- **Tulenbaev, Lemma 3.2.** The dilation `St(R, 𝔄R) →* St(B)`. -/
noncomputable def dil (h5 : 5 ≤ N) :
    RelSt (Fin N) (LaurentPolynomial A) (coeffIdeal 𝔄) →* SteinbergGroup (Fin N) (BB 𝔄) :=
  PresentedGroup.toGroup
    (f := fun g : RGen (Fin N) (LaurentPolynomial A) (coeffIdeal 𝔄) => dgen TX g.1 g.2) (by
    intro r hr
    change IsRel (coeffIdeal 𝔄) r at hr
    cases hr with
    | add v w w' h₁ h₂ h₃ =>
        simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
        rw [mul_inv_eq_one]
        exact dgen_add TX v w w' h₁ h₂ h₃
    | conj p q hp hq hc =>
        simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
        rw [mul_inv_eq_one]
        exact dgen_conj TX p q hp hq hc
    | frame v v' w u b hu hu' hw h₁ h₂ h₃ =>
        simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
        rw [mul_inv_eq_one]
        exact dgen_frame TX h5 v v' w u b hu hu' hw h₁ h₂ h₃)

theorem dil_X (h5 : 5 ≤ N) (p : (Fin N → LaurentPolynomial A) × (Fin N → LaurentPolynomial A))
    (hp : RMem (coeffIdeal 𝔄) p) : dil TX h5 (X p hp) = dgen TX p hp :=
  PresentedGroup.toGroup.of _

#audit_axioms dil_X

/-! ### The pair `(0, 0)` -/

theorem T_neg_zero : (T (-((0 : ℕ) : ℤ)) : LaurentPolynomial A) = 1 := by
  rw [Nat.cast_zero, neg_zero, T_zero]

theorem tB_zero : tB 𝔄 0 = 1 := by
  apply Subtype.ext
  exact T_neg_zero

theorem adm_of_unimod {B : Type} [CommRing B] {u v w : Fin N → B} (hu : u ⬝ᵥ v = 1)
    (hwv : w ⬝ᵥ v = 0) : AdmRow v w := by
  have e : w = ∑ k, v k • (u k • w) := by
    have h : ∑ k, v k • (u k • w) = (u ⬝ᵥ v) • w := by
      rw [dotProduct, Finset.sum_smul]
      exact Finset.sum_congr rfl fun k _ => by rw [smul_smul, mul_comm]
    rw [h, hu, one_smul]
  show w ∈ coordIdeal v • orthSub v
  rw [e]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem_smul (PaninAffine.mem_coordIdeal k) ?_
  show (u k • w) ⬝ᵥ v = 0
  rw [smul_dotProduct, hwv, smul_zero]

theorem one_mem_coordIdeal {B : Type} [CommRing B] {u v : Fin N → B} (hu : u ⬝ᵥ v = 1) :
    (1 : B) ∈ coordIdeal v := by
  rw [← hu]
  show ∑ i, u i * v i ∈ coordIdeal v
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- **Restriction to `B`.** On a generator over `B`, the dilation is `X_{v,w}(1)`. -/
theorem dgen_map_subtype (p : (Fin N → BB 𝔄) × (Fin N → BB 𝔄))
    (hp : RMem ((coeffIdeal 𝔄).comap (Graded.horrB 𝔄).subtype) p) :
    dgen TX (mapPair (Graded.horrB 𝔄).subtype p)
        (rmem_map (Graded.horrB 𝔄).subtype le_rfl hp) = TX.X p.1 p.2 1 := by
  have hp' := rmem_map (Graded.horrB 𝔄).subtype le_rfl hp
  have h0 : VB 𝔄 (mapPair (Graded.horrB 𝔄).subtype p).1 0 := fun i => by
    show T (-((0 : ℕ) : ℤ)) * ((p.1 i : BB 𝔄) : LaurentPolynomial A) ∈ Graded.horrB 𝔄
    rw [T_neg_zero, one_mul]
    exact (p.1 i).2
  have hvt : vt h0 = p.1 := by
    funext i
    apply Subtype.ext
    show T (-((0 : ℕ) : ℤ)) * ((p.1 i : BB 𝔄) : LaurentPolynomial A) = p.1 i
    rw [T_neg_zero, one_mul]
  have hWt : Wt hp'.2.1 (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)) = p.2 := by
    funext i
    apply Subtype.ext
    show T (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)) * ((p.2 i : BB 𝔄) : LaurentPolynomial A) = p.2 i
    rw [Nat.cast_zero, add_zero, T_zero, one_mul]
  obtain ⟨u, hu⟩ := hp.1.isUnimodular
  have ht : tB 𝔄 0 ∈ coordIdeal (vt h0) := by
    rw [tB_zero, hvt]
    exact one_mem_coordIdeal hu
  rw [dgen_eq TX hp' h0 ht]
  unfold val
  rw [hvt, hWt, tB_zero]

#audit_axioms dgen_map_subtype

theorem toLaurentNeg_mem (f : Polynomial A) : toLaurentNeg A f ∈ Graded.horrB 𝔄 := by
  have hT : (T (-1) : LaurentPolynomial A) ∈ Graded.horrB 𝔄 := by
    have h := T_neg_mem (A := A) (𝔄 := 𝔄) 1
    rwa [Nat.cast_one] at h
  refine Polynomial.induction_on f (fun a => ?_) (fun p q hp hq => ?_) (fun n a h => ?_)
  · have e := RingHom.congr_fun (toLaurentNeg_comp_C (A := A)) a
    rw [RingHom.comp_apply] at e
    rw [e]
    refine Graded.mem_horrB.2 fun n hn => ?_
    rw [← single_eq_C, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (by omega)]
    exact 𝔄.zero_mem
  · rw [map_add]
    exact add_mem hp hq
  · rw [pow_succ, ← mul_assoc, map_mul, toLaurentNeg_X]
    exact Subring.mul_mem _ h hT

/-- `A[T] → B`, `T ↦ T⁻¹`. -/
noncomputable def negB (𝔄 : Ideal A) : Polynomial A →+* BB 𝔄 :=
  (toLaurentNeg A).codRestrict (Graded.horrB 𝔄) toLaurentNeg_mem

theorem coe_negB (f : Polynomial A) : ((negB 𝔄 f : BB 𝔄) : LaurentPolynomial A) = toLaurentNeg A f :=
  rfl

/-- **Restriction to `A[T]`.** On a generator over `A[T]` (sent by `T ↦ T⁻¹`), the dilation is
the image of `X_{v,w}(1)` under `A[T] → B`. -/
theorem dgen_map_neg {𝔓 : Ideal (Polynomial A)} (h𝔓 : 𝔓 ≤ (coeffIdeal 𝔄).comap (toLaurentNeg A))
    (p : (Fin N → Polynomial A) × (Fin N → Polynomial A)) (hp : RMem 𝔓 p) :
    dgen TX (mapPair (toLaurentNeg A) p) (rmem_map (toLaurentNeg A) h𝔓 hp) =
      ringMap (negB 𝔄) (TX.X p.1 p.2 1) := by
  have hp' := rmem_map (toLaurentNeg A) h𝔓 hp
  obtain ⟨u, hu⟩ := hp.1.isUnimodular
  have h0 : VB 𝔄 (mapPair (toLaurentNeg A) p).1 0 := fun i => by
    show T (-((0 : ℕ) : ℤ)) * toLaurentNeg A (p.1 i) ∈ Graded.horrB 𝔄
    rw [T_neg_zero, one_mul]
    exact toLaurentNeg_mem _
  have hvt : vt h0 = negB 𝔄 ∘ p.1 := by
    funext i
    apply Subtype.ext
    show T (-((0 : ℕ) : ℤ)) * toLaurentNeg A (p.1 i) = toLaurentNeg A (p.1 i)
    rw [T_neg_zero, one_mul]
  have hWt : Wt hp'.2.1 (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)) = negB 𝔄 ∘ p.2 := by
    funext i
    apply Subtype.ext
    show T (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)) * toLaurentNeg A (p.2 i) = toLaurentNeg A (p.2 i)
    rw [Nat.cast_zero, add_zero, T_zero, one_mul]
  have hu' : (negB 𝔄 ∘ u) ⬝ᵥ (negB 𝔄 ∘ p.1) = 1 := by
    rw [← RingHom.map_dotProduct, hu, map_one]
  have ht : tB 𝔄 0 ∈ coordIdeal (vt h0) := by
    rw [tB_zero, hvt]
    exact one_mem_coordIdeal hu'
  rw [dgen_eq TX hp' h0 ht]
  unfold val
  rw [hvt, hWt, tB_zero, TX.nat (negB 𝔄) p.1 p.2 1 (adm_of_unimod hu hp.2.2)
    (one_mem_coordIdeal hu), map_one]

#audit_axioms dgen_map_neg

end Dil

/-! ### T Lemma 3.2 in the form of `DilationAt` -/

theorem card_ge_four {N : ℕ} (h5 : 5 ≤ N) : 4 ≤ Fintype.card (Fin N) := by
  rw [Fintype.card_fin]
  omega

/-- **Tulenbaev, Lemma 3.2**, for a local ring `A`, `N ≥ 5`, and van der Kallen's elements. -/
theorem dilationAt (A : Type) [CommRing A] [IsLocalRing A] {N : ℕ} (h5 : 5 ≤ N) :
    DilationAt A N (VdK.elements (Fin N) (horrBm A) (card_ge_four h5))
      (VdK.elements (Fin N) (Polynomial A) (card_ge_four h5)) := by
  refine ⟨dil (TulElem.tulX N h5) h5, ?_, ?_⟩
  · apply PresentedGroup.ext
    rintro ⟨⟨v, w⟩, hp⟩
    change dil (TulElem.tulX N h5) h5 (relMap (horrBm A).subtype (mB_le A) (X (v, w) hp)) =
      can _ (mB A) (X (v, w) hp)
    rw [relMap_X, dil_X, can_X, dgen_map_subtype, TulElem.tulX_X_one h5 hp.mem_U]
  · have hcomp : (dil (TulElem.tulX N h5) h5).comp (relMap (toLaurentNeg A) (mP_le A)) =
        (ringMap (negB (IsLocalRing.maximalIdeal A))).comp
          (can (VdK.elements (Fin N) (Polynomial A) (card_ge_four h5)) (mP A)) := by
      apply PresentedGroup.ext
      rintro ⟨⟨v, w⟩, hp⟩
      change dil (TulElem.tulX N h5) h5 (relMap (toLaurentNeg A) (mP_le A) (X (v, w) hp)) =
        ringMap (negB (IsLocalRing.maximalIdeal A)) (can _ (mP A) (X (v, w) hp))
      rw [relMap_X, dil_X, can_X, dgen_map_neg (TulElem.tulX N h5) (mP_le A) (v, w) hp,
        TulElem.tulX_X_one h5 hp.mem_U]
    intro γ hγ
    have h := DFunLike.congr_fun hcomp γ
    simp only [MonoidHom.comp_apply] at h
    rw [h, hγ, map_one]

#audit_axioms dilationAt

end HL1
end TulenbaevHorrocks
end BooneHigmanLinear
end GroupApproximation
