import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.HL1.DilVal
import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.RelPres

/-!
# Tulenbaev's dilation on generators: relations (1.1) and (1.2) (T Lemma 3.2)

For a generator `X_{v,w}` of `St(R, 𝔄R)` (`RMem (coeffIdeal 𝔄) (v, w)`), `dgen TX (v, w)` is the
common value `X_{T⁻ᵐ v, Tᵐ⁺ⁿ w}(T⁻ⁿ)` over the valid pairs `(m, n)` (`dgen_eq`).

* `dgen_add` (relation (1.1)): `dgen (v, w) dgen (v, w') = dgen (v, w + w')`, from `TulX.rowAdd`.
* `dgen_conj` (relation (1.2)): `dgen p dgen q (dgen p)⁻¹ = dgen (conjPair p q)`, from
  `TulX.conj` and `TulX.proj`. The conjugated column and row are `T⁻ᵐ` and `Tᵐ⁺ⁿ` times those
  of `conjPair p q`, because `T⁻ⁿ¹ Tᵐ¹⁺ⁿ¹ T⁻ᵐ¹ = 1`.
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
open GroupApproximation.BooneHigmanLinear.K2Found.RelPres (RMem IsEColumn)
open GroupApproximation.BooneHigmanLinear.K2Found.VdK (conjPair)

variable {A : Type} [CommRing A] {𝔄 : Ideal A} {N : ℕ} (TX : TulX N)

/-! ### Matrix identities -/

theorem one_add_smul_vecMulVec_mulVec {B : Type*} [CommRing B] (s : B) (a b x : Fin N → B) :
    (1 + s • vecMulVec a b) *ᵥ x = x + (s * (b ⬝ᵥ x)) • a := by
  rw [add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul]

theorem vecMul_one_add_smul_vecMulVec {B : Type*} [CommRing B] (s : B) (a b x : Fin N → B) :
    x ᵥ* (1 + s • vecMulVec a b) = x + (s * (x ⬝ᵥ a)) • b := by
  rw [vecMul_add, vecMul_one, vecMul_smul, vecMul_vecMulVec, smul_smul]

theorem coordIdeal_mulVec_le {B : Type*} [CommRing B] (M : Matrix (Fin N) (Fin N) B)
    (x : Fin N → B) : coordIdeal (M *ᵥ x) ≤ coordIdeal x := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  show ∑ j, M i j * x j ∈ coordIdeal x
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

theorem coordIdeal_le_mulVec {B : Type*} [CommRing B] {M M' : Matrix (Fin N) (Fin N) B}
    (h : M' * M = 1) (x : Fin N → B) : coordIdeal x ≤ coordIdeal (M *ᵥ x) := by
  have e : x = M' *ᵥ (M *ᵥ x) := by rw [mulVec_mulVec, h, one_mulVec]
  conv_lhs => rw [e]
  exact coordIdeal_mulVec_le M' _

/-! ### The generator values -/

/-- The value of the dilation on the generator `X_{v,w}`. -/
noncomputable def dgen (p : (Fin N → LaurentPolynomial A) × (Fin N → LaurentPolynomial A))
    (hp : RMem (coeffIdeal 𝔄) p) : SteinbergGroup (Fin N) (BB 𝔄) :=
  gval TX 𝔄 hp.1.isUnimodular.choose_spec hp.2.1

theorem dgen_eq {p : (Fin N → LaurentPolynomial A) × (Fin N → LaurentPolynomial A)}
    (hp : RMem (coeffIdeal 𝔄) p) {m : ℕ} (hm : VB 𝔄 p.1 m) {n : ℕ}
    (ht : tB 𝔄 n ∈ coordIdeal (vt hm)) : dgen TX p hp = val TX hp.2.1 hm n :=
  gval_eq TX hp.1.isUnimodular.choose_spec hp.2.2 hp.2.1 hm ht

theorem exists_valid_of_rmem {p : (Fin N → LaurentPolynomial A) × (Fin N → LaurentPolynomial A)}
    (hp : RMem (coeffIdeal 𝔄) p) :
    ∃ (m : ℕ) (hm : VB 𝔄 p.1 m) (n : ℕ), tB 𝔄 n ∈ coordIdeal (vt hm) :=
  exists_valid 𝔄 hp.1.isUnimodular.choose_spec

theorem adm_of_rmem {p : (Fin N → LaurentPolynomial A) × (Fin N → LaurentPolynomial A)}
    (hp : RMem (coeffIdeal 𝔄) p) {m : ℕ} (hm : VB 𝔄 p.1 m) (k : ℤ) :
    AdmRow (vt hm) (Wt hp.2.1 k) :=
  adm_Wt hp.1.isUnimodular.choose_spec hp.2.2 hp.2.1 hm k

/-! ### Relation (1.1) -/

theorem Wt_add {w w' : Fin N → LaurentPolynomial A} (hw : ∀ i, w i ∈ coeffIdeal 𝔄)
    (hw' : ∀ i, w' i ∈ coeffIdeal 𝔄) (hww : ∀ i, (w + w') i ∈ coeffIdeal 𝔄) (k : ℤ) :
    Wt hw k + Wt hw' k = Wt hww k := by
  funext i
  apply Subtype.ext
  show T k * w i + T k * w' i = T k * (w i + w' i)
  rw [mul_add]

/-- **Relation (1.1).** -/
theorem dgen_add (v w w' : Fin N → LaurentPolynomial A) (h₁ : RMem (coeffIdeal 𝔄) (v, w))
    (h₂ : RMem (coeffIdeal 𝔄) (v, w')) (h₃ : RMem (coeffIdeal 𝔄) (v, w + w')) :
    dgen TX (v, w) h₁ * dgen TX (v, w') h₂ = dgen TX (v, w + w') h₃ := by
  obtain ⟨m, hm, n, ht⟩ := exists_valid_of_rmem h₁
  have hm' : VB 𝔄 v m := hm
  rw [dgen_eq TX h₁ hm' ht, dgen_eq TX h₂ hm' ht, dgen_eq TX h₃ hm' ht]
  unfold val
  rw [TX.rowAdd _ _ _ _ (adm_of_rmem h₁ hm' _) (adm_of_rmem h₂ hm' _) ht,
    Wt_add h₁.2.1 h₂.2.1 h₃.2.1]

#audit_axioms dgen_add

/-! ### Relation (1.2) -/

theorem T_three (m n : ℕ) :
    (T (-(n : ℤ)) : LaurentPolynomial A) * T ((m : ℤ) + n) * T (-(m : ℤ)) = 1 := by
  rw [← T_add, ← T_add, show -(n : ℤ) + ((m : ℤ) + n) + -(m : ℤ) = 0 by ring, T_zero]

/-- The conjugated column: `T⁻ᵐ²` times the column of `conjPair p q`. -/
theorem coe_conj_col (p q : (Fin N → LaurentPolynomial A) × (Fin N → LaurentPolynomial A))
    (hp : RMem (coeffIdeal 𝔄) p) {m₁ m₂ : ℕ} (hm₁ : VB 𝔄 p.1 m₁) (hm₂ : VB 𝔄 q.1 m₂) (n₁ : ℕ)
    (i : Fin N) :
    (((vt hm₂ + (tB 𝔄 n₁ * (Wt hp.2.1 ((m₁ : ℤ) + n₁) ⬝ᵥ vt hm₂)) • vt hm₁) i : BB 𝔄) :
      LaurentPolynomial A) = T (-(m₂ : ℤ)) * (conjPair p q).1 i := by
  have hdot : ((Wt hp.2.1 ((m₁ : ℤ) + n₁) ⬝ᵥ vt hm₂ : BB 𝔄) : LaurentPolynomial A) =
      T ((m₁ : ℤ) + n₁) * T (-(m₂ : ℤ)) * (p.2 ⬝ᵥ q.1) := by
    rw [coe_dotProduct]
    show ∑ k, T ((m₁ : ℤ) + n₁) * p.2 k * (T (-(m₂ : ℤ)) * q.1 k) = _
    rw [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h3 := T_three (A := A) m₁ n₁
  show (vt hm₂ i : LaurentPolynomial A) +
      (tB 𝔄 n₁ : LaurentPolynomial A) * ((Wt hp.2.1 ((m₁ : ℤ) + n₁) ⬝ᵥ vt hm₂ : BB 𝔄) :
        LaurentPolynomial A) * (vt hm₁ i : LaurentPolynomial A) =
    T (-(m₂ : ℤ)) * (q.1 i + (p.2 ⬝ᵥ q.1) * p.1 i)
  rw [hdot]
  show T (-(m₂ : ℤ)) * q.1 i + T (-(n₁ : ℤ)) * (T ((m₁ : ℤ) + n₁) * T (-(m₂ : ℤ)) * (p.2 ⬝ᵥ q.1)) *
      (T (-(m₁ : ℤ)) * p.1 i) = T (-(m₂ : ℤ)) * (q.1 i + (p.2 ⬝ᵥ q.1) * p.1 i)
  linear_combination (T (-(m₂ : ℤ)) * (p.2 ⬝ᵥ q.1) * p.1 i) * h3

/-- The conjugated row: `Tᵐ²⁺ⁿ²` times the row of `conjPair p q`. -/
theorem coe_conj_row (p q : (Fin N → LaurentPolynomial A) × (Fin N → LaurentPolynomial A))
    (hp : RMem (coeffIdeal 𝔄) p) (hq : RMem (coeffIdeal 𝔄) q) {m₁ : ℕ} (hm₁ : VB 𝔄 p.1 m₁)
    (n₁ : ℕ) (k₂ : ℤ) (i : Fin N) :
    (((Wt hq.2.1 k₂ + (-tB 𝔄 n₁ * (Wt hq.2.1 k₂ ⬝ᵥ vt hm₁)) • Wt hp.2.1 ((m₁ : ℤ) + n₁)) i :
      BB 𝔄) : LaurentPolynomial A) = T k₂ * (conjPair p q).2 i := by
  have hdot : ((Wt hq.2.1 k₂ ⬝ᵥ vt hm₁ : BB 𝔄) : LaurentPolynomial A) =
      T k₂ * T (-(m₁ : ℤ)) * (q.2 ⬝ᵥ p.1) := by
    rw [coe_dotProduct]
    show ∑ k, T k₂ * q.2 k * (T (-(m₁ : ℤ)) * p.1 k) = _
    rw [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h3 := T_three (A := A) m₁ n₁
  show (Wt hq.2.1 k₂ i : LaurentPolynomial A) +
      -(tB 𝔄 n₁ : LaurentPolynomial A) * ((Wt hq.2.1 k₂ ⬝ᵥ vt hm₁ : BB 𝔄) : LaurentPolynomial A) *
        (Wt hp.2.1 ((m₁ : ℤ) + n₁) i : LaurentPolynomial A) =
    T k₂ * (q.2 i - (q.2 ⬝ᵥ p.1) * p.2 i)
  rw [hdot]
  show T k₂ * q.2 i + -T (-(n₁ : ℤ)) * (T k₂ * T (-(m₁ : ℤ)) * (q.2 ⬝ᵥ p.1)) *
      (T ((m₁ : ℤ) + n₁) * p.2 i) = T k₂ * (q.2 i - (q.2 ⬝ᵥ p.1) * p.2 i)
  linear_combination (-(T k₂ * (q.2 ⬝ᵥ p.1) * p.2 i)) * h3

/-- **Relation (1.2).** -/
theorem dgen_conj (p q : (Fin N → LaurentPolynomial A) × (Fin N → LaurentPolynomial A))
    (hp : RMem (coeffIdeal 𝔄) p) (hq : RMem (coeffIdeal 𝔄) q)
    (hc : RMem (coeffIdeal 𝔄) (conjPair p q)) :
    dgen TX p hp * dgen TX q hq * (dgen TX p hp)⁻¹ = dgen TX (conjPair p q) hc := by
  obtain ⟨m₁, hm₁, n₁, ht₁⟩ := exists_valid_of_rmem hp
  obtain ⟨m₂, hm₂, n₂, ht₂⟩ := exists_valid_of_rmem hq
  have hadm₁ := adm_of_rmem hp hm₁ ((m₁ : ℤ) + n₁)
  have hadm₂ := adm_of_rmem hq hm₂ ((m₂ : ℤ) + n₂)
  set γ := TX.X (vt hm₁) (Wt hp.2.1 ((m₁ : ℤ) + n₁)) (tB 𝔄 n₁) with hγ
  have hproj : pMat γ = 1 + tB 𝔄 n₁ • vecMulVec (vt hm₁) (Wt hp.2.1 ((m₁ : ℤ) + n₁)) :=
    TX.proj _ _ _ hadm₁ ht₁
  have hproj' : pMat γ⁻¹ = 1 + (-tB 𝔄 n₁) • vecMulVec (vt hm₁) (Wt hp.2.1 ((m₁ : ℤ) + n₁)) :=
    TX.pMat_X_inv _ _ _ hadm₁ ht₁
  have hconj := TX.conj _ _ _ hadm₂ ht₂ γ
  rw [hproj, hproj', one_add_smul_vecMulVec_mulVec, vecMul_one_add_smul_vecMulVec] at hconj
  have hmc : VB 𝔄 (conjPair p q).1 m₂ := fun i => by
    rw [← coe_conj_col p q hp hm₁ hm₂ n₁ i]
    exact Subtype.property _
  have hcol : vt hmc = vt hm₂ + (tB 𝔄 n₁ * (Wt hp.2.1 ((m₁ : ℤ) + n₁) ⬝ᵥ vt hm₂)) • vt hm₁ := by
    funext i
    apply Subtype.ext
    exact (coe_conj_col p q hp hm₁ hm₂ n₁ i).symm
  have hrow : Wt hc.2.1 ((m₂ : ℤ) + n₂) = Wt hq.2.1 ((m₂ : ℤ) + n₂) +
      (-tB 𝔄 n₁ * (Wt hq.2.1 ((m₂ : ℤ) + n₂) ⬝ᵥ vt hm₁)) • Wt hp.2.1 ((m₁ : ℤ) + n₁) := by
    funext i
    apply Subtype.ext
    exact (coe_conj_row p q hp hq hm₁ n₁ ((m₂ : ℤ) + n₂) i).symm
  have htc : tB 𝔄 n₂ ∈ coordIdeal (vt hmc) := by
    have hle := coordIdeal_le_mulVec (PaninAffine.pMat_inv_mul γ) (vt hm₂)
    rw [hproj, one_add_smul_vecMulVec_mulVec, ← hcol] at hle
    exact hle ht₂
  rw [dgen_eq TX hp hm₁ ht₁, dgen_eq TX hq hm₂ ht₂, dgen_eq TX hc hmc htc]
  unfold val
  rw [← hγ, hconj, hcol, hrow]

#audit_axioms dgen_conj

end HL1
end TulenbaevHorrocks
end BooneHigmanLinear
end GroupApproximation
