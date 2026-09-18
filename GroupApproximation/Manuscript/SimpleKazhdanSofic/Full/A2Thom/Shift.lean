import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2Endpoint.ThomGroup
import GroupApproximation.Algebra.FiniteResidual
import Mathlib.GroupTheory.Finiteness
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finite.Prod
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Thom's group is not Hopfian, hence not residually finite once finitely generated

`simple_kazhdan_sofic_group.tex`, Introduction, tex l.57–59 (table row A2):

> Thom constructed a finitely generated Kazhdan group that is locally embeddable into finite
> groups but not residually finite [...]

Thom (Groups Geom. Dyn. 4 (2010), §2.1) argues: "the shift `t ↦ t⁻¹`" (conjugation by
`diag(t,1,1,1,1)`) is a surjective endomorphism of `G = G_0(F_p[t,t⁻¹])/C` whose kernel "sits as
`F_p t⁻¹` in the upper right corner", so `G` is not Hopfian; by Mal'cev a finitely generated
residually finite group is Hopfian.

* `injective_of_surjective_of_isResiduallyFinite`: Mal'cev's theorem (proved here).
* `shiftMat u M = diag(u,1,1,1,1) · M · diag(u⁻¹,1,1,1,1)` and the endomorphism `shiftG0` of
  `G_0(R)`, a bijection.
* `thomShift K`: the induced endomorphism of `ThomGroup K`; surjective (`thomShift_surjective`),
  and not injective (`thomShift_not_injective`): the class of `e_15(t⁻¹)` is nontrivial and maps
  to the class of `e_15(1) ∈ C`.
* `not_isResiduallyFinite_thomGroup_of_fg`.
-/

namespace GroupApproximation.Full.A2Thom

open GroupApproximation.Full.A2Endpoint

section Malcev

/-- **Mal'cev**: in a finitely generated residually finite group every surjective endomorphism is
injective (Thom, §2.1, "a result of Mal'cev"). -/
theorem injective_of_surjective_of_isResiduallyFinite {G : Type*} [Group G] [Group.FG G]
    (hrf : IsResiduallyFinite G) (φ : G →* G) (hφ : Function.Surjective φ) :
    Function.Injective φ := by
  rw [injective_iff_map_eq_one]
  intro x hx
  by_contra hx1
  obtain ⟨L, hL, hxL⟩ := isResiduallyFinite_iff.1 hrf x hx1
  haveI := hL
  haveI : Finite (G ⧸ L.normalCore) := L.normalCore.finite_quotient_of_finiteIndex
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.1 ‹Group.FG G›
  haveI : Finite S := hSfin.to_subtype
  haveI : Finite (G →* G ⧸ L.normalCore) :=
    Finite.of_injective (fun ψ : G →* G ⧸ L.normalCore => fun s : S => ψ s) (by
      intro ψ₁ ψ₂ h
      refine MonoidHom.eq_of_eqOn_dense hS ?_
      intro s hs
      exact congrFun h ⟨s, hs⟩)
  have hinj : Function.Injective (fun ψ : G →* G ⧸ L.normalCore => ψ.comp φ) :=
    fun ψ₁ ψ₂ h => (MonoidHom.cancel_right hφ).1 h
  obtain ⟨ψ, hψ⟩ := Finite.injective_iff_surjective.1 hinj (QuotientGroup.mk' L.normalCore)
  have h1 : QuotientGroup.mk' L.normalCore x = 1 := by
    rw [← hψ]
    show ψ (φ x) = 1
    rw [hx, map_one]
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact hxL (L.normalCore_le h1)

end Malcev

section Shift

variable {R : Type*} [CommRing R]

/-- The diagonal entries `(u, 1, 1, 1, 1)`. -/
def shiftDiag (u : Rˣ) (i : Fin 5) : R :=
  if i = 0 then (u : R) else 1

theorem shiftDiag_zero (u : Rˣ) : shiftDiag u 0 = (u : R) :=
  if_pos rfl

theorem shiftDiag_of_ne (u : Rˣ) {i : Fin 5} (h : i ≠ 0) : shiftDiag u i = 1 :=
  if_neg h

theorem shiftDiag_mul_inv (u : Rˣ) (i : Fin 5) : shiftDiag u i * shiftDiag u⁻¹ i = 1 := by
  by_cases hi : i = 0
  · subst hi
    rw [shiftDiag_zero, shiftDiag_zero, Units.mul_inv]
  · rw [shiftDiag_of_ne u hi, shiftDiag_of_ne u⁻¹ hi, mul_one]

theorem diagonal_shiftDiag_mul_inv (u : Rˣ) :
    Matrix.diagonal (shiftDiag u) * Matrix.diagonal (shiftDiag u⁻¹) = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  exact congrArg Matrix.diagonal (funext (shiftDiag_mul_inv u))

/-- Conjugation by `diag(u,1,1,1,1)` (Thom, §2.1, the shift for `u = t`). -/
def shiftMat (u : Rˣ) (M : Matrix (Fin 5) (Fin 5) R) : Matrix (Fin 5) (Fin 5) R :=
  Matrix.diagonal (shiftDiag u) * M * Matrix.diagonal (shiftDiag u⁻¹)

theorem shiftMat_apply (u : Rˣ) (M : Matrix (Fin 5) (Fin 5) R) (k l : Fin 5) :
    shiftMat u M k l = shiftDiag u k * M k l * shiftDiag u⁻¹ l := by
  rw [shiftMat, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem shiftMat_one (u : Rˣ) : shiftMat u (1 : Matrix (Fin 5) (Fin 5) R) = 1 := by
  rw [shiftMat, mul_one, diagonal_shiftDiag_mul_inv]

theorem shiftMat_mul (u : Rˣ) (M N : Matrix (Fin 5) (Fin 5) R) :
    shiftMat u (M * N) = shiftMat u M * shiftMat u N := by
  have hDD : Matrix.diagonal (shiftDiag u⁻¹) * Matrix.diagonal (shiftDiag u) = 1 := by
    have h := diagonal_shiftDiag_mul_inv u⁻¹
    rwa [inv_inv] at h
  calc shiftMat u (M * N)
      = Matrix.diagonal (shiftDiag u) * M * 1 * N * Matrix.diagonal (shiftDiag u⁻¹) := by
        rw [mul_one, shiftMat, mul_assoc (Matrix.diagonal (shiftDiag u)) M N]
    _ = Matrix.diagonal (shiftDiag u) * M *
          (Matrix.diagonal (shiftDiag u⁻¹) * Matrix.diagonal (shiftDiag u)) * N *
          Matrix.diagonal (shiftDiag u⁻¹) := by rw [hDD]
    _ = shiftMat u M * shiftMat u N := by simp only [shiftMat, mul_assoc]

theorem shiftMat_shiftMat_inv (u : Rˣ) (M : Matrix (Fin 5) (Fin 5) R) :
    shiftMat u (shiftMat u⁻¹ M) = M := by
  calc shiftMat u (shiftMat u⁻¹ M)
      = Matrix.diagonal (shiftDiag u) * Matrix.diagonal (shiftDiag u⁻¹) * M *
          (Matrix.diagonal (shiftDiag u) * Matrix.diagonal (shiftDiag u⁻¹)) := by
        simp only [shiftMat, inv_inv, mul_assoc]
    _ = M := by rw [diagonal_shiftDiag_mul_inv, one_mul, mul_one]

theorem det_shiftMat (u : Rˣ) (M : Matrix (Fin 5) (Fin 5) R) : (shiftMat u M).det = M.det := by
  rw [shiftMat, Matrix.det_mul, Matrix.det_mul,
    mul_comm (Matrix.diagonal (shiftDiag u)).det M.det, mul_assoc, ← Matrix.det_mul,
    diagonal_shiftDiag_mul_inv, Matrix.det_one, mul_one]

theorem isThomShape_shiftMat (u : Rˣ) {M : Matrix (Fin 5) (Fin 5) R} (hM : IsThomShape M) :
    IsThomShape (shiftMat u M) := by
  constructor
  · intro i
    rw [shiftMat_apply, hM.col]
    by_cases hi : i = 0
    · subst hi
      rw [Matrix.one_apply_eq, mul_one, shiftDiag_mul_inv]
    · rw [Matrix.one_apply_ne hi, mul_zero, zero_mul]
  · intro j
    rw [shiftMat_apply, hM.row, shiftDiag_of_ne u (by decide : (4 : Fin 5) ≠ 0), one_mul]
    by_cases hj : j = 4
    · subst hj
      rw [Matrix.one_apply_eq, shiftDiag_of_ne u⁻¹ (by decide : (4 : Fin 5) ≠ 0), mul_one]
    · rw [Matrix.one_apply_ne (fun h => hj h.symm), zero_mul]

theorem transvection_zero_four_apply_of_not {k l : Fin 5} (h : ¬(k = 0 ∧ l = 4)) (c : R) :
    Matrix.transvection (0 : Fin 5) 4 c k l = (1 : Matrix (Fin 5) (Fin 5) R) k l := by
  rw [Matrix.transvection, Matrix.add_apply,
    Matrix.single_apply_of_ne (h := fun h' => h ⟨h'.1.symm, h'.2.symm⟩), add_zero]

/-- The shift multiplies the corner entry: `diag(u,1,1,1,1) e_15(c) diag(u⁻¹,1,1,1,1) =
e_15(uc)`. -/
theorem shiftMat_transvection (u : Rˣ) (c : R) :
    shiftMat u (Matrix.transvection (0 : Fin 5) 4 c) =
      Matrix.transvection (0 : Fin 5) 4 ((u : R) * c) := by
  ext k l
  rw [shiftMat_apply]
  by_cases hkl : k = 0 ∧ l = 4
  · obtain ⟨rfl, rfl⟩ := hkl
    rw [transvection_apply_self fin_zero_ne_four, transvection_apply_self fin_zero_ne_four,
      shiftDiag_zero, shiftDiag_of_ne u⁻¹ (by decide : (4 : Fin 5) ≠ 0), mul_one]
  · rw [transvection_zero_four_apply_of_not hkl, transvection_zero_four_apply_of_not hkl]
    by_cases hk : k = l
    · subst hk
      rw [Matrix.one_apply_eq, mul_one, shiftDiag_mul_inv]
    · rw [Matrix.one_apply_ne hk, mul_zero, zero_mul]

variable (R) in
/-- The shift endomorphism of `G_0(R)`: conjugation by `diag(u,1,1,1,1)`. -/
def shiftG0 (u : Rˣ) : thomG0 R →* thomG0 R where
  toFun g := ⟨⟨shiftMat u g.1.1, by rw [det_shiftMat]; exact g.1.2⟩,
    (mem_thomG0 R).2 (isThomShape_shiftMat u ((mem_thomG0 R).1 g.2))⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact shiftMat_one u
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    exact shiftMat_mul u g.1.1 h.1.1

variable (R) in
theorem shiftG0_shiftG0_inv (u : Rˣ) (g : thomG0 R) : shiftG0 R u (shiftG0 R u⁻¹ g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  exact shiftMat_shiftMat_inv u g.1.1

end Shift

section Quotient

variable (K : Type*) [CommRing K]

/-- The unit `t ∈ K[t,t⁻¹]`. -/
def laurentT : (LaurentPolynomial K)ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := by rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]
  inv_val := by rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]

theorem laurentT_val : ((laurentT K : (LaurentPolynomial K)ˣ) : LaurentPolynomial K) =
    LaurentPolynomial.T 1 :=
  rfl

/-- Thom's shift on `G_0(K[t,t⁻¹])`. -/
def thomShiftG0 : thomG0 (LaurentPolynomial K) →* thomG0 (LaurentPolynomial K) :=
  shiftG0 (LaurentPolynomial K) (laurentT K)

theorem thomShiftG0_central (a : LaurentPolynomial K) :
    thomShiftG0 K (thomCentral (LaurentPolynomial K) (Multiplicative.ofAdd a)) =
      thomCentral (LaurentPolynomial K) (Multiplicative.ofAdd (LaurentPolynomial.T 1 * a)) := by
  apply Subtype.ext
  apply Subtype.ext
  exact shiftMat_transvection (laurentT K) a

/-- The shift maps `C = e_15(K[t])` into itself. -/
theorem thomC_le_comap : thomC K ≤ (thomC K).comap (thomShiftG0 K) := by
  intro g hg
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hg
  rw [Subgroup.mem_comap]
  refine MonoidHom.mem_range.2 ⟨Multiplicative.ofAdd (Polynomial.X * Multiplicative.toAdd x), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change Matrix.transvection (0 : Fin 5) 4
      (Polynomial.toLaurent (Polynomial.X * Multiplicative.toAdd x)) =
    shiftMat (laurentT K)
      (Matrix.transvection (0 : Fin 5) 4 (Polynomial.toLaurent (Multiplicative.toAdd x)))
  rw [shiftMat_transvection, laurentT_val, map_mul, Polynomial.toLaurent_X]

/-- Thom's shift endomorphism of `G = G_0(K[t,t⁻¹])/C` (Thom, §2.1). -/
def thomShift : ThomGroup K →* ThomGroup K :=
  QuotientGroup.map (thomC K) (thomC K) (thomShiftG0 K) (thomC_le_comap K)

/-- Thom, §2.1: the shift is surjective (it is induced by a bijection of `G_0`). -/
theorem thomShift_surjective : Function.Surjective (thomShift K) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (thomC K) q
  exact ⟨QuotientGroup.mk' (thomC K) (shiftG0 (LaurentPolynomial K) (laurentT K)⁻¹ g),
    congrArg (QuotientGroup.mk' (thomC K))
      (shiftG0_shiftG0_inv (LaurentPolynomial K) (laurentT K) g)⟩

/-- `e_15(t⁻¹) ∉ C`. -/
theorem thomCentral_T_neg_one_not_mem [Nontrivial K] :
    thomCentral (LaurentPolynomial K) (Multiplicative.ofAdd (LaurentPolynomial.T (-1))) ∉
      thomC K := by
  intro hmem
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.1 hmem
  have h04 : Polynomial.toLaurent (Multiplicative.toAdd p) =
      (LaurentPolynomial.T (-1) : LaurentPolynomial K) := by
    have h := congrArg (fun g : thomG0 (LaurentPolynomial K) => g.1.1 0 4) hp
    change Matrix.transvection (0 : Fin 5) 4 (Polynomial.toLaurent (Multiplicative.toAdd p)) 0 4 =
      Matrix.transvection (0 : Fin 5) 4 (LaurentPolynomial.T (-1) : LaurentPolynomial K) 0 4 at h
    rwa [transvection_apply_self fin_zero_ne_four, transvection_apply_self fin_zero_ne_four] at h
  have hXq : (Polynomial.X : Polynomial K) * Multiplicative.toAdd p = 1 := by
    apply Polynomial.toLaurent_injective
    rw [map_mul, Polynomial.toLaurent_X, h04, ← LaurentPolynomial.T_add, add_neg_cancel,
      LaurentPolynomial.T_zero, Polynomial.toLaurent_one]
  exact Polynomial.not_isUnit_X (R := K)
    ⟨⟨Polynomial.X, Multiplicative.toAdd p, hXq, (mul_comm _ _).trans hXq⟩, rfl⟩

/-- Thom, §2.1: the class of `e_15(t⁻¹)` lies in the kernel of the shift. -/
theorem thomShift_T_neg_one :
    thomShift K (QuotientGroup.mk' (thomC K)
      (thomCentral (LaurentPolynomial K) (Multiplicative.ofAdd (LaurentPolynomial.T (-1))))) =
      1 := by
  change QuotientGroup.mk' (thomC K) (thomShiftG0 K
      (thomCentral (LaurentPolynomial K) (Multiplicative.ofAdd (LaurentPolynomial.T (-1))))) = 1
  rw [thomShiftG0_central, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine MonoidHom.mem_range.2 ⟨Multiplicative.ofAdd (1 : Polynomial K), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change Matrix.transvection (0 : Fin 5) 4 (Polynomial.toLaurent (1 : Polynomial K)) =
    Matrix.transvection (0 : Fin 5) 4
      (LaurentPolynomial.T 1 * LaurentPolynomial.T (-1) : LaurentPolynomial K)
  rw [Polynomial.toLaurent_one, ← LaurentPolynomial.T_add, add_neg_cancel,
    LaurentPolynomial.T_zero]

/-- Thom, §2.1: the shift is not injective, so `ThomGroup K` is not Hopfian. -/
theorem thomShift_not_injective [Nontrivial K] : ¬ Function.Injective (thomShift K) := by
  intro hinj
  have h := (injective_iff_map_eq_one (thomShift K)).1 hinj _ (thomShift_T_neg_one K)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  exact thomCentral_T_neg_one_not_mem K h

/-- **tex l.58–59** ("not residually finite"), modulo finite generation: a finitely generated
`ThomGroup K` is not residually finite (Thom, §2.1: non-Hopfian plus Mal'cev). -/
theorem not_isResiduallyFinite_thomGroup_of_fg [Nontrivial K] (hfg : Group.FG (ThomGroup K)) :
    ¬ IsResiduallyFinite (ThomGroup K) := fun hrf =>
  thomShift_not_injective K
    (injective_of_surjective_of_isResiduallyFinite hrf (thomShift K) (thomShift_surjective K))

end Quotient

#audit_axioms GroupApproximation.Full.A2Thom.injective_of_surjective_of_isResiduallyFinite
#audit_axioms GroupApproximation.Full.A2Thom.not_isResiduallyFinite_thomGroup_of_fg

end GroupApproximation.Full.A2Thom
