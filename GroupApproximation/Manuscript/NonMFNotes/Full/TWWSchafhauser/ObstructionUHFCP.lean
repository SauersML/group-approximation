import GroupApproximation.Analysis.QuasidiagonalTrace
import GroupApproximation.Analysis.CStarCompletelyPositiveForm

/-!
# Form-positive after completely positive is form-positive

Lane `TWWSch3d5b` (work order `WO-TWWSchafhauser-3d-5`, part (b)).  Manuscript:
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378), through
C. Schafhauser, *A new proof of the Tikuisis--White--Winter theorem*, J. reine
angew. Math. **759** (2020), 291--304, §4.

In Schafhauser's compression step a unital completely positive map `φ : S → Q`
into the universal UHF algebra is composed with the conditional expectation
`E_m : Q → M_{m!}`.  The two maps are completely positive in two different
vocabularies:

* `φ` in the factorization sense `CStarExactness.IsCompletelyPositive`
  (positive matrices over `S` go to matrices `star P * P` over `Q`), which is
  the sense in which Choi--Effros lifts are produced;
* `E_m` in the form sense `Quasidiagonal.IsCompletelyPositiveOnMatrices`, the
  sense `Quasidiagonal.IsLocallyQuasidiagonalTrace` asks for.

`isCompletelyPositiveOnMatrices_comp_isCompletelyPositive` shows the composite is
completely positive in the form sense.  The proof is the column trick: the matrix
`(a i⋆ a j)ᵢⱼ` is `star N * N` (`CStarExactness.star_col_mul_col`), so
`φ (a i⋆ a j) = ∑ₖ (P k i)⋆ (P k j)`, and the form of `E ∘ φ` at the tuple `a` is
the sum over `k` of the forms of `E` at the tuples `P k ·`.  Each summand is real
and nonnegative by hypothesis.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.Quasidiagonal

noncomputable section

universe u v

/-- Moving the innermost of five finite sums to the outside. -/
theorem sum_five_comm_innermost {α β γ δ ε M : Type*} [AddCommMonoid M]
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype ε]
    (f : α → β → γ → δ → ε → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e = ∑ e, ∑ a, ∑ b, ∑ c, ∑ d, f a b c d e := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e
      = ∑ a, ∑ b, ∑ c, ∑ e, ∑ d, f a b c d e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ e, ∑ c, ∑ d, f a b c d e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_comm
    _ = ∑ a, ∑ e, ∑ b, ∑ c, ∑ d, f a b c d e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ e, ∑ a, ∑ b, ∑ c, ∑ d, f a b c d e := Finset.sum_comm

/-- **A form-positive map after a completely positive map is form-positive.**

`E : B → M_Y` completely positive in the form sense and `φ : A → B` completely
positive in the factorization sense give `E ∘ φ` completely positive in the form
sense.  In the application `B` is the universal UHF algebra `Q`, `E` is the
conditional expectation onto `M_{m!}` and `φ` is a ucp model `S → Q`
(Schafhauser, Crelle 759 (2020), §4). -/
theorem isCompletelyPositiveOnMatrices_comp_isCompletelyPositive
    {A : Type u} [CStarAlgebra A] {B : Type v} [CStarAlgebra B] {Y : FiniteModel}
    {E : B →ₗ[ℂ] Matrix Y Y ℂ} (hE : IsCompletelyPositiveOnMatrices Y ⇑E)
    {φ : A →ₗ[ℂ] B} (hφ : CStarExactness.IsCompletelyPositive φ) :
    IsCompletelyPositiveOnMatrices Y ⇑(E ∘ₗ φ) := by
  intro m a w
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    constructor <;> simp
  · haveI : NeZero m := ⟨hm.ne'⟩
    obtain ⟨N, hN⟩ := CStarExactness.star_col_mul_col a
    obtain ⟨P, hP⟩ := hφ m
      (CStarMatrix.ofMatrix (Matrix.of fun i j => star (a i) * a j)) ⟨N, hN⟩
    -- the image of the column matrix is `star P * P`, entry by entry
    have hφa : ∀ i j : Fin m,
        φ (star (a i) * a j) = ∑ k : Fin m, star (P k i) * P k j := by
      intro i j
      calc φ (star (a i) * a j) = (star P * P) i j := congrArg (fun M => M i j) hP
        _ = ∑ k : Fin m, (star P) i k * P k j :=
          CStarExactness.cstarMatrix_mul_apply (star P) P i j
        _ = ∑ k : Fin m, star (P k i) * P k j :=
          Finset.sum_congr rfl fun k _ =>
            congrArg (fun z : B => z * P k j) (CStarExactness.cstarMatrix_star_apply P i k)
    -- each summand of the form splits as a sum over `k`
    have hentry : ∀ (i j : Fin m) (x y : Y),
        (starRingEnd ℂ) (w i x) * (E ∘ₗ φ) (star (a i) * a j) x y * w j y
          = ∑ k : Fin m,
            (starRingEnd ℂ) (w i x) * E (star (P k i) * P k j) x y * w j y := by
      intro i j x y
      rw [LinearMap.comp_apply, hφa i j, map_sum, Matrix.sum_apply, Finset.mul_sum,
        Finset.sum_mul]
    have hS : (∑ i : Fin m, ∑ j : Fin m, ∑ x : Y, ∑ y : Y,
          (starRingEnd ℂ) (w i x) * (E ∘ₗ φ) (star (a i) * a j) x y * w j y)
        = ∑ k : Fin m, ∑ i : Fin m, ∑ j : Fin m, ∑ x : Y, ∑ y : Y,
          (starRingEnd ℂ) (w i x) * E (star (P k i) * P k j) x y * w j y := by
      calc (∑ i : Fin m, ∑ j : Fin m, ∑ x : Y, ∑ y : Y,
            (starRingEnd ℂ) (w i x) * (E ∘ₗ φ) (star (a i) * a j) x y * w j y)
          = ∑ i : Fin m, ∑ j : Fin m, ∑ x : Y, ∑ y : Y, ∑ k : Fin m,
            (starRingEnd ℂ) (w i x) * E (star (P k i) * P k j) x y * w j y :=
            Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
              Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
                hentry i j x y
        _ = ∑ k : Fin m, ∑ i : Fin m, ∑ j : Fin m, ∑ x : Y, ∑ y : Y,
            (starRingEnd ℂ) (w i x) * E (star (P k i) * P k j) x y * w j y :=
            sum_five_comm_innermost fun (i j : Fin m) (x y : Y) (k : Fin m) =>
              (starRingEnd ℂ) (w i x) * E (star (P k i) * P k j) x y * w j y
    constructor
    · rw [hS, Complex.im_sum]
      exact Finset.sum_eq_zero fun k _ => (hE m (fun i => P k i) w).1
    · rw [hS, Complex.re_sum]
      exact Finset.sum_nonneg fun k _ => (hE m (fun i => P k i) w).2

end

end GroupApproximation.Full.TWWSchafhauser
