import GroupApproximation.Analysis.CStarProductCorona
import GroupApproximation.Analysis.CStarExactness

/-!
# Ucp lifts through a constant-coefficient product corona

Lane `TWWSchafhauser-3d1` (work order `WO-TWWSchafhauser-3d-1`).  Manuscript:
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378), through
C. Schafhauser, *A new proof of the Tikuisis--White--Winter theorem*, J. reine
angew. Math. **759** (2020), 291--304, §5.

The obstruction argument runs over the universal UHF algebra `Q`, so the norm
ultraproduct is the constant-coefficient product corona
`Q_l = ℓ^∞(ℕ, Q) / c_l(ℕ, Q)` (`PolarLiftingGeneralCStar.CStarProductCorona`).
Its last step reads as follows.  A unital `⋆`-homomorphism `ψ : A → Q_l` is
given, together with a ucp lift `L : A → ℓ^∞(ℕ, Q)` (Choi--Effros).  Then:

* the coordinates `φ_n = ev_n ∘ L : A → Q` are unital and completely positive;
* they are asymptotically multiplicative along `l`, because `ψ` is multiplicative;
* any bounded functional on `Q` sees the same limit on every representative of
  `ψ a`, so a trace formula proved for one representative holds for `φ_n`.

This file is coefficient-general (`B` is any nontrivial unital C⋆-algebra), and
it imports only the product-corona API and the completely-positive API.

## Main declarations

* `productCoordinate B n`: evaluation `ℓ^∞(ℕ, B) → B` as a `⋆`-homomorphism, and
  `isCompletelyPositive_productCoordinate`.
* `tendsto_norm_sub_of_quotient_eq`, `tendsto_functional_sub_of_quotient_eq`:
  two representatives of the same corona class agree along `l`.
* `ProductCoronaLift A B l`: a unital `⋆`-homomorphism into the corona with a ucp
  lift.
* `ProductCoronaLift.coordMap`, with `coordMap_one`,
  `completelyPositive_coordMap`, `tendsto_coordMap_mul` and
  `tendsto_trace_coordMap`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open Filter GroupApproximation.PolarLiftingGeneralCStar

noncomputable section

universe u v

section Coordinates

variable (B : Type u) [CStarAlgebra B]

/-- Evaluation at the `n`-th coordinate of the constant-coefficient bounded
product `ℓ^∞(ℕ, B)`, as a `⋆`-homomorphism. -/
def productCoordinate (n : ℕ) :
    BoundedCStarSequence (fun _ : ℕ ↦ B) →⋆ₙₐ[ℂ] B where
  toFun a := a n
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

@[simp] theorem productCoordinate_apply (n : ℕ)
    (a : BoundedCStarSequence (fun _ : ℕ ↦ B)) :
    productCoordinate B n a = a n :=
  rfl

/-- Coordinate evaluation is completely positive: it is a `⋆`-homomorphism. -/
theorem isCompletelyPositive_productCoordinate [Nontrivial B] (n : ℕ) :
    CStarExactness.IsCompletelyPositive
      (productCoordinate B n : BoundedCStarSequence (fun _ : ℕ ↦ B) →ₗ[ℂ] B) :=
  CStarExactness.isCompletelyPositive_of_starAlgHom (productCoordinate B n)

end Coordinates

section Representatives

variable {B : Type u} [CStarAlgebra B] [Nontrivial B] {l : Filter ℕ}

/-- Two bounded representatives of the same corona class are `l`-close. -/
theorem tendsto_norm_sub_of_quotient_eq
    {x y : BoundedCStarSequence (fun _ : ℕ ↦ B)}
    (h : cStarProductCoronaQuotient (fun _ : ℕ ↦ B) l x =
      cStarProductCoronaQuotient (fun _ : ℕ ↦ B) l y) :
    Tendsto (fun n ↦ ‖x n - y n‖) l (nhds 0) := by
  have h0 : cStarProductCoronaQuotient (fun _ : ℕ ↦ B) l (x - y) = 0 := by
    rw [_root_.map_sub, h, sub_self]
  exact (cStarProductCoronaQuotient_eq_zero_iff (fun _ : ℕ ↦ B) l (x - y)).mp h0

/-- A bounded linear functional takes `l`-asymptotically equal values on two
representatives of the same corona class. -/
theorem tendsto_functional_sub_of_quotient_eq (f : B →ₗ[ℂ] ℂ) (C : ℝ)
    (hf : ∀ b : B, ‖f b‖ ≤ C * ‖b‖)
    {x y : BoundedCStarSequence (fun _ : ℕ ↦ B)}
    (h : cStarProductCoronaQuotient (fun _ : ℕ ↦ B) l x =
      cStarProductCoronaQuotient (fun _ : ℕ ↦ B) l y) :
    Tendsto (fun n ↦ ‖f (x n) - f (y n)‖) l (nhds 0) := by
  have hC := (tendsto_norm_sub_of_quotient_eq h).const_mul C
  rw [mul_zero] at hC
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hC
  show ‖f (x n) - f (y n)‖ ≤ C * ‖x n - y n‖
  rw [← _root_.map_sub]
  exact hf (x n - y n)

end Representatives

/-- **A ucp lift into a constant-coefficient product corona** (Schafhauser,
Crelle 759 (2020), §5).  A unital `⋆`-homomorphism `ψ : A → B_l` together with a
unital completely positive lift `L : A → ℓ^∞(ℕ, B)` of `ψ`. -/
structure ProductCoronaLift (A : Type v) [CStarAlgebra A]
    (B : Type u) [CStarAlgebra B] [Nontrivial B] (l : Filter ℕ) where
  /-- The unital `⋆`-homomorphism `ψ : A → B_l`. -/
  hom : A →⋆ₐ[ℂ] CStarProductCorona (fun _ : ℕ ↦ B) l
  /-- The lift `L : A → ℓ^∞(ℕ, B)`. -/
  lift : A →ₗ[ℂ] BoundedCStarSequence (fun _ : ℕ ↦ B)
  /-- The lift is unital. -/
  lift_one : lift 1 = 1
  /-- The lift is completely positive. -/
  completelyPositive : CStarExactness.IsCompletelyPositive lift
  /-- The lift lifts `ψ`. -/
  mk_lift : ∀ a : A, cStarProductCoronaQuotient (fun _ : ℕ ↦ B) l (lift a) = hom a

namespace ProductCoronaLift

variable {A : Type v} [CStarAlgebra A] {B : Type u} [CStarAlgebra B] [Nontrivial B]
  {l : Filter ℕ} (L : ProductCoronaLift A B l)

/-- The coordinate maps `φ_n = ev_n ∘ L : A → B`. -/
def coordMap (n : ℕ) : A →ₗ[ℂ] B :=
  (productCoordinate B n : BoundedCStarSequence (fun _ : ℕ ↦ B) →ₗ[ℂ] B) ∘ₗ L.lift

@[simp] theorem coordMap_apply (n : ℕ) (a : A) : L.coordMap n a = L.lift a n :=
  rfl

/-- Each coordinate map is unital. -/
theorem coordMap_one (n : ℕ) : L.coordMap n 1 = 1 :=
  (congrArg (fun s : BoundedCStarSequence (fun _ : ℕ ↦ B) ↦ s n) L.lift_one).trans rfl

/-- Each coordinate map is completely positive. -/
theorem completelyPositive_coordMap (n : ℕ) :
    CStarExactness.IsCompletelyPositive (L.coordMap n) :=
  (isCompletelyPositive_productCoordinate B n).comp L.completelyPositive

/-- The coordinate maps are asymptotically multiplicative along `l`, because
the lifted map `ψ` is multiplicative. -/
theorem tendsto_coordMap_mul (a b : A) :
    Tendsto (fun n ↦ ‖L.coordMap n (a * b) - L.coordMap n a * L.coordMap n b‖)
      l (nhds 0) := by
  have h : cStarProductCoronaQuotient (fun _ : ℕ ↦ B) l (L.lift (a * b)) =
      cStarProductCoronaQuotient (fun _ : ℕ ↦ B) l (L.lift a * L.lift b) := by
    rw [L.mk_lift, _root_.map_mul (cStarProductCoronaQuotient (fun _ : ℕ ↦ B) l),
      L.mk_lift, L.mk_lift]
    exact _root_.map_mul L.hom a b
  exact tendsto_norm_sub_of_quotient_eq h

/-- **Trace transfer to the coordinate maps.**  Let `f` be a bounded functional
on `B` (the trace of `Q`) and `seq a` any representative of `ψ a` along which
`f` converges to `τ a`.  Then `f ∘ φ_n` converges to `τ` along `l`. -/
theorem tendsto_trace_coordMap (f : B →ₗ[ℂ] ℂ) (C : ℝ)
    (hf : ∀ b : B, ‖f b‖ ≤ C * ‖b‖) (τ : A → ℂ)
    (seq : A → BoundedCStarSequence (fun _ : ℕ ↦ B))
    (hseq : ∀ a : A, cStarProductCoronaQuotient (fun _ : ℕ ↦ B) l (seq a) = L.hom a)
    (htr : ∀ a : A, Tendsto (fun n ↦ ‖τ a - f (seq a n)‖) l (nhds 0)) (a : A) :
    Tendsto (fun n ↦ ‖τ a - f (L.coordMap n a)‖) l (nhds 0) := by
  have hq : cStarProductCoronaQuotient (fun _ : ℕ ↦ B) l (seq a) =
      cStarProductCoronaQuotient (fun _ : ℕ ↦ B) l (L.lift a) := by
    rw [hseq, L.mk_lift]
  have hsum := (htr a).add (tendsto_functional_sub_of_quotient_eq f C hf hq)
  rw [add_zero] at hsum
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hsum
  calc ‖τ a - f (L.coordMap n a)‖
      = ‖(τ a - f (seq a n)) + (f (seq a n) - f (L.lift a n))‖ := by
        rw [sub_add_sub_cancel, coordMap_apply]
    _ ≤ ‖τ a - f (seq a n)‖ + ‖f (seq a n) - f (L.lift a n)‖ := norm_add_le _ _

end ProductCoronaLift

end

end GroupApproximation.Full.TWWSchafhauser
