import GroupApproximation.Analysis.ShulmanFillDiagonalHom
import GroupApproximation.Analysis.ShulmanFillNormingAsymptotic
import GroupApproximation.Analysis.ShulmanFillNormingDoubledData

/-!
# The doubling bridge: one asymptotic lift, doubled

`Analysis/ShulmanFillNormingDoubledData` builds the doubled data
`ι' n = hBlockOp ∘ (entrywise ι n) : M₂(A n) → B(H ⊕ H)` out of a model
`(ι, hnorm, hone)` on `H`, together with the contractivity and unit clauses
`doubled_norm_le` and `doubled_hone`.  This module carries an asymptotic lift
across that construction.

Given `φ : StarStrongAsymptoticLift ι hnorm hone π`, the doubled family is

    `Φ_t b = (n ↦ diag (φ_t b n, φ_t b n))` ,

a sequence in the bounded product of the doubled models, and
`StarStrongAsymptoticLift.double` is the full structure instance at
`(doubledIota ι, doubled_norm_le ι, doubled_hone ι hone)` lifting
`doubledRep π : b ↦ hBlockOp (diag (π b, π b))`.

## How each clause is discharged

The diagonal `x ↦ diag(x, x)` is `ShulmanFill.diagonalHom2`, a unital
`*`-homomorphism, and `doubledDiagSeqHom` is the induced `*`-homomorphism of
the bounded products.  So the four defect clauses and the unitality clause are
all one inequality: the doubled defect *is* the doubled sequence of the
original defect, and `norm_doubledDiagSeq_le` bounds it.  Nothing is estimated.

Only the membership and the lifting clause have geometric content, and both are
the same computation.  Entrywise, `diag(x, x)` has `ι n (x n)` on the diagonal
and `0` off it, so `tendsto_hBlockOp_of_coord` turns the `*`-strong convergence
of `n ↦ ι n (x n)` into the `*`-strong convergence of the doubled sequence, with
limit `hBlockOp (diag(T, T))`; that is `isStarStrongLimit_doubledDiagSeq`.  With
`T = π b`, supplied by `φ.lift`, the limit is `doubledRep π b` on the nose, so
the lifting clause stays exact.

## What this does *not* supply

`Analysis/ShulmanFillNormingExistentialLiftFlip` records the consequence: the
flip is a unitary of the doubled `𝒟`, but it *commutes* with every doubled
diagonal, so conjugating `double φ` by it returns `double φ` unchanged.  The
second leg of Shulman's Theorem 10 is therefore not obtained from a single lift
this way.

## Section layout

The positivity order of the coefficients enters only where a norm on the
doubled models is named, and nontriviality only where their unit is; the
sections below are nested so that every declaration uses the instances it
carries, which is what `Analysis/ShulmanFillNormingDoubledFlip` does for the
same reason.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

/-! ## The diagonal at one coefficient algebra -/

section DiagonalCoefficients

variable {E : Type} [CStarAlgebra E]

/-- **The diagonal embedding is contractive.**  It is a `*`-homomorphism of
C-star algebras, and those are contractive; no block-norm computation is
needed.  This is the argument of `ShulmanFill.doubled_norm_le` again. -/
theorem norm_diagonalHom2_le (a : E) :
    ‖(diagonalHom2 a : CStarMatrix (Fin 2) (Fin 2) E)‖ ≤ ‖a‖ :=
  NonUnitalStarAlgHom.norm_apply_le
    (diagonalHom2 :
      E →⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) E).toNonUnitalStarAlgHom a

/-- The diagonal entries of `diag(a, a)`. -/
theorem diagonalHom2_entry_self (a : E) (i : Fin 2) :
    (diagonalHom2 a : CStarMatrix (Fin 2) (Fin 2) E) i i = a := by
  show (cStarDiagonal2 a a : CStarMatrix (Fin 2) (Fin 2) E) i i = a
  fin_cases i
  · exact cStarDiagonal2_apply_zero_zero a a
  · exact cStarDiagonal2_apply_one_one a a

/-- The off-diagonal entries of `diag(a, a)`. -/
theorem diagonalHom2_entry_ne (a : E) {i j : Fin 2} (hij : i ≠ j) :
    (diagonalHom2 a : CStarMatrix (Fin 2) (Fin 2) E) i j = 0 := by
  show (cStarDiagonal2 a a : CStarMatrix (Fin 2) (Fin 2) E) i j = 0
  fin_cases i
  · fin_cases j
    · exact absurd rfl hij
    · exact cStarDiagonal2_apply_zero_one a a
  · fin_cases j
    · exact cStarDiagonal2_apply_one_zero a a
    · exact absurd rfl hij

end DiagonalCoefficients

/-! ## The doubled representation -/

section DoubledRepresentation

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]

/-- **The doubled representation** `b ↦ diag(π b, π b)`, read as one operator on
`H ⊕ H`. -/
def doubledRep {B : Type} [CStarAlgebra B] (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    B →⋆ₐ[ℂ] (BlockSpace H 2 →L[ℂ] BlockSpace H 2) :=
  (hBlockOpHom (E := H) (n := 2)).comp (diagonalHom2.comp π)

@[simp] theorem doubledRep_apply {B : Type} [CStarAlgebra B]
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (b : B) :
    doubledRep π b = hBlockOp (diagonalHom2 (π b)) := rfl

end DoubledRepresentation

/-! ## The entries of a doubled sequence -/

section DoubledEntries

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {A : ℕ → Type} [∀ n, CStarAlgebra (A n)]
variable (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))

/-- **The entries of the doubled sequence converge.**  On the diagonal the
entry is `ι n (xₙ)`, off it the entry is `0`; this is the entrywise input that
`tendsto_hBlockOp_of_coord` asks for. -/
theorem tendsto_diagonalHom2_entry (x : StarStrong.BoundedStarSequence A)
    {T : H →L[ℂ] H}
    (hT : ∀ v : H, Tendsto (fun n ↦ ι n (x n) v) atTop (𝓝 (T v)))
    (i j : Fin 2) (v : H) :
    Tendsto (fun n ↦ ((CStarMatrix.mapₙₐ (ι n))
        (diagonalHom2 (x n) : CStarMatrix (Fin 2) (Fin 2) (A n)) i j) v) atTop
      (𝓝 (((diagonalHom2 T : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)) i j)
        v)) := by
  by_cases hij : i = j
  · subst hij
    have hL : (fun n ↦ ((CStarMatrix.mapₙₐ (ι n))
          (diagonalHom2 (x n) : CStarMatrix (Fin 2) (Fin 2) (A n)) i i) v)
        = fun n ↦ ι n (x n) v := by
      funext n
      have hentry :
          (diagonalHom2 (x n) : CStarMatrix (Fin 2) (Fin 2) (A n)) i i = x n :=
        diagonalHom2_entry_self (x n) i
      rw [mapₙₐ_entry, hentry]
    have hR :
        ((diagonalHom2 T : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)) i i) v
          = T v := by
      rw [diagonalHom2_entry_self T i]
    rw [hL, hR]
    exact hT v
  · have hL : (fun n ↦ ((CStarMatrix.mapₙₐ (ι n))
          (diagonalHom2 (x n) : CStarMatrix (Fin 2) (Fin 2) (A n)) i j) v)
        = fun _ : ℕ ↦ (0 : H) := by
      funext n
      have hentry :
          (diagonalHom2 (x n) : CStarMatrix (Fin 2) (Fin 2) (A n)) i j = 0 :=
        diagonalHom2_entry_ne (x n) hij
      rw [mapₙₐ_entry, hentry, map_zero, _root_.zero_apply]
    have hR :
        ((diagonalHom2 T : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)) i j) v
          = 0 := by
      rw [diagonalHom2_entry_ne T hij, _root_.zero_apply]
    rw [hL, hR]
    exact tendsto_const_nhds

end DoubledEntries

/-! ## The doubled sequence -/

section DoubledSequence

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {A : ℕ → Type} [∀ n, CStarAlgebra (A n)]
-- The positivity order of the coefficients is what makes the doubled models
-- C-star algebras; `Analysis/ShulmanFillNormingDoubledData` carries it the same
-- way, and a consumer discharges it with `CStarAlgebra.spectralOrder` and
-- `CStarAlgebra.spectralOrderedRing`.
variable [∀ n, PartialOrder (A n)] [∀ n, StarOrderedRing (A n)]
variable (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))

/-- **The doubled sequence** `n ↦ diag(xₙ, xₙ)`, in the bounded product of the
doubled models. -/
def doubledDiagSeq (x : StarStrong.BoundedStarSequence A) :
    StarStrong.BoundedStarSequence (fun n ↦ DoubledModel A n) :=
  ⟨fun n ↦ diagonalHom2 (x n), memℓp_infty ⟨‖x‖, by
    rintro _ ⟨n, rfl⟩
    exact (norm_diagonalHom2_le (x n)).trans
      (lp.norm_apply_le_norm ENNReal.top_ne_zero x n)⟩⟩

@[simp] theorem doubledDiagSeq_apply (x : StarStrong.BoundedStarSequence A)
    (n : ℕ) : (doubledDiagSeq (A := A) x) n = diagonalHom2 (x n) := rfl

/-- **The doubled sequence map, as a `*`-homomorphism of the bounded
products.**  Every clause is the corresponding clause of `diagonalHom2` read
coordinatewise, because all the operations of `lp _ ∞` are coordinatewise. -/
def doubledDiagSeqHom :
    StarStrong.BoundedStarSequence A →⋆ₙₐ[ℂ]
      StarStrong.BoundedStarSequence (fun n ↦ DoubledModel A n) where
  toFun := doubledDiagSeq
  map_zero' := by
    apply lp.ext
    funext n
    exact map_zero (diagonalHom2 (E := A n))
  map_add' x y := by
    apply lp.ext
    funext n
    exact map_add (diagonalHom2 (E := A n)) (x n) (y n)
  map_mul' x y := by
    apply lp.ext
    funext n
    exact map_mul (diagonalHom2 (E := A n)) (x n) (y n)
  map_smul' z x := by
    apply lp.ext
    funext n
    exact map_smul (diagonalHom2 (E := A n)) z (x n)
  map_star' x := by
    apply lp.ext
    funext n
    exact map_star (diagonalHom2 (E := A n)) (x n)

@[simp] theorem doubledDiagSeqHom_apply (x : StarStrong.BoundedStarSequence A) :
    doubledDiagSeqHom (A := A) x = doubledDiagSeq x := rfl

theorem doubledDiagSeq_sub (x y : StarStrong.BoundedStarSequence A) :
    doubledDiagSeq (A := A) (x - y) = doubledDiagSeq x - doubledDiagSeq y :=
  map_sub (doubledDiagSeqHom (A := A)) x y

-- There is deliberately no `doubledDiagSeq_smul` here.  Writing `z • y` with
-- `y : lp (fun n ↦ DoubledModel A n) ∞` in a *statement* opens a bare
-- `SMul ℂ (lp …)` goal, and that search walks the whole `CStarMatrix` tower and
-- overruns the instance budget.  Inside a proof the same equation costs
-- nothing: `map_smul doubledDiagSeqHom` carries the scalar action along in the
-- homomorphism's own type, so no new goal is opened.  See the `tendsto_smul`
-- clause of `StarStrongAsymptoticLift.double` below.

theorem doubledDiagSeq_mul (x y : StarStrong.BoundedStarSequence A) :
    doubledDiagSeq (A := A) (x * y) = doubledDiagSeq x * doubledDiagSeq y :=
  map_mul (doubledDiagSeqHom (A := A)) x y

theorem doubledDiagSeq_star (x : StarStrong.BoundedStarSequence A) :
    doubledDiagSeq (A := A) (star x) = star (doubledDiagSeq x) :=
  map_star (doubledDiagSeqHom (A := A)) x

/-- **The doubled sequence map is contractive.**  Each coordinate is, and the
`ℓ∞`-norm is the supremum of the coordinate norms. -/
theorem norm_doubledDiagSeq_le (x : StarStrong.BoundedStarSequence A) :
    ‖doubledDiagSeq (A := A) x‖ ≤ ‖x‖ := by
  rw [lp.norm_eq_ciSup]
  exact ciSup_le fun n ↦ (norm_diagonalHom2_le (x n)).trans
    (lp.norm_apply_le_norm ENNReal.top_ne_zero x n)

/-- **The doubled sequence converges strongly to the doubled limit.**  The
entrywise statement `tendsto_diagonalHom2_entry`, transported by
`tendsto_hBlockOp_of_coord`. -/
theorem tendsto_doubledDiagSeq_apply (x : StarStrong.BoundedStarSequence A)
    {T : H →L[ℂ] H}
    (hT : ∀ v : H, Tendsto (fun n ↦ ι n (x n) v) atTop (𝓝 (T v)))
    (w : BlockSpace H 2) :
    Tendsto (fun n ↦ doubledIota ι n ((doubledDiagSeq (A := A) x) n) w) atTop
      (𝓝 (hBlockOp (diagonalHom2 T) w)) := by
  -- stated at the un-abbreviated block operator, so that
  -- `tendsto_hBlockOp_of_coord` has its matrix sequence in hand rather than
  -- behind `doubledIota`
  have key : Tendsto
      (fun n ↦ hBlockOp ((CStarMatrix.mapₙₐ (ι n))
        (diagonalHom2 (x n) : CStarMatrix (Fin 2) (Fin 2) (A n))) w) atTop
      (𝓝 (hBlockOp (diagonalHom2 T) w)) :=
    tendsto_hBlockOp_of_coord
      (fun i j y ↦ tendsto_diagonalHom2_entry ι x hT i j y) w
  exact key

/-- **The `*`-strong limit of a doubled sequence is the doubled limit.**  The
adjoint clause is the first clause at `star x`, because the diagonal and the
doubled embedding both commute with the adjoint. -/
theorem isStarStrongLimit_doubledDiagSeq (x : StarStrong.BoundedStarSequence A)
    {T : H →L[ℂ] H}
    (hT : StarStrong.IsStarStrongLimit (fun n ↦ ι n (x n)) T) :
    StarStrong.IsStarStrongLimit
      (fun n ↦ doubledIota ι n ((doubledDiagSeq (A := A) x) n))
      (hBlockOp (diagonalHom2 T)) := by
  refine ⟨fun w ↦ tendsto_doubledDiagSeq_apply ι x hT.1 w, fun w ↦ ?_⟩
  have hstar : ∀ y : H,
      Tendsto (fun n ↦ ι n ((star x : StarStrong.BoundedStarSequence A) n) y)
        atTop (𝓝 ((star T) y)) := by
    intro y
    have hfun : (fun n ↦ ι n ((star x : StarStrong.BoundedStarSequence A) n) y)
        = fun n ↦ (star (ι n (x n))) y := by
      funext n
      have h : ι n ((star x : StarStrong.BoundedStarSequence A) n)
          = star (ι n (x n)) := map_star (ι n) (x n)
      rw [h]
    rw [hfun]
    exact hT.2 y
  have key := tendsto_doubledDiagSeq_apply ι
    (star x : StarStrong.BoundedStarSequence A) hstar w
  have hL : (fun n ↦ doubledIota ι n ((doubledDiagSeq (A := A)
        (star x : StarStrong.BoundedStarSequence A)) n) w)
      = fun n ↦ (star (doubledIota ι n ((doubledDiagSeq (A := A) x) n))) w := by
    funext n
    have h1 : (doubledDiagSeq (A := A)
        (star x : StarStrong.BoundedStarSequence A)) n
        = star ((doubledDiagSeq (A := A) x) n) :=
      map_star (diagonalHom2 (E := A n)) (x n)
    have h : doubledIota ι n ((doubledDiagSeq (A := A)
        (star x : StarStrong.BoundedStarSequence A)) n)
        = star (doubledIota ι n ((doubledDiagSeq (A := A) x) n)) := by
      rw [h1, map_star]
    rw [h]
  have hR : hBlockOp (diagonalHom2 (star T))
      = star (hBlockOp (diagonalHom2 T)) := by
    rw [map_star (diagonalHom2 (E := H →L[ℂ] H)) T]
    exact hBlockOp_star (diagonalHom2 T)
  rw [hL, hR] at key
  exact key

/-! ## The bridge -/

section Unital

variable [∀ n, Nontrivial (A n)]

/-- The doubled sequence of the unit is the unit: `diag(1, 1) = 1`. -/
theorem doubledDiagSeq_one :
    doubledDiagSeq (A := A) 1 = 1 := by
  apply lp.ext
  funext n
  exact map_one (diagonalHom2 (E := A n))

/-- **A doubled sequence lies in the doubled `𝒟`.** -/
theorem doubledDiagSeq_mem
    (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
    (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))
    (x : StarStrong.BoundedStarSequence A)
    (hx : x ∈ StarStrong.starStrongSubalgebra ι hnorm hone) :
    doubledDiagSeq (A := A) x ∈ StarStrong.starStrongSubalgebra (doubledIota ι)
      (doubled_norm_le ι) (doubled_hone ι hone) := by
  obtain ⟨T, hT⟩ : ∃ T : H →L[ℂ] H,
    StarStrong.IsStarStrongLimit (fun n ↦ ι n (x n)) T := hx
  exact ⟨hBlockOp (diagonalHom2 T), isStarStrongLimit_doubledDiagSeq ι x hT⟩

namespace StarStrongAsymptoticLift

/-- **The doubling bridge.**  An asymptotic lift of `π` into `𝒟` gives an
asymptotic lift of `diag(π, π)` into the doubled `𝒟`, by doubling every value.

The five defect clauses are the corresponding defects of `φ`, doubled and
bounded by `norm_doubledDiagSeq_le`; the lifting clause stays exact, because the
`*`-strong limit of `diag(φ_t b, φ_t b)` is `diag(π b, π b)` by
`isStarStrongLimit_doubledDiagSeq`. -/
def double {hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖}
    {hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)}
    {B : Type} [CStarAlgebra B] {π : B →⋆ₐ[ℂ] (H →L[ℂ] H)}
    (φ : StarStrongAsymptoticLift ι hnorm hone π) :
    StarStrongAsymptoticLift (doubledIota ι) (doubled_norm_le ι)
      (doubled_hone ι hone) (doubledRep π) where
  toFun t b := doubledDiagSeq (A := A) (φ.toFun t b)
  mem t b := doubledDiagSeq_mem ι hnorm hone (φ.toFun t b) (φ.mem t b)
  norm_le t b := (norm_doubledDiagSeq_le (φ.toFun t b)).trans (φ.norm_le t b)
  tendsto_add b c := by
    refine squeeze_zero (fun t ↦ norm_nonneg _) (fun t ↦ ?_) (φ.tendsto_add b c)
    have h : doubledDiagSeq (A := A) (φ.toFun t (b + c))
          - doubledDiagSeq (A := A) (φ.toFun t b)
          - doubledDiagSeq (A := A) (φ.toFun t c)
        = doubledDiagSeq (A := A)
            (φ.toFun t (b + c) - φ.toFun t b - φ.toFun t c) := by
      rw [doubledDiagSeq_sub, doubledDiagSeq_sub]
    rw [h]
    exact norm_doubledDiagSeq_le _
  tendsto_smul z b := by
    refine squeeze_zero (fun t ↦ norm_nonneg _) (fun t ↦ ?_)
      (φ.tendsto_smul z b)
    -- `hsm` is never *stated*, only obtained: `map_smul` builds the scalar
    -- action into its own conclusion from the homomorphism's type, so the
    -- expensive `SMul ℂ (lp (fun n ↦ DoubledModel A n) ∞)` goal is never opened.
    have hsm := map_smul (doubledDiagSeqHom (A := A)) z (φ.toFun t b)
    simp only [doubledDiagSeqHom_apply] at hsm
    rw [← hsm, ← doubledDiagSeq_sub]
    exact norm_doubledDiagSeq_le _
  tendsto_mul b c := by
    refine squeeze_zero (fun t ↦ norm_nonneg _) (fun t ↦ ?_) (φ.tendsto_mul b c)
    have h : doubledDiagSeq (A := A) (φ.toFun t (b * c))
          - doubledDiagSeq (A := A) (φ.toFun t b)
            * doubledDiagSeq (A := A) (φ.toFun t c)
        = doubledDiagSeq (A := A)
            (φ.toFun t (b * c) - φ.toFun t b * φ.toFun t c) := by
      rw [doubledDiagSeq_sub, doubledDiagSeq_mul]
    rw [h]
    exact norm_doubledDiagSeq_le _
  tendsto_star b := by
    refine squeeze_zero (fun t ↦ norm_nonneg _) (fun t ↦ ?_) (φ.tendsto_star b)
    have h : doubledDiagSeq (A := A) (φ.toFun t (star b))
          - star (doubledDiagSeq (A := A) (φ.toFun t b))
        = doubledDiagSeq (A := A)
            (φ.toFun t (star b) - star (φ.toFun t b)) := by
      rw [doubledDiagSeq_sub, doubledDiagSeq_star]
    rw [h]
    exact norm_doubledDiagSeq_le _
  tendsto_one := by
    refine squeeze_zero (fun t ↦ norm_nonneg _) (fun t ↦ ?_) φ.tendsto_one
    have h : doubledDiagSeq (A := A) (φ.toFun t (1 : B)) - 1
        = doubledDiagSeq (A := A) (φ.toFun t (1 : B) - 1) := by
      rw [doubledDiagSeq_sub, doubledDiagSeq_one]
    rw [h]
    exact norm_doubledDiagSeq_le _
  lift t b := by
    have hT : StarStrong.IsStarStrongLimit
        (fun n ↦ ι n ((φ.toFun t b) n)) (π b) := by
      have h := StarStrong.starStrongLimit_spec ι hnorm hone
        ⟨φ.toFun t b, φ.mem t b⟩
      rwa [φ.starStrongLimit_toFun t b] at h
    exact StarStrong.starStrongLimit_eq (doubledIota ι) (doubled_norm_le ι)
      (doubled_hone ι hone) _
      (isStarStrongLimit_doubledDiagSeq ι (φ.toFun t b) hT)

@[simp] theorem double_toFun {hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖}
    {hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)}
    {B : Type} [CStarAlgebra B] {π : B →⋆ₐ[ℂ] (H →L[ℂ] H)}
    (φ : StarStrongAsymptoticLift ι hnorm hone π) (t : ℕ) (b : B) :
    (double ι φ).toFun t b = doubledDiagSeq (A := A) (φ.toFun t b) := rfl

end StarStrongAsymptoticLift

end Unital

end DoubledSequence

end

end ShulmanFill
end GroupApproximation
