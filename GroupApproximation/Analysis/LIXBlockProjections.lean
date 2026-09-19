import GroupApproximation.Analysis.LIXProjectiveSpaceModel
import GroupApproximation.KTheory.MatrixProjection
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!
# The block projections of the STW LIX construction

This file writes down, as explicit projection-valued matrix functions, the bundles of
the inductive system in §4 of
`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`, and the
rank-two bundle `F` over `S^5` from §2.  Nothing here uses a vector-bundle library: a
bundle *is* a projection `p : Matrix ι ι C(X, ℂ)` and bundle isomorphism *is*
`GroupApproximation.MurrayVonNeumannEquiv`, as in
`GroupApproximation/KTheory/MatrixProjection.lean`.

## Model choices (other LIX lanes must match these exactly)

* `S^4 := STW59.sphereFour = Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1`, used as the
  subtype `↥STW59.sphereFour`.
* `S^5 ⊂ ℂ³ := STW59.sphereFive = STW59.unitVectors (Fin 3)`, a subset of the *plain*
  product space `Fin 3 → ℂ` cut out by `∑ i, ‖x i‖ ^ 2 = 1`.  **No `EuclideanSpace ℂ` and
  no `PiLp` anywhere**: coordinates are needed to write `x xᴴ`, and `PiLp` coordinate
  access has been an elaboration trap in this repo.
* `ℂP^d := STW59.CP d`, the matrix model of `Analysis/LIXProjectiveSpaceModel.lean`.
* Stage data: `r i = STW59.stageRank i = 2 ^ (i + 1)`,
  `Y i = STW59.baseY i = ∀ j : Fin i, CP (r j)`,
  `X i = STW59.baseX i = ↥sphereFour × baseY i`.
* Index types are **recursive in the stage**, so that the block decomposition used by the
  connecting maps of `Analysis/LIXConnectingMap.lean` is definitional:
  `STW59.NIdx i = Fin (r i) × Fin (r i + 1)` (`r i` copies of the ambient `ℂ^{r i + 1}` of
  `CP^{r i}`), `STW59.HIdx (i+1) = HIdx i ⊕ NIdx i` with `HIdx 0 = Empty`, and
  `STW59.EIdx i = Fin 2 ⊕ HIdx i`.  Thus
  `EIdx (i+1) = Fin 2 ⊕ (HIdx i ⊕ NIdx i)` is `Equiv.sumAssoc`-equivalent to
  `EIdx i ⊕ NIdx i` (`STW59.eIdxSucc`), and `STW59.Eproj_succ` says that under exactly
  that equivalence `E_{i+1} = π_i^* E_i ⊕ (𝟏_{r i} ⊗ L_{i+1})`.
* Coefficients live in `C(X i, ℂ)`, so the block assembly needs no continuity proof:
  `Matrix.fromBlocks` over a ring of continuous functions is continuous by construction.

## Main results

* `STW59.trace_Hproj`, `STW59.trace_Eproj`, `STW59.hrank_add_two`,
  `STW59.realDim_baseX` — the manuscript's (4.2): `rank H_i = r_i - 2`,
  `rank E_i = r_i`, `dim_ℝ X_i = 2 r_i`.
* `STW59.Eproj_succ` — the manuscript's global bundle decomposition
  `E_{i+1} ≅ π_i^* E_i ⊕ (E_i(x_i) ⊗ L_{i+1})`, in the form in which the connecting map
  uses it.
* `STW59.exists_frame` — a star projection of trace `k` over `ℂ` is `s sᴴ` for an
  isometry `s : ℂ^k → ℂ^n`; this is the manuscript's "choose an orthonormal
  identification `E_i(x_i) ≅ ℂ^{r_i}`".
* `STW59.murrayVonNeumannEquiv_Fproj` — `F ⊕ 𝟏 ≅ 𝟏³` over `S^5`.
* `STW59.isLocallyConstant_trace` — the rank of a projection-valued function is locally
  constant, because it is a continuous `ℕ`-valued function
  (`STW59.exists_natCast_trace`).
-/

namespace GroupApproximation
namespace STW59

open scoped Matrix Kronecker

noncomputable section

/-! ### Generic block lemmas -/

section Blocks

variable {A : Type*} [NonUnitalNonAssocSemiring A] [StarRing A]

theorem isStarProjection_blockDiagonal {o m : Type*} [DecidableEq o] [Fintype o] [Fintype m]
    {M : o → Matrix m m A} (h : ∀ k, IsStarProjection (M k)) :
    IsStarProjection (Matrix.blockDiagonal M) := by
  rw [isStarProjection_matrix_iff]
  constructor
  · rw [Matrix.blockDiagonal_conjTranspose]
    congr 1
    funext k
    exact conjTranspose_eq_of_isStarProjection (h k)
  · rw [← Matrix.blockDiagonal_mul]
    congr 1
    funext k
    exact (h k).isIdempotentElem.eq

theorem isStarProjection_fromBlocks_diag {l m : Type*} [Fintype l] [Fintype m]
    {P : Matrix l l A} {Q : Matrix m m A} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) : IsStarProjection (Matrix.fromBlocks P 0 0 Q) := by
  rw [isStarProjection_matrix_iff]
  constructor
  · simp [Matrix.fromBlocks_conjTranspose, conjTranspose_eq_of_isStarProjection hP,
      conjTranspose_eq_of_isStarProjection hQ]
  · rw [Matrix.fromBlocks_multiply]
    simp [hP.isIdempotentElem.eq, hQ.isIdempotentElem.eq]

end Blocks

/-- A Kronecker product of star projections is a star projection. -/
theorem isStarProjection_kronecker {A : Type*} [CommRing A] [StarRing A] {m n : Type*}
    [Fintype m] [Fintype n] {P : Matrix m m A} {Q : Matrix n n A} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) : IsStarProjection (P ⊗ₖ Q) := by
  rw [isStarProjection_matrix_iff]
  constructor
  · rw [Matrix.conjTranspose_kronecker, conjTranspose_eq_of_isStarProjection hP,
      conjTranspose_eq_of_isStarProjection hQ]
  · rw [← Matrix.mul_kronecker_mul, hP.isIdempotentElem.eq, hQ.isIdempotentElem.eq]

theorem trace_fromBlocks {l m R : Type*} [Fintype l] [Fintype m] [AddCommMonoid R]
    (P : Matrix l l R) (B : Matrix l m R) (C : Matrix m l R) (Q : Matrix m m R) :
    (Matrix.fromBlocks P B C Q).trace = P.trace + Q.trace := by
  simp [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type]

/-! ### Constant and pulled-back matrices of functions -/

section Transfer

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {ι κ : Type*}

/-- A matrix of scalars, read as a matrix of constant continuous functions. -/
def constMat (X : Type*) [TopologicalSpace X] (M : Matrix ι κ ℂ) : Matrix ι κ C(X, ℂ) :=
  M.map fun c => ContinuousMap.const X c

@[simp]
theorem matEval_constMat (x : X) (M : Matrix ι κ ℂ) : matEval x (constMat X M) = M := rfl

theorem constMat_mul [Fintype κ] {ρ : Type*} (M : Matrix ι κ ℂ) (N : Matrix κ ρ ℂ) :
    constMat X (M * N) = constMat X M * constMat X N := by
  refine matrix_ext_of_matEval fun x => ?_
  rw [matEval_constMat, matEval_mul, matEval_constMat, matEval_constMat]

theorem constMat_one [DecidableEq ι] : constMat X (1 : Matrix ι ι ℂ) = 1 := by
  refine matrix_ext_of_matEval fun x => ?_
  rw [matEval_constMat, matEval_one]

theorem constMat_conjTranspose (M : Matrix ι κ ℂ) :
    constMat X Mᴴ = (constMat X M)ᴴ := by
  refine matrix_ext_of_matEval fun x => ?_
  rw [matEval_constMat, matEval_conjTranspose, matEval_constMat]

theorem matEval_add (x : X) (M N : Matrix ι κ C(X, ℂ)) :
    matEval x (M + N) = matEval x M + matEval x N :=
  Matrix.ext fun _ _ => rfl

theorem matEval_smul (x : X) (c : ℂ) (M : Matrix ι κ C(X, ℂ)) :
    matEval x (c • M) = c • matEval x M :=
  Matrix.ext fun _ _ => rfl

theorem constMat_add (M N : Matrix ι κ ℂ) :
    constMat X (M + N) = constMat X M + constMat X N := by
  refine matrix_ext_of_matEval fun x => ?_
  rw [matEval_add, matEval_constMat, matEval_constMat, matEval_constMat]

theorem constMat_smul (c : ℂ) (M : Matrix ι κ ℂ) :
    constMat X (c • M) = c • constMat X M := by
  refine matrix_ext_of_matEval fun x => ?_
  rw [matEval_smul, matEval_constMat, matEval_constMat]

/-- Pulling a matrix of continuous functions back along a continuous map. -/
def pullMat (f : C(X, Y)) (M : Matrix ι κ C(Y, ℂ)) : Matrix ι κ C(X, ℂ) :=
  M.map fun g => g.comp f

@[simp]
theorem matEval_pullMat (f : C(X, Y)) (M : Matrix ι κ C(Y, ℂ)) (x : X) :
    matEval x (pullMat f M) = matEval (f x) M := rfl

theorem pullMat_mul [Fintype κ] {ρ : Type*} (f : C(X, Y)) (M : Matrix ι κ C(Y, ℂ))
    (N : Matrix κ ρ C(Y, ℂ)) : pullMat f (M * N) = pullMat f M * pullMat f N := by
  refine matrix_ext_of_matEval fun x => ?_
  rw [matEval_pullMat, matEval_mul, matEval_mul, matEval_pullMat, matEval_pullMat]

theorem pullMat_one [DecidableEq ι] (f : C(X, Y)) :
    pullMat f (1 : Matrix ι ι C(Y, ℂ)) = 1 := by
  refine matrix_ext_of_matEval fun x => ?_
  rw [matEval_pullMat, matEval_one, matEval_one]

theorem pullMat_zero (f : C(X, Y)) : pullMat f (0 : Matrix ι κ C(Y, ℂ)) = 0 := by
  refine matrix_ext_of_matEval fun x => ?_
  rw [matEval_pullMat, matEval_zero, matEval_zero]

theorem pullMat_add (f : C(X, Y)) (M N : Matrix ι κ C(Y, ℂ)) :
    pullMat f (M + N) = pullMat f M + pullMat f N := by
  refine matrix_ext_of_matEval fun x => ?_
  rw [matEval_pullMat, matEval_add, matEval_add, matEval_pullMat, matEval_pullMat]

theorem pullMat_smul (f : C(X, Y)) (c : ℂ) (M : Matrix ι κ C(Y, ℂ)) :
    pullMat f (c • M) = c • pullMat f M := by
  refine matrix_ext_of_matEval fun x => ?_
  rw [matEval_pullMat, matEval_smul, matEval_smul, matEval_pullMat]

/-- **A pullback along a surjective map is injective.**  This is what makes the connecting
maps of `Analysis/LIXConnectingMap.lean` injective: the (1,1) block of `φ_i(a)` is
`pullMat π a`, and `π = baseProj i` is surjective (`STW59.basePr_surjective`). -/
theorem pullMat_injective_of_surjective {f : C(X, Y)} (hf : Function.Surjective f) :
    Function.Injective (pullMat f : Matrix ι κ C(Y, ℂ) → Matrix ι κ C(X, ℂ)) := by
  intro M N h
  refine matrix_ext_of_matEval fun y => ?_
  obtain ⟨x, rfl⟩ := hf y
  have h' := congrArg (matEval x) h
  rwa [matEval_pullMat, matEval_pullMat] at h'

theorem pullMat_conjTranspose (f : C(X, Y)) (M : Matrix ι κ C(Y, ℂ)) :
    pullMat f Mᴴ = (pullMat f M)ᴴ := by
  refine matrix_ext_of_matEval fun x => ?_
  rw [matEval_pullMat, matEval_conjTranspose, matEval_conjTranspose, matEval_pullMat]

theorem pullMat_constMat (f : C(X, Y)) (M : Matrix ι κ ℂ) :
    pullMat f (constMat Y M) = constMat X M := by
  refine matrix_ext_of_matEval fun x => ?_
  rw [matEval_pullMat, matEval_constMat, matEval_constMat]

theorem pullMat_fromBlocks {l m n p : Type*} (f : C(X, Y)) (A : Matrix l m C(Y, ℂ))
    (B : Matrix l p C(Y, ℂ)) (C : Matrix n m C(Y, ℂ)) (D : Matrix n p C(Y, ℂ)) :
    pullMat f (Matrix.fromBlocks A B C D)
      = Matrix.fromBlocks (pullMat f A) (pullMat f B) (pullMat f C) (pullMat f D) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> rfl

theorem pullMat_comp {Z : Type*} [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z))
    (M : Matrix ι κ C(Z, ℂ)) : pullMat f (pullMat g M) = pullMat (g.comp f) M := rfl

theorem pullMat_kronecker {l n l' n' : Type*} (f : C(X, Y)) (A : Matrix l l' C(Y, ℂ))
    (B : Matrix n n' C(Y, ℂ)) :
    pullMat f (A ⊗ₖ B) = pullMat f A ⊗ₖ pullMat f B :=
  Matrix.ext fun _ _ => rfl

theorem isStarProjection_pullMat [Fintype ι] [DecidableEq ι] (f : C(X, Y))
    {M : Matrix ι ι C(Y, ℂ)} (h : IsStarProjection M) : IsStarProjection (pullMat f M) := by
  refine isStarProjection_of_forall_matEval fun x => ?_
  rw [matEval_pullMat]
  exact isStarProjection_matEval h _

end Transfer

/-! ### Reindexing along a fixed equivalence, compatibly with `+`, scalars, `*`, and `ᴴ`

`Matrix.reindex e e'` is used (in `Eproj_succ` below, and in `Analysis/LIXConnectingMap.lean`)
purely as an index relabelling, so every algebraic operation commutes with it; the `+`/smul/`ᴴ`
cases are `rfl` since `reindex e e' M = M.submatrix e.symm e'.symm` is entrywise, and the `*`
case (same equivalence on both sides) is Mathlib's `Matrix.reindexRingEquiv`. -/

section Reindex

variable {X : Type*} [TopologicalSpace X] {ι κ ι' κ' : Type*}

theorem reindex_add (e : ι ≃ ι') (e' : κ ≃ κ') (M N : Matrix ι κ C(X, ℂ)) :
    Matrix.reindex e e' (M + N) = Matrix.reindex e e' M + Matrix.reindex e e' N :=
  Matrix.ext fun _ _ => rfl

theorem reindex_smul (e : ι ≃ ι') (e' : κ ≃ κ') (c : ℂ) (M : Matrix ι κ C(X, ℂ)) :
    Matrix.reindex e e' (c • M) = c • Matrix.reindex e e' M :=
  Matrix.ext fun _ _ => rfl

theorem reindex_conjTranspose (e : ι ≃ κ) (M : Matrix ι ι C(X, ℂ)) :
    Matrix.reindex e e Mᴴ = (Matrix.reindex e e M)ᴴ :=
  Matrix.ext fun _ _ => rfl

theorem reindex_mul [Fintype ι] [Fintype κ] (e : ι ≃ κ) (M N : Matrix ι ι C(X, ℂ)) :
    Matrix.reindex e e (M * N) = Matrix.reindex e e M * Matrix.reindex e e N := by
  simp

end Reindex

/-! ### An orthonormal frame for the range of a projection

The manuscript's "choose an orthonormal identification `E_i(x_i) ≅ ℂ^{r_i}`", proved by
peeling rank-one subprojections off (`STW59.exists_rankOneProj_absorbed`), with no
spectral theorem. -/

/-- **A star projection of trace `k` is `s sᴴ` for an isometry `s : ℂ^k → ℂ^n`.** -/
theorem exists_frame {n : Type*} [Fintype n] [DecidableEq n] :
    ∀ (k : ℕ) (q : Matrix n n ℂ), IsStarProjection q → q.trace = (k : ℂ) →
      ∃ s : Matrix n (Fin k) ℂ, sᴴ * s = 1 ∧ s * sᴴ = q := by
  intro k
  induction k with
  | zero =>
      intro q hq ht
      have hq0 : q = 0 := proj_eq_zero_of_trace_eq_zero hq (by simpa using ht)
      refine ⟨0, ?_, ?_⟩
      · ext i j
        exact i.elim0
      · rw [hq0, Matrix.conjTranspose_zero, Matrix.mul_zero]
  | succ k ih =>
      intro q hq ht
      have hne : q ≠ 0 := by
        intro h
        rw [h, Matrix.trace_zero] at ht
        have hz : ((k + 1 : ℕ) : ℂ) = 0 := ht.symm
        have hz' : (k + 1 : ℕ) = 0 := by exact_mod_cast hz
        omega
      obtain ⟨j, hj⟩ := exists_column_ne_zero hne
      obtain ⟨x, hxu, hqP, hPq⟩ := exists_rankOneProj_absorbed hq hj
      have hPproj : IsStarProjection (rankOneProj x) := isStarProjection_rankOneProj hxu
      have hq' : IsStarProjection (q - rankOneProj x) := isStarProjection_sub hq hPproj hqP hPq
      have ht' : (q - rankOneProj x).trace = (k : ℂ) := by
        rw [Matrix.trace_sub, ht, trace_rankOneProj hxu]
        push_cast
        ring
      obtain ⟨s', hs'1, hs'2⟩ := ih (q - rankOneProj x) hq' ht'
      -- `x` as a one-column matrix, so that everything below is matrix multiplication
      obtain ⟨col, hcol⟩ : ∃ c : Matrix n (Fin 1) ℂ, ∀ (a : n) (u : Fin 1), c a u = x a :=
        ⟨Matrix.of fun a _ => x a, fun _ _ => rfl⟩
      -- the peeled rank-one projection fixes `x`, so the remainder annihilates it
      have hPx : rankOneProj x * col = col := by
        ext i u
        rw [Matrix.mul_apply, hcol i u]
        have hterm : ∀ a : n, rankOneProj x i a * col a u = x i * (star (x a) * x a) := by
          intro a
          rw [rankOneProj_apply, hcol a u]
          ring
        rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.mul_sum,
          sum_star_mul_self hxu, mul_one]
      have hzero : (q - rankOneProj x) * rankOneProj x = 0 := by
        rw [Matrix.sub_mul, hqP, hPproj.isIdempotentElem.eq, sub_self]
      have hAnn : (q - rankOneProj x) * col = 0 := by
        have h1 : (q - rankOneProj x) * col = (q - rankOneProj x) * (rankOneProj x * col) := by
          rw [hPx]
        rw [h1, ← Matrix.mul_assoc, hzero, Matrix.zero_mul]
      -- hence the frame of the remainder is orthogonal to `x`
      have hsq : s'ᴴ * (q - rankOneProj x) = s'ᴴ := by
        rw [← hs'2, ← Matrix.mul_assoc, hs'1, Matrix.one_mul]
      have hOrth : ∀ j' : Fin k, (∑ a, star (s' a j') * x a) = 0 := by
        intro j'
        have hv : s'ᴴ * col = 0 := by
          have h1 : s'ᴴ * col = (s'ᴴ * (q - rankOneProj x)) * col := by rw [hsq]
          rw [h1, Matrix.mul_assoc, hAnn, Matrix.mul_zero]
        have h2 : (s'ᴴ * col) j' 0 = 0 := by rw [hv, Matrix.zero_apply]
        rw [Matrix.mul_apply] at h2
        have hterm : ∀ a : n, s'ᴴ j' a * col a 0 = star (s' a j') * x a := by
          intro a
          rw [Matrix.conjTranspose_apply, hcol a 0]
        rw [Finset.sum_congr rfl fun a _ => hterm a] at h2
        exact h2
      have hOrth' : ∀ j' : Fin k, (∑ a, star (x a) * s' a j') = 0 := by
        intro j'
        have hstep : (∑ a, star (x a) * s' a j') = star (∑ a, star (s' a j') * x a) := by
          rw [star_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [star_mul, star_star]
        rw [hstep, hOrth j', star_zero]
      -- the frame of `q`: the unit vector `x` followed by the frame of the remainder
      obtain ⟨s, hs0, hssucc⟩ : ∃ s : Matrix n (Fin (k + 1)) ℂ,
          (∀ a : n, s a 0 = x a) ∧ (∀ (a : n) (j' : Fin k), s a j'.succ = s' a j') :=
        ⟨Matrix.of fun a => Fin.cons (x a) (s' a), fun _ => rfl, fun _ _ => rfl⟩
      refine ⟨s, ?_, ?_⟩
      · ext u v
        rw [Matrix.mul_apply]
        obtain rfl | ⟨u', rfl⟩ := u.eq_zero_or_eq_succ
        · obtain rfl | ⟨v', rfl⟩ := v.eq_zero_or_eq_succ
          · have hterm : ∀ a : n, sᴴ 0 a * s a 0 = star (x a) * x a := by
              intro a
              rw [Matrix.conjTranspose_apply, hs0 a]
            rw [Finset.sum_congr rfl fun a _ => hterm a, sum_star_mul_self hxu,
              Matrix.one_apply_eq]
          · have hterm : ∀ a : n, sᴴ 0 a * s a v'.succ = star (x a) * s' a v' := by
              intro a
              rw [Matrix.conjTranspose_apply, hs0 a, hssucc a v']
            rw [Finset.sum_congr rfl fun a _ => hterm a, hOrth' v',
              Matrix.one_apply_ne (Ne.symm (Fin.succ_ne_zero v'))]
        · obtain rfl | ⟨v', rfl⟩ := v.eq_zero_or_eq_succ
          · have hterm : ∀ a : n, sᴴ u'.succ a * s a 0 = star (s' a u') * x a := by
              intro a
              rw [Matrix.conjTranspose_apply, hssucc a u', hs0 a]
            rw [Finset.sum_congr rfl fun a _ => hterm a, hOrth u',
              Matrix.one_apply_ne (Fin.succ_ne_zero u')]
          · have hterm : ∀ a : n, sᴴ u'.succ a * s a v'.succ = s'ᴴ u' a * s' a v' := by
              intro a
              rw [Matrix.conjTranspose_apply, Matrix.conjTranspose_apply, hssucc a u',
                hssucc a v']
            rw [Finset.sum_congr rfl fun a _ => hterm a, ← Matrix.mul_apply, hs'1]
            by_cases huv : u' = v'
            · subst huv
              rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
            · rw [Matrix.one_apply_ne huv,
                Matrix.one_apply_ne (fun hsucc => huv (Fin.succ_inj.mp hsucc))]
      · ext a b
        rw [Matrix.mul_apply, Fin.sum_univ_succ]
        have hhead : s a 0 * sᴴ 0 b = rankOneProj x a b := by
          rw [Matrix.conjTranspose_apply, hs0 a, hs0 b, rankOneProj_apply]
        have htail : ∀ j' : Fin k, s a j'.succ * sᴴ j'.succ b = s' a j' * s'ᴴ j' b := by
          intro j'
          rw [Matrix.conjTranspose_apply, Matrix.conjTranspose_apply, hssucc a j',
            hssucc b j']
        rw [hhead, Finset.sum_congr rfl fun j' _ => htail j', ← Matrix.mul_apply, hs'2,
          Matrix.sub_apply]
        ring

/-- **`Aᴴ A` has zero trace only for `A = 0`**: the trace is the sum of the squared norms
of the entries.  This is what makes a section with a nowhere-zero `aᴴ a` trace full. -/
theorem eq_zero_of_trace_conjTranspose_mul_self {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : Matrix ι κ ℂ} (h : (Aᴴ * A).trace = 0) : A = 0 := by
  have hd : (Aᴴ * A).trace = ∑ s : κ, (Aᴴ * A) s s := rfl
  have hterm : ∀ s : κ, (Aᴴ * A) s s = ((∑ u : ι, ‖A u s‖ ^ 2 : ℝ) : ℂ) := by
    intro s
    rw [Matrix.mul_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Matrix.conjTranspose_apply, star_mul_self_eq_normSq]
  rw [hd, Finset.sum_congr rfl (fun s _ => hterm s), ← Complex.ofReal_sum] at h
  have hreal : (∑ s : κ, ∑ u : ι, ‖A u s‖ ^ 2 : ℝ) = 0 := by exact_mod_cast h
  refine Matrix.ext fun u s => ?_
  have h1 : (∑ u' : ι, ‖A u' s‖ ^ 2) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun s' _ => Finset.sum_nonneg fun u' _ => by positivity)).mp hreal s (Finset.mem_univ s)
  have h2 : ‖A u s‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun u' _ => by positivity)).mp h1 u (Finset.mem_univ u)
  have h3 : ‖A u s‖ = 0 := by nlinarith [norm_nonneg (A u s)]
  rw [Matrix.zero_apply]
  exact norm_eq_zero.mp h3

/-! ### The base spaces -/

/-- `S^4`, the unit sphere of `ℝ^5`. -/
abbrev sphereFour : Set (EuclideanSpace ℝ (Fin 5)) := Metric.sphere 0 1

/-- `S^5`, the unit sphere of `ℂ³` inside the plain product space `Fin 3 → ℂ`. -/
abbrev sphereFive : Set (Fin 3 → ℂ) := unitVectors (Fin 3)

instance sphereFive.instCompactSpace : CompactSpace ↥sphereFive :=
  isCompact_iff_compactSpace.mp (isCompact_unitVectors (Fin 3))

instance sphereFive.instNonempty : Nonempty ↥sphereFive := by
  classical
  refine ⟨⟨fun i : Fin 3 => if i = 0 then (1 : ℂ) else 0, ?_⟩⟩
  show (∑ i : Fin 3, ‖(if i = 0 then (1 : ℂ) else 0)‖ ^ 2) = 1
  rw [Finset.sum_eq_single (0 : Fin 3)]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin 3)) h

instance sphereFour.instCompactSpace : CompactSpace ↥sphereFour :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 5)) 1)

instance sphereFour.instNonempty : Nonempty ↥sphereFour :=
  Set.Nonempty.to_subtype (NormedSpace.sphere_nonempty.mpr zero_le_one)

/-! ### Stage data -/

/-- `r i = 2^{i+1}`, the rank of `E_i` in the manuscript's (4.1). -/
def stageRank (i : ℕ) : ℕ := 2 ^ (i + 1)

@[simp] theorem stageRank_zero : stageRank 0 = 2 := by simp [stageRank]

theorem stageRank_pos (i : ℕ) : 0 < stageRank i := by
  unfold stageRank
  positivity

theorem stageRank_succ (i : ℕ) : stageRank (i + 1) = 2 * stageRank i := by
  unfold stageRank
  rw [pow_succ]
  ring

/-- `rank H_i = ∑_{j<i} r_j`, defined by the same recursion as `H_i` itself. -/
def hrank : ℕ → ℕ
  | 0 => 0
  | (i + 1) => hrank i + stageRank i

@[simp] theorem hrank_zero : hrank 0 = 0 := rfl

theorem hrank_succ (i : ℕ) : hrank (i + 1) = hrank i + stageRank i := rfl

/-- The manuscript's `rank H_i = r_i - 2`, stated without truncated subtraction. -/
theorem hrank_add_two (i : ℕ) : hrank i + 2 = stageRank i := by
  induction i with
  | zero => simp [stageRank]
  | succ i ih =>
      rw [hrank_succ, stageRank_succ]
      omega

/-- The manuscript's `dim_ℝ X_i = 2 r_i`: `X_i = S^4 × ∏_{j<i} ℂP^{r_j}` has real
dimension `4 + ∑_{j<i} 2 r_j`. -/
theorem realDim_baseX (i : ℕ) : 4 + 2 * hrank i = 2 * stageRank i := by
  have h := hrank_add_two i
  omega

/-- `Y_i = ∏_{j<i} ℂP^{r_j}`. -/
abbrev baseY (i : ℕ) := ∀ j : Fin i, CP (stageRank (j : ℕ))

/-- `X_i = S^4 × Y_i`. -/
abbrev baseX (i : ℕ) := ↥sphereFour × baseY i

/-- The coordinate projection `X_i → X_k` for `k ≤ i`, the manuscript's `π_{k,i}`. -/
def basePr {k i : ℕ} (h : k ≤ i) : C(baseX i, baseX k) :=
  ⟨fun w => (w.1, fun j => w.2 (Fin.castLE h j)), by
    refine Continuous.prodMk continuous_fst (continuous_pi fun j => ?_)
    exact (continuous_apply (Fin.castLE h j)).comp continuous_snd⟩

@[simp]
theorem basePr_apply {k i : ℕ} (h : k ≤ i) (w : baseX i) :
    basePr h w = (w.1, fun j => w.2 (Fin.castLE h j)) := rfl

theorem basePr_self (i : ℕ) : basePr (le_refl i) = ContinuousMap.id (baseX i) :=
  ContinuousMap.ext fun _ => rfl

theorem basePr_comp {k i m : ℕ} (h₁ : k ≤ i) (h₂ : i ≤ m) :
    (basePr h₁).comp (basePr h₂) = basePr (h₁.trans h₂) :=
  ContinuousMap.ext fun _ => rfl

/-- **The tower of base spaces is surjective**: every point of `X_k` is `π_{k,i}` of a
point of `X_i`.  This is what makes the connecting maps injective and what the dense
point sequence of `Analysis/LIXConnectingMapPoints.lean` needs. -/
theorem basePr_surjective {k i : ℕ} (h : k ≤ i) : Function.Surjective (basePr h) := by
  classical
  rintro ⟨w1, w2⟩
  refine ⟨⟨w1, fun j : Fin i =>
      if hj : (j : ℕ) < k then w2 ⟨(j : ℕ), hj⟩ else Classical.arbitrary _⟩, ?_⟩
  exact Prod.ext rfl (funext fun j => dif_pos j.2)

/-- `π_i : X_{i+1} → X_i`. -/
abbrev baseProj (i : ℕ) : C(baseX (i + 1), baseX i) := basePr (Nat.le_succ i)

/-! ### Index types

They are recursive in the stage, so that `EIdx (i+1)` splits as `EIdx i ⊕ NIdx i`
definitionally (up to the fixed associativity equivalence `eIdxSucc`). -/

/-- The new block at stage `i`: `r_i` copies of the ambient `ℂ^{r_i+1}` of `ℂP^{r_i}`. -/
abbrev NIdx (i : ℕ) : Type := Fin (stageRank i) × Fin (stageRank i + 1)

/-- The index set of `H_i = ⊕_{j<i} L_{j+1}^{⊕ r_j}`. -/
def HIdx : ℕ → Type
  | 0 => Empty
  | (i + 1) => HIdx i ⊕ NIdx i

instance instFintypeHIdx : (i : ℕ) → Fintype (HIdx i)
  | 0 => inferInstanceAs (Fintype Empty)
  | (i + 1) =>
      letI := instFintypeHIdx i
      inferInstanceAs (Fintype (HIdx i ⊕ NIdx i))

instance instDecidableEqHIdx : (i : ℕ) → DecidableEq (HIdx i)
  | 0 => inferInstanceAs (DecidableEq Empty)
  | (i + 1) =>
      letI := instDecidableEqHIdx i
      inferInstanceAs (DecidableEq (HIdx i ⊕ NIdx i))

theorem HIdx_succ (i : ℕ) : HIdx (i + 1) = (HIdx i ⊕ NIdx i) := rfl

/-- The index set of `E_i = 𝟏² ⊕ H_i`. -/
abbrev EIdx (i : ℕ) : Type := Fin 2 ⊕ HIdx i

/-- `E_{i+1}`'s index set is `E_i`'s plus the new block, by associativity of `⊕`. -/
def eIdxSucc (i : ℕ) : EIdx i ⊕ NIdx i ≃ EIdx (i + 1) :=
  Equiv.sumAssoc (Fin 2) (HIdx i) (NIdx i)

/-! ### The line bundles `L_{j+1}` pulled back to `X_i` -/

/-- The tautological line of the `j`-th projective factor, pulled back to `X_i`. -/
def lineProj (i : ℕ) (j : Fin i) :
    Matrix (Fin (stageRank (j : ℕ) + 1)) (Fin (stageRank (j : ℕ) + 1)) C(baseX i, ℂ) :=
  Matrix.of fun a b =>
    ⟨fun z => ((z.2 j : CP (stageRank (j : ℕ))) :
        Matrix (Fin (stageRank (j : ℕ) + 1)) (Fin (stageRank (j : ℕ) + 1)) ℂ) a b,
      (continuous_subtype_val.comp ((continuous_apply j).comp continuous_snd)).matrix_elem a b⟩

@[simp]
theorem matEval_lineProj (i : ℕ) (j : Fin i) (z : baseX i) :
    matEval z (lineProj i j) = taut (stageRank (j : ℕ)) (z.2 j) := by
  ext a b
  rfl

theorem isStarProjection_lineProj (i : ℕ) (j : Fin i) : IsStarProjection (lineProj i j) := by
  refine isStarProjection_of_forall_matEval fun z => ?_
  rw [matEval_lineProj]
  exact isStarProjection_taut _ _

theorem trace_lineProj (i : ℕ) (j : Fin i) : Matrix.trace (lineProj i j) = 1 := by
  refine ContinuousMap.ext fun z => ?_
  rw [← trace_matEval, matEval_lineProj, trace_taut]
  rfl

/-- `L_{i+1}`, the tautological line of the newest projective factor of `X_{i+1}`. -/
def newLine (i : ℕ) :
    Matrix (Fin (stageRank i + 1)) (Fin (stageRank i + 1)) C(baseX (i + 1), ℂ) :=
  lineProj (i + 1) (Fin.last i)

theorem isStarProjection_newLine (i : ℕ) : IsStarProjection (newLine i) :=
  isStarProjection_lineProj _ _

theorem trace_newLine (i : ℕ) : Matrix.trace (newLine i) = 1 :=
  trace_lineProj _ _

/-- The new block of `H_{i+1}`: `r_i` copies of `L_{i+1}`. -/
def newBlock (i : ℕ) : Matrix (NIdx i) (NIdx i) C(baseX (i + 1), ℂ) :=
  (1 : Matrix (Fin (stageRank i)) (Fin (stageRank i)) C(baseX (i + 1), ℂ)) ⊗ₖ newLine i

theorem isStarProjection_newBlock (i : ℕ) : IsStarProjection (newBlock i) :=
  isStarProjection_kronecker (IsStarProjection.one _) (isStarProjection_newLine i)

theorem trace_newBlock (i : ℕ) :
    Matrix.trace (newBlock i) = ((stageRank i : ℕ) : C(baseX (i + 1), ℂ)) := by
  rw [newBlock, Matrix.trace_kronecker, Matrix.trace_one, trace_newLine, mul_one,
    Fintype.card_fin]

/-! ### `H_i` and `E_i` -/

/-- `H_i = ⊕_{j<i} L_{j+1}^{⊕ r_j}`, built by the recursion
`H_{i+1} = π_i^* H_i ⊕ L_{i+1}^{⊕ r_i}`. -/
def Hproj : (i : ℕ) → Matrix (HIdx i) (HIdx i) C(baseX i, ℂ)
  | 0 => 0
  | (i + 1) =>
      Matrix.fromBlocks (pullMat (baseProj i) (Hproj i)) 0 0 (newBlock i)

theorem Hproj_zero : Hproj 0 = 0 := rfl

theorem Hproj_succ (i : ℕ) : Hproj (i + 1) =
    Matrix.fromBlocks (pullMat (baseProj i) (Hproj i)) 0 0 (newBlock i) := rfl

/-- `E_i = 𝟏² ⊕ H_i`. -/
def Eproj (i : ℕ) : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ) :=
  Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) C(baseX i, ℂ)) 0 0 (Hproj i)

theorem Eproj_def (i : ℕ) : Eproj i =
    Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) C(baseX i, ℂ)) 0 0 (Hproj i) := rfl

theorem isStarProjection_Hproj : ∀ i, IsStarProjection (Hproj i)
  | 0 => IsStarProjection.zero _
  | (i + 1) => by
      rw [Hproj_succ]
      exact isStarProjection_fromBlocks_diag
        (isStarProjection_pullMat _ (isStarProjection_Hproj i)) (isStarProjection_newBlock i)

theorem isStarProjection_Eproj (i : ℕ) : IsStarProjection (Eproj i) :=
  Eproj_def i ▸ isStarProjection_fromBlocks_diag (IsStarProjection.one _)
    (isStarProjection_Hproj i)

/-- **`rank H_i = r_i - 2`**, in the untruncated form `trace H_i = ∑_{j<i} r_j`. -/
theorem trace_Hproj : ∀ i : ℕ,
    Matrix.trace (Hproj i) = ((hrank i : ℕ) : C(baseX i, ℂ))
  | 0 => by rw [Hproj_zero, Matrix.trace_zero, hrank_zero, Nat.cast_zero]
  | (i + 1) => by
      have hblocks : Matrix.trace (Hproj (i + 1))
          = Matrix.trace (pullMat (baseProj i) (Hproj i)) + Matrix.trace (newBlock i) :=
        trace_fromBlocks _ _ _ _
      have hpull : Matrix.trace (pullMat (baseProj i) (Hproj i))
          = ((hrank i : ℕ) : C(baseX (i + 1), ℂ)) := by
        refine ContinuousMap.ext fun w => ?_
        rw [← trace_matEval, matEval_pullMat, trace_matEval, trace_Hproj i]
        rw [ContinuousMap.natCast_apply, ContinuousMap.natCast_apply]
      rw [hblocks, hpull, trace_newBlock, hrank_succ]
      push_cast
      ring

/-- **`rank E_i = r_i`.** -/
theorem trace_Eproj (i : ℕ) :
    Matrix.trace (Eproj i) = ((stageRank i : ℕ) : C(baseX i, ℂ)) := by
  rw [Eproj_def, trace_fromBlocks, Matrix.trace_one, trace_Hproj, Fintype.card_fin,
    ← hrank_add_two i]
  push_cast
  ring

/-- The pointwise form of `rank E_i = r_i`, which is what the frame construction
(`STW59.exists_frame`) consumes. -/
theorem trace_matEval_Eproj (i : ℕ) (w : baseX i) :
    (matEval w (Eproj i)).trace = ((stageRank i : ℕ) : ℂ) := by
  rw [trace_matEval, trace_Eproj, ContinuousMap.natCast_apply]

/-- **`E_i` is not the zero projection**, since its rank `r_i` is positive and `X_i` is
nonempty.  This is what makes the stage algebra `A_i` nontrivial. -/
theorem Eproj_ne_zero (i : ℕ) : Eproj i ≠ 0 := by
  intro h
  have ht : Matrix.trace (Eproj i) = ((stageRank i : ℕ) : C(baseX i, ℂ)) := trace_Eproj i
  rw [h, Matrix.trace_zero] at ht
  obtain ⟨w⟩ : Nonempty (baseX i) := inferInstance
  have hw := congrArg (fun f : C(baseX i, ℂ) => f w) ht
  rw [ContinuousMap.zero_apply, ContinuousMap.natCast_apply] at hw
  have hz : stageRank i = 0 := by exact_mod_cast hw.symm
  exact (stageRank_pos i).ne' hz

/-! ### The stage decomposition `E_{i+1} = π_i^* E_i ⊕ (𝟏_{r_i} ⊗ L_{i+1})` -/

/-- **The manuscript's global bundle decomposition**
`E_{i+1} ≅ π_i^* E_i ⊕ (E_i(x_i) ⊗ L_{i+1})`, with `E_i(x_i) ⊗ L_{i+1}` written as
`𝟏_{r_i} ⊗ L_{i+1}` under the orthonormal identification `E_i(x_i) ≅ ℂ^{r_i}` of
`STW59.exists_frame`.  The equivalence is the fixed associativity reindexing
`STW59.eIdxSucc`; no unitary is involved. -/
theorem Eproj_succ (i : ℕ) :
    Eproj (i + 1) = Matrix.reindex (eIdxSucc i) (eIdxSucc i)
      (Matrix.fromBlocks (pullMat (baseProj i) (Eproj i)) 0 0 (newBlock i)) := by
  rw [Eproj_def, Eproj_def, Hproj_succ, pullMat_fromBlocks, pullMat_one, pullMat_zero,
    pullMat_zero]
  ext a b
  rcases a with a | (a | a) <;> rcases b with b | (b | b) <;> rfl

/-! ### The `Y`-level form of `H_i`

Lemma 2 lives over `S⁵ × Y_i`, not over `X_i = S⁴ × Y_i`, so the topology lanes need `H_i`
as a projection over `Y_i` alone, to be pulled back along whatever map into `Y_i` the
situation provides (`prY : C(↥sphereFive × baseY i, baseY i)` for Lemma 2 itself).
`HprojY` is that projection and `Hproj_eq_pullMat` identifies it with `Hproj`; the two run
the same block recursion, so nothing has to be proved twice. -/

/-- The projection `X_i → Y_i`. -/
def baseYproj (i : ℕ) : C(baseX i, baseY i) := ⟨Prod.snd, continuous_snd⟩

/-- The truncation `Y_{i+1} → Y_i`. -/
def baseYtrunc (i : ℕ) : C(baseY (i + 1), baseY i) :=
  ⟨fun y j => y (Fin.castSucc j), continuous_pi fun j => continuous_apply (Fin.castSucc j)⟩

theorem baseYproj_comp_baseProj (i : ℕ) :
    (baseYproj i).comp (baseProj i) = (baseYtrunc i).comp (baseYproj (i + 1)) := rfl

/-- The tautological line of the `j`-th projective factor, over `Y_i`. -/
def lineProjY (i : ℕ) (j : Fin i) :
    Matrix (Fin (stageRank (j : ℕ) + 1)) (Fin (stageRank (j : ℕ) + 1)) C(baseY i, ℂ) :=
  Matrix.of fun a b =>
    ⟨fun y => ((y j : CP (stageRank (j : ℕ))) :
        Matrix (Fin (stageRank (j : ℕ) + 1)) (Fin (stageRank (j : ℕ) + 1)) ℂ) a b,
      (continuous_subtype_val.comp (continuous_apply j)).matrix_elem a b⟩

theorem lineProj_eq_pullMat (i : ℕ) (j : Fin i) :
    lineProj i j = pullMat (baseYproj i) (lineProjY i j) := rfl

@[simp]
theorem matEval_lineProjY (i : ℕ) (j : Fin i) (y : baseY i) :
    matEval y (lineProjY i j) = taut (stageRank (j : ℕ)) (y j) := by
  ext a b
  rfl

theorem isStarProjection_lineProjY (i : ℕ) (j : Fin i) :
    IsStarProjection (lineProjY i j) := by
  refine isStarProjection_of_forall_matEval fun y => ?_
  rw [matEval_lineProjY]
  exact isStarProjection_taut _ _

theorem trace_lineProjY (i : ℕ) (j : Fin i) : Matrix.trace (lineProjY i j) = 1 := by
  refine ContinuousMap.ext fun y => ?_
  rw [← trace_matEval, matEval_lineProjY, trace_taut]
  rfl

/-- `L_{i+1}` over `Y_{i+1}`. -/
def newLineY (i : ℕ) :
    Matrix (Fin (stageRank i + 1)) (Fin (stageRank i + 1)) C(baseY (i + 1), ℂ) :=
  lineProjY (i + 1) (Fin.last i)

theorem newLine_eq_pullMat (i : ℕ) :
    newLine i = pullMat (baseYproj (i + 1)) (newLineY i) := rfl

theorem isStarProjection_newLineY (i : ℕ) : IsStarProjection (newLineY i) :=
  isStarProjection_lineProjY _ _

theorem trace_newLineY (i : ℕ) : Matrix.trace (newLineY i) = 1 :=
  trace_lineProjY _ _

/-- `L_{i+1}^{⊕ r_i}` over `Y_{i+1}`. -/
def newBlockY (i : ℕ) : Matrix (NIdx i) (NIdx i) C(baseY (i + 1), ℂ) :=
  (1 : Matrix (Fin (stageRank i)) (Fin (stageRank i)) C(baseY (i + 1), ℂ)) ⊗ₖ newLineY i

theorem isStarProjection_newBlockY (i : ℕ) : IsStarProjection (newBlockY i) :=
  isStarProjection_kronecker (IsStarProjection.one _) (isStarProjection_newLineY i)

theorem newBlock_eq_pullMat (i : ℕ) :
    newBlock i = pullMat (baseYproj (i + 1)) (newBlockY i) := by
  rw [newBlock, newBlockY, pullMat_kronecker, pullMat_one, newLine_eq_pullMat]

/-- **`H_i` as a projection over `Y_i` alone.** -/
def HprojY : (i : ℕ) → Matrix (HIdx i) (HIdx i) C(baseY i, ℂ)
  | 0 => 0
  | (i + 1) =>
      Matrix.fromBlocks (pullMat (baseYtrunc i) (HprojY i)) 0 0 (newBlockY i)

theorem HprojY_zero : HprojY 0 = 0 := rfl

theorem HprojY_succ (i : ℕ) : HprojY (i + 1) =
    Matrix.fromBlocks (pullMat (baseYtrunc i) (HprojY i)) 0 0 (newBlockY i) := rfl

theorem isStarProjection_HprojY : ∀ i, IsStarProjection (HprojY i)
  | 0 => IsStarProjection.zero _
  | (i + 1) => by
      rw [HprojY_succ]
      exact isStarProjection_fromBlocks_diag
        (isStarProjection_pullMat _ (isStarProjection_HprojY i)) (isStarProjection_newBlockY i)

theorem trace_HprojY : ∀ i : ℕ,
    Matrix.trace (HprojY i) = ((hrank i : ℕ) : C(baseY i, ℂ))
  | 0 => by rw [HprojY_zero, Matrix.trace_zero, hrank_zero, Nat.cast_zero]
  | (i + 1) => by
      have hblocks : Matrix.trace (HprojY (i + 1))
          = Matrix.trace (pullMat (baseYtrunc i) (HprojY i)) + Matrix.trace (newBlockY i) :=
        trace_fromBlocks _ _ _ _
      have hpull : Matrix.trace (pullMat (baseYtrunc i) (HprojY i))
          = ((hrank i : ℕ) : C(baseY (i + 1), ℂ)) := by
        refine ContinuousMap.ext fun y => ?_
        rw [← trace_matEval, matEval_pullMat, trace_matEval, trace_HprojY i]
        rw [ContinuousMap.natCast_apply, ContinuousMap.natCast_apply]
      have hnew : Matrix.trace (newBlockY i) = ((stageRank i : ℕ) : C(baseY (i + 1), ℂ)) := by
        rw [newBlockY, Matrix.trace_kronecker, Matrix.trace_one, trace_newLineY, mul_one,
          Fintype.card_fin]
      rw [hblocks, hpull, hnew, hrank_succ]
      push_cast
      ring

/-- **`H_i` does not see the `S^4` factor**: it is pulled back from `Y_i`. -/
theorem Hproj_eq_pullMat : ∀ i : ℕ, Hproj i = pullMat (baseYproj i) (HprojY i)
  | 0 => by rw [Hproj_zero, HprojY_zero, pullMat_zero]
  | (i + 1) => by
      have key : pullMat (baseYproj (i + 1)) (HprojY (i + 1))
          = Matrix.fromBlocks
              (pullMat (baseYproj (i + 1)) (pullMat (baseYtrunc i) (HprojY i)))
              (pullMat (baseYproj (i + 1)) (0 : Matrix (HIdx i) (NIdx i) C(baseY (i + 1), ℂ)))
              (pullMat (baseYproj (i + 1)) (0 : Matrix (NIdx i) (HIdx i) C(baseY (i + 1), ℂ)))
              (pullMat (baseYproj (i + 1)) (newBlockY i)) :=
        pullMat_fromBlocks _ _ _ _ _
      rw [Hproj_succ, key, pullMat_zero, pullMat_zero, ← newBlock_eq_pullMat,
        Hproj_eq_pullMat i, pullMat_comp, baseYproj_comp_baseProj, ← pullMat_comp]

/-! ### The stage unitaries `w_i = u ⊕ 𝟏_{H_i}`

The manuscript's §6 clutches `u`, the generator over `S^4`, with the identity of `H_i`.
This is the block-sum vocabulary lane `cs-clutching` asked for: `blockUnitary i u` is `w_i`,
it lies in the corner cut out by `E_i` (`blockUnitary_mem_corner`, so it is an element of the
stage algebra `A_i`), and it is a unitary of that corner — meaning `w* w = w w* = E_i` — as
soon as `u` is a unitary of `M₂(C(X_i))`. -/

/-- Multiplication of two block-diagonal matrices.  Also used by
`Analysis/LIXConnectingMap.lean`; do not restate it there. -/
theorem fromBlocks_diag_mul {l n R : Type*} [Fintype l] [Fintype n] [Semiring R]
    (A A' : Matrix l l R) (D D' : Matrix n n R) :
    Matrix.fromBlocks A 0 0 D * Matrix.fromBlocks A' 0 0 D'
      = Matrix.fromBlocks (A * A') 0 0 (D * D') := by
  rw [Matrix.fromBlocks_multiply]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp

/-- **`w_i = u ⊕ 𝟏_{H_i}`.** -/
def blockUnitary (i : ℕ) (u : Matrix (Fin 2) (Fin 2) C(baseX i, ℂ)) :
    Matrix (EIdx i) (EIdx i) C(baseX i, ℂ) :=
  Matrix.fromBlocks u 0 0 (Hproj i)

theorem blockUnitary_def (i : ℕ) (u : Matrix (Fin 2) (Fin 2) C(baseX i, ℂ)) :
    blockUnitary i u = Matrix.fromBlocks u 0 0 (Hproj i) := rfl

theorem conjTranspose_blockUnitary (i : ℕ) (u : Matrix (Fin 2) (Fin 2) C(baseX i, ℂ)) :
    (blockUnitary i u)ᴴ = Matrix.fromBlocks uᴴ 0 0 (Hproj i) := by
  rw [blockUnitary_def, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_zero, conjTranspose_eq_of_isStarProjection (isStarProjection_Hproj i)]

/-- `w_i` is a section of `End E_i`: it lies in the corner cut out by `E_i`. -/
theorem blockUnitary_mem_corner (i : ℕ) (u : Matrix (Fin 2) (Fin 2) C(baseX i, ℂ)) :
    Eproj i * blockUnitary i u * Eproj i = blockUnitary i u := by
  rw [Eproj_def, blockUnitary_def, fromBlocks_diag_mul, fromBlocks_diag_mul,
    Matrix.one_mul, Matrix.mul_one, (isStarProjection_Hproj i).isIdempotentElem.eq,
    (isStarProjection_Hproj i).isIdempotentElem.eq]

/-- `w_i* w_i = E_i`: `w_i` is an isometry of the corner. -/
theorem blockUnitary_star_mul (i : ℕ) {u : Matrix (Fin 2) (Fin 2) C(baseX i, ℂ)}
    (hu : uᴴ * u = 1) : (blockUnitary i u)ᴴ * blockUnitary i u = Eproj i := by
  rw [conjTranspose_blockUnitary, blockUnitary_def, fromBlocks_diag_mul, hu,
    (isStarProjection_Hproj i).isIdempotentElem.eq, Eproj_def]

/-- `w_i w_i* = E_i`: `w_i` is a unitary of the corner. -/
theorem blockUnitary_mul_star (i : ℕ) {u : Matrix (Fin 2) (Fin 2) C(baseX i, ℂ)}
    (hu : u * uᴴ = 1) : blockUnitary i u * (blockUnitary i u)ᴴ = Eproj i := by
  rw [conjTranspose_blockUnitary, blockUnitary_def, fromBlocks_diag_mul, hu,
    (isStarProjection_Hproj i).isIdempotentElem.eq, Eproj_def]

/-- The unit `E_i` is `w_i` for `u = 1`. -/
theorem blockUnitary_one (i : ℕ) :
    blockUnitary i (1 : Matrix (Fin 2) (Fin 2) C(baseX i, ℂ)) = Eproj i := rfl

/-! ### `F` over `S^5 ⊂ ℂ³` -/

/-- The tautological column vector `x` over `S^5`. -/
def hopfCol : Matrix (Fin 3) (Fin 1) C(↥sphereFive, ℂ) :=
  Matrix.of fun a _ =>
    ⟨fun x => (x : Fin 3 → ℂ) a, (continuous_apply a).comp continuous_subtype_val⟩

@[simp]
theorem hopfCol_apply (a : Fin 3) (u : Fin 1) (x : ↥sphereFive) :
    hopfCol a u x = (x : Fin 3 → ℂ) a := rfl

/-- The tautological line `x xᴴ` over `S^5` (the pullback of the tautological line of
`ℂP²` along the Hopf map). -/
def hopfProj : Matrix (Fin 3) (Fin 3) C(↥sphereFive, ℂ) := hopfCol * hopfColᴴ

theorem hopfProj_def : hopfProj = hopfCol * hopfColᴴ := rfl

theorem matEval_hopfProj (x : ↥sphereFive) :
    matEval x hopfProj = rankOneProj ((x : Fin 3 → ℂ)) := by
  rw [hopfProj_def, matEval_mul, matEval_conjTranspose]
  ext a b
  rw [Matrix.mul_apply]
  simp [Matrix.conjTranspose_apply]

theorem isStarProjection_hopfProj : IsStarProjection hopfProj := by
  refine isStarProjection_of_forall_matEval fun x => ?_
  rw [matEval_hopfProj]
  exact isStarProjection_rankOneProj x.2

theorem hopfCol_conjTranspose_mul : hopfColᴴ * hopfCol = 1 := by
  refine matrix_ext_of_matEval fun x => ?_
  rw [matEval_mul, matEval_conjTranspose, matEval_one]
  ext u v
  rw [Matrix.mul_apply]
  have hterm : ∀ a : Fin 3,
      ((matEval x hopfCol)ᴴ) u a * (matEval x hopfCol) a v
        = star ((x : Fin 3 → ℂ) a) * (x : Fin 3 → ℂ) a := by
    intro a
    rw [Matrix.conjTranspose_apply]
    rfl
  rw [Finset.sum_congr rfl (fun a _ => hterm a), sum_star_mul_self x.2]
  have huv : u = v := Subsingleton.elim u v
  subst huv
  rw [Matrix.one_apply_eq]

theorem trace_hopfProj : Matrix.trace hopfProj = 1 := by
  refine ContinuousMap.ext fun x => ?_
  rw [← trace_matEval, matEval_hopfProj, trace_rankOneProj x.2]
  rfl

/-- **`F`**: the rank-two bundle `F_x = {w ∈ ℂ³ : ⟨w, x⟩ = 0}` over `S^5`, written as the
projection `x ↦ 1 - x xᴴ`. -/
def Fproj : Matrix (Fin 3) (Fin 3) C(↥sphereFive, ℂ) := 1 - hopfProj

theorem Fproj_def : Fproj = 1 - hopfProj := rfl

theorem isStarProjection_Fproj : IsStarProjection Fproj :=
  isStarProjection_hopfProj.one_sub

/-- `F` has rank two. -/
theorem trace_Fproj : Matrix.trace Fproj = 2 := by
  rw [Fproj_def, Matrix.trace_sub, Matrix.trace_one, trace_hopfProj, Fintype.card_fin]
  norm_num

theorem Fproj_mul_hopfCol : Fproj * hopfCol = 0 := by
  rw [Fproj_def, Matrix.sub_mul, Matrix.one_mul, hopfProj_def, Matrix.mul_assoc,
    hopfCol_conjTranspose_mul, Matrix.mul_one, sub_self]

theorem hopfCol_conjTranspose_mul_Fproj : hopfColᴴ * Fproj = 0 := by
  have h := congrArg Matrix.conjTranspose Fproj_mul_hopfCol
  rw [Matrix.conjTranspose_mul, conjTranspose_eq_of_isStarProjection isStarProjection_Fproj,
    Matrix.conjTranspose_zero] at h
  exact h

theorem hopfProj_add_Fproj : hopfProj + Fproj = 1 := by
  rw [Fproj_def]
  abel

/-- **`F ⊕ 𝟏 ≅ 𝟏³`**, the cancellation identity of the manuscript's §2, as a
Murray–von Neumann equivalence of projections in `M₄(C(S^5))`.

The implementer is the explicit partial isometry `[[F, x], [0, 0]]`. -/
theorem murrayVonNeumannEquiv_Fproj :
    MurrayVonNeumannEquiv
      (Matrix.fromBlocks Fproj 0 0 (1 : Matrix (Fin 1) (Fin 1) C(↥sphereFive, ℂ)))
      (Matrix.fromBlocks (1 : Matrix (Fin 3) (Fin 3) C(↥sphereFive, ℂ)) 0 0
        (0 : Matrix (Fin 1) (Fin 1) C(↥sphereFive, ℂ))) := by
  refine ⟨Matrix.fromBlocks Fproj hopfCol 0 0, ?_, ?_⟩
  · rw [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
      Matrix.conjTranspose_zero,
      conjTranspose_eq_of_isStarProjection isStarProjection_Fproj,
      Matrix.fromBlocks_multiply, isStarProjection_Fproj.isIdempotentElem.eq,
      Fproj_mul_hopfCol, hopfCol_conjTranspose_mul_Fproj, hopfCol_conjTranspose_mul]
    simp
  · have hkey : Fproj * Fproj + hopfCol * hopfColᴴ
        = (1 : Matrix (Fin 3) (Fin 3) C(↥sphereFive, ℂ)) := by
      rw [isStarProjection_Fproj.isIdempotentElem.eq, ← hopfProj_def, Fproj_def]
      abel
    rw [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
      Matrix.conjTranspose_zero,
      conjTranspose_eq_of_isStarProjection isStarProjection_Fproj,
      Matrix.fromBlocks_multiply, hkey]
    simp

/-! ### Rank is locally constant -/

/-- A continuous function with values in the natural numbers is locally constant. -/
theorem isLocallyConstant_of_natCast_valued {X : Type*} [TopologicalSpace X] {f : X → ℂ}
    (hf : Continuous f) (h : ∀ x, ∃ k : ℕ, f x = (k : ℂ)) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hnbhd : f ⁻¹' Metric.ball (f x) 1 ∈ nhds x :=
    hf.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ one_pos)
  filter_upwards [hnbhd] with y hy
  obtain ⟨k, hk⟩ := h x
  obtain ⟨l, hl⟩ := h y
  have hdist : ‖f y - f x‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hy
  rw [hk, hl] at hdist ⊢
  have hcast : ((l : ℂ) - (k : ℂ)) = (((l : ℝ) - (k : ℝ) : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs] at hdist
  have habs := abs_lt.mp hdist
  have hlk : (l : ℤ) = (k : ℤ) := by
    have h1 : (l : ℤ) - (k : ℤ) < 1 := by
      have hr : ((l : ℤ) : ℝ) - ((k : ℤ) : ℝ) < 1 := by push_cast; linarith [habs.2]
      exact_mod_cast hr
    have h2 : (-1 : ℤ) < (l : ℤ) - (k : ℤ) := by
      have hr : (-1 : ℝ) < ((l : ℤ) : ℝ) - ((k : ℤ) : ℝ) := by push_cast; linarith [habs.1]
      exact_mod_cast hr
    omega
  have hlk' : l = k := by exact_mod_cast hlk
  rw [hlk']

/-- **The rank of a projection-valued function is locally constant.**

Its rank at a point is the trace of the evaluated matrix, which is a natural number
(`STW59.exists_natCast_trace`) and depends continuously on the point. -/
theorem isLocallyConstant_trace {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    [DecidableEq ι] {M : Matrix ι ι C(X, ℂ)} (h : IsStarProjection M) :
    IsLocallyConstant fun x => (Matrix.trace M) x := by
  refine isLocallyConstant_of_natCast_valued (Matrix.trace M).continuous fun x => ?_
  obtain ⟨m, hm⟩ := exists_natCast_trace (isStarProjection_matEval h x)
  exact ⟨m, by rw [← trace_matEval, hm]⟩

end

end STW59
end GroupApproximation
