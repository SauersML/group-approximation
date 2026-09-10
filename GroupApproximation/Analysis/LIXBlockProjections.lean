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
rank-`n` bundle `F` over `S^{2n+1}` from §2.  Nothing here uses a vector-bundle library: a
bundle *is* a projection `p : Matrix ι ι C(X, ℂ)` and bundle isomorphism *is*
`GroupApproximation.MurrayVonNeumannEquiv`, as in
`GroupApproximation/KTheory/MatrixProjection.lean`.

## Two layers: generic in the rank, and the `n = 2` instance

The tower is built **generically in the rank `n`** in the namespace `STW59.Gen`
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.1), and the mod-2 program of
`notes/LIX_FULL_PROGRAM_2026-09-05.md` is its `n = 2` instance.  The second half of the
file pins the names the rest of the LIX closure is written against — `sphereFour`,
`stageRank`, `EIdx`, `Eproj`, `Fproj`, … — to `Gen.<same name> 2`, so nothing downstream
changes.  Each such declaration is the generic one applied at `2`; none of them has a
proof of its own.

The one arithmetic choice that makes this cost nothing: `Gen.stageRank n i = 2 ^ i * n`,
**not** `n * 2 ^ i`.  `Nat.pow` recurses on the exponent, so at `n = 2` the generic
`2 ^ i * 2` is *definitionally* the mod-2 program's `2 ^ (i + 1)`, and every `rfl`
downstream of the specialisation — `Analysis/LIXLemmaTwoProp.lean`'s `lixDD_apply` above
all, which about a hundred `CharClass` modules depend on — is unaffected.

## Model choices (other LIX lanes must match these exactly)

* `S^{2n} := STW59.Gen.sphereEven n = Metric.sphere (0 : EuclideanSpace ℝ (Fin (2n+1))) 1`,
  used as a subtype; at `n = 2` this is `STW59.sphereFour`.
* `S^{2n+1} ⊂ ℂ^{n+1} := STW59.Gen.sphereOdd n = STW59.unitVectors (Fin (n+1))`, a subset of
  the *plain* product space `Fin (n+1) → ℂ` cut out by `∑ i, ‖x i‖ ^ 2 = 1`.  **No
  `EuclideanSpace ℂ` and no `PiLp` anywhere**: coordinates are needed to write `x xᴴ`, and
  `PiLp` coordinate access has been an elaboration trap in this repo.  At `n = 2` this is
  `STW59.sphereFive`.
* `ℂP^d := STW59.CP d`, the matrix model of `Analysis/LIXProjectiveSpaceModel.lean`.
* Stage data: `r i = STW59.Gen.stageRank n i = 2 ^ i * n`,
  `Y i = STW59.Gen.baseY n i = ∀ j : Fin i, CP (r j)`,
  `X i = STW59.Gen.baseX n i = ↥(sphereEven n) × baseY n i`.
* Index types are **recursive in the stage**, so that the block decomposition used by the
  connecting maps of `Analysis/LIXConnectingMap.lean` is definitional:
  `Gen.NIdx n i = Fin (r i) × Fin (r i + 1)` (`r i` copies of the ambient `ℂ^{r i + 1}` of
  `CP^{r i}`), `Gen.HIdx n (i+1) = HIdx n i ⊕ NIdx n i` with `HIdx n 0 = Empty`, and
  `Gen.EIdx n i = Fin n ⊕ HIdx n i`.  Thus
  `EIdx n (i+1) = Fin n ⊕ (HIdx n i ⊕ NIdx n i)` is `Equiv.sumAssoc`-equivalent to
  `EIdx n i ⊕ NIdx n i` (`Gen.eIdxSucc`), and `Gen.Eproj_succ` says that under exactly
  that equivalence `E_{i+1} = π_i^* E_i ⊕ (𝟏_{r i} ⊗ L_{i+1})`.
* Coefficients live in `C(X i, ℂ)`, so the block assembly needs no continuity proof:
  `Matrix.fromBlocks` over a ring of continuous functions is continuous by construction.

## Main results

* `STW59.Gen.trace_Hproj`, `STW59.Gen.trace_Eproj`, `STW59.Gen.hrank_add_rank`,
  `STW59.Gen.realDim_baseX` — the manuscript's (4.2) at general rank: `rank H_i = r_i - n`,
  `rank E_i = r_i`, `dim_ℝ X_i = 2 r_i`.
* `STW59.Gen.dvd_stageRank` — every prime dividing `n` divides every stage rank.  This is
  the only property of the tower's shape that Step D of the stronger theorem uses.
* `STW59.Gen.Eproj_succ` — the manuscript's global bundle decomposition
  `E_{i+1} ≅ π_i^* E_i ⊕ (E_i(x_i) ⊗ L_{i+1})`, in the form in which the connecting map
  uses it.
* `STW59.exists_frame` — a star projection of trace `k` over `ℂ` is `s sᴴ` for an
  isometry `s : ℂ^k → ℂ^n`; this is the manuscript's "choose an orthonormal
  identification `E_i(x_i) ≅ ℂ^{r_i}`".
* `STW59.Gen.murrayVonNeumannEquiv_Fproj` — `F ⊕ 𝟏 ≅ 𝟏^{n+1}` over `S^{2n+1}`.
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

/-- Multiplication of two block-diagonal matrices.  Also used by
`Analysis/LIXConnectingMap.lean`; do not restate it there. -/
theorem fromBlocks_diag_mul {l n R : Type*} [Fintype l] [Fintype n] [Semiring R]
    (A A' : Matrix l l R) (D D' : Matrix n n R) :
    Matrix.fromBlocks A 0 0 D * Matrix.fromBlocks A' 0 0 D'
      = Matrix.fromBlocks (A * A') 0 0 (D * D') := by
  rw [Matrix.fromBlocks_multiply]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp

/-! ### The base spheres, generic in the rank `n`

`Gen.sphereEven n = S^{2n}` is the equator sphere the tower is built over, and
`Gen.sphereOdd n = S^{2n+1} ⊂ ℂ^{n+1}` is the sphere the rank-`n` bundle `F` of §2 lives
over.  At `n = 2` they are the `S⁴` and `S⁵` of the mod-2 program, and the `n = 2` section
at the end of this file pins the old names `sphereFour`/`sphereFive` to them. -/

namespace Gen

/-- `S^{2n}`, the unit sphere of `ℝ^{2n+1}`. -/
abbrev sphereEven (n : ℕ) : Set (EuclideanSpace ℝ (Fin (2 * n + 1))) := Metric.sphere 0 1

/-- `S^{2n+1}`, the unit sphere of `ℂ^{n+1}` inside the *plain* product space
`Fin (n+1) → ℂ`.  No `EuclideanSpace ℂ` and no `PiLp` anywhere. -/
abbrev sphereOdd (n : ℕ) : Set (Fin (n + 1) → ℂ) := unitVectors (Fin (n + 1))

instance sphereOdd.instCompactSpace (n : ℕ) : CompactSpace ↥(sphereOdd n) :=
  isCompact_iff_compactSpace.mp (isCompact_unitVectors (Fin (n + 1)))

instance sphereOdd.instNonempty (n : ℕ) : Nonempty ↥(sphereOdd n) := by
  classical
  refine ⟨⟨fun i : Fin (n + 1) => if i = 0 then (1 : ℂ) else 0, ?_⟩⟩
  show (∑ i : Fin (n + 1), ‖(if i = 0 then (1 : ℂ) else 0)‖ ^ 2) = 1
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin (n + 1))) h

instance sphereEven.instCompactSpace (n : ℕ) : CompactSpace ↥(sphereEven n) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : EuclideanSpace ℝ (Fin (2 * n + 1))) 1)

instance sphereEven.instNonempty (n : ℕ) : Nonempty ↥(sphereEven n) :=
  Set.Nonempty.to_subtype (NormedSpace.sphere_nonempty.mpr zero_le_one)

/-! ### Stage data -/

/-- `r_i = n · 2^i`, the rank of `E_i` in the manuscript's (4.1), generic in `n`.

Written `2 ^ i * n` and **not** `n * 2 ^ i`: `Nat.pow` recurses on the exponent, so
`2 ^ i * n` at `n = 2` is *definitionally* the mod-2 program's `2 ^ (i + 1)`, and every
`rfl` downstream of the `n = 2` specialisation survives unchanged. -/
def stageRank (n i : ℕ) : ℕ := 2 ^ i * n

@[simp] theorem stageRank_zero (n : ℕ) : stageRank n 0 = n := by simp [stageRank]

theorem stageRank_pos (n i : ℕ) [NeZero n] : 0 < stageRank n i :=
  mul_pos (pow_pos (by norm_num) i) (Nat.pos_of_ne_zero (NeZero.ne n))

theorem stageRank_succ (n i : ℕ) : stageRank n (i + 1) = 2 * stageRank n i := by
  unfold stageRank
  rw [pow_succ]
  ring

/-- **Every prime dividing `n` divides every stage rank.**  This is the only place the
shape of the tower enters Step D of the stronger theorem (`§1.1` of
`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`), and it is immediate from `r_i = 2^i · n`. -/
theorem dvd_stageRank {p n : ℕ} (h : p ∣ n) (i : ℕ) : p ∣ stageRank n i :=
  h.mul_left _

/-- `rank H_i = ∑_{j<i} r_j`, defined by the same recursion as `H_i` itself. -/
def hrank (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | (i + 1) => hrank n i + stageRank n i

@[simp] theorem hrank_zero (n : ℕ) : hrank n 0 = 0 := rfl

theorem hrank_succ (n i : ℕ) : hrank n (i + 1) = hrank n i + stageRank n i := rfl

/-- The manuscript's `rank H_i = r_i - n`, stated without truncated subtraction. -/
theorem hrank_add_rank (n i : ℕ) : hrank n i + n = stageRank n i := by
  induction i with
  | zero => simp [stageRank, hrank]
  | succ i ih =>
      rw [hrank_succ, stageRank_succ]
      omega

/-- The manuscript's `dim_ℝ X_i = 2 r_i`: `X_i = S^{2n} × ∏_{j<i} ℂP^{r_j}` has real
dimension `2n + ∑_{j<i} 2 r_j`. -/
theorem realDim_baseX (n i : ℕ) : 2 * n + 2 * hrank n i = 2 * stageRank n i := by
  have h := hrank_add_rank n i
  omega

/-- `Y_i = ∏_{j<i} ℂP^{r_j}`. -/
abbrev baseY (n i : ℕ) := ∀ j : Fin i, CP (stageRank n (j : ℕ))

/-- `X_i = S^{2n} × Y_i`. -/
abbrev baseX (n i : ℕ) := ↥(sphereEven n) × baseY n i

/-- The coordinate projection `X_i → X_k` for `k ≤ i`, the manuscript's `π_{k,i}`. -/
def basePr (n : ℕ) {k i : ℕ} (h : k ≤ i) : C(baseX n i, baseX n k) :=
  ⟨fun w => (w.1, fun j => w.2 (Fin.castLE h j)), by
    refine Continuous.prodMk continuous_fst (continuous_pi fun j => ?_)
    exact (continuous_apply (Fin.castLE h j)).comp continuous_snd⟩

@[simp]
theorem basePr_apply (n : ℕ) {k i : ℕ} (h : k ≤ i) (w : baseX n i) :
    basePr n h w = (w.1, fun j => w.2 (Fin.castLE h j)) := rfl

theorem basePr_self (n i : ℕ) : basePr n (le_refl i) = ContinuousMap.id (baseX n i) :=
  ContinuousMap.ext fun _ => rfl

theorem basePr_comp (n : ℕ) {k i m : ℕ} (h₁ : k ≤ i) (h₂ : i ≤ m) :
    (basePr n h₁).comp (basePr n h₂) = basePr n (h₁.trans h₂) :=
  ContinuousMap.ext fun _ => rfl

/-- **The tower of base spaces is surjective**: every point of `X_k` is `π_{k,i}` of a
point of `X_i`. -/
theorem basePr_surjective (n : ℕ) {k i : ℕ} (h : k ≤ i) :
    Function.Surjective (basePr n h) := by
  classical
  rintro ⟨w1, w2⟩
  refine ⟨⟨w1, fun j : Fin i =>
      if hj : (j : ℕ) < k then w2 ⟨(j : ℕ), hj⟩ else Classical.arbitrary _⟩, ?_⟩
  exact Prod.ext rfl (funext fun j => dif_pos j.2)

/-- `π_i : X_{i+1} → X_i`. -/
abbrev baseProj (n i : ℕ) : C(baseX n (i + 1), baseX n i) := basePr n (Nat.le_succ i)

/-! ### Index types -/

/-- The new block at stage `i`: `r_i` copies of the ambient `ℂ^{r_i+1}` of `ℂP^{r_i}`. -/
abbrev NIdx (n i : ℕ) : Type := Fin (stageRank n i) × Fin (stageRank n i + 1)

/-- The index set of `H_i = ⊕_{j<i} L_{j+1}^{⊕ r_j}`. -/
def HIdx (n : ℕ) : ℕ → Type
  | 0 => Empty
  | (i + 1) => HIdx n i ⊕ NIdx n i

instance instFintypeHIdx (n : ℕ) : (i : ℕ) → Fintype (HIdx n i)
  | 0 => inferInstanceAs (Fintype Empty)
  | (i + 1) =>
      letI := instFintypeHIdx n i
      inferInstanceAs (Fintype (HIdx n i ⊕ NIdx n i))

instance instDecidableEqHIdx (n : ℕ) : (i : ℕ) → DecidableEq (HIdx n i)
  | 0 => inferInstanceAs (DecidableEq Empty)
  | (i + 1) =>
      letI := instDecidableEqHIdx n i
      inferInstanceAs (DecidableEq (HIdx n i ⊕ NIdx n i))

theorem HIdx_succ (n i : ℕ) : HIdx n (i + 1) = (HIdx n i ⊕ NIdx n i) := rfl

/-- The index set of `E_i = 𝟏^n ⊕ H_i`. -/
abbrev EIdx (n i : ℕ) : Type := Fin n ⊕ HIdx n i

/-- `E_{i+1}`'s index set is `E_i`'s plus the new block, by associativity of `⊕`. -/
def eIdxSucc (n i : ℕ) : EIdx n i ⊕ NIdx n i ≃ EIdx n (i + 1) :=
  Equiv.sumAssoc (Fin n) (HIdx n i) (NIdx n i)

/-! ### The line bundles `L_{j+1}` pulled back to `X_i` -/

/-- The tautological line of the `j`-th projective factor, pulled back to `X_i`. -/
def lineProj (n i : ℕ) (j : Fin i) :
    Matrix (Fin (stageRank n (j : ℕ) + 1)) (Fin (stageRank n (j : ℕ) + 1))
      C(baseX n i, ℂ) :=
  Matrix.of fun a b =>
    ⟨fun z => ((z.2 j : CP (stageRank n (j : ℕ))) :
        Matrix (Fin (stageRank n (j : ℕ) + 1)) (Fin (stageRank n (j : ℕ) + 1)) ℂ) a b,
      (continuous_subtype_val.comp ((continuous_apply j).comp continuous_snd)).matrix_elem a b⟩

@[simp]
theorem matEval_lineProj (n i : ℕ) (j : Fin i) (z : baseX n i) :
    matEval z (lineProj n i j) = taut (stageRank n (j : ℕ)) (z.2 j) := by
  ext a b
  rfl

theorem isStarProjection_lineProj (n i : ℕ) (j : Fin i) :
    IsStarProjection (lineProj n i j) := by
  refine isStarProjection_of_forall_matEval fun z => ?_
  rw [matEval_lineProj]
  exact isStarProjection_taut _ _

theorem trace_lineProj (n i : ℕ) (j : Fin i) : Matrix.trace (lineProj n i j) = 1 := by
  refine ContinuousMap.ext fun z => ?_
  rw [← trace_matEval, matEval_lineProj, trace_taut]
  rfl

/-- `L_{i+1}`, the tautological line of the newest projective factor of `X_{i+1}`. -/
def newLine (n i : ℕ) :
    Matrix (Fin (stageRank n i + 1)) (Fin (stageRank n i + 1)) C(baseX n (i + 1), ℂ) :=
  lineProj n (i + 1) (Fin.last i)

theorem isStarProjection_newLine (n i : ℕ) : IsStarProjection (newLine n i) :=
  isStarProjection_lineProj _ _ _

theorem trace_newLine (n i : ℕ) : Matrix.trace (newLine n i) = 1 :=
  trace_lineProj _ _ _

/-- The new block of `H_{i+1}`: `r_i` copies of `L_{i+1}`. -/
def newBlock (n i : ℕ) : Matrix (NIdx n i) (NIdx n i) C(baseX n (i + 1), ℂ) :=
  (1 : Matrix (Fin (stageRank n i)) (Fin (stageRank n i)) C(baseX n (i + 1), ℂ))
    ⊗ₖ newLine n i

theorem isStarProjection_newBlock (n i : ℕ) : IsStarProjection (newBlock n i) :=
  isStarProjection_kronecker (IsStarProjection.one _) (isStarProjection_newLine n i)

theorem trace_newBlock (n i : ℕ) :
    Matrix.trace (newBlock n i) = ((stageRank n i : ℕ) : C(baseX n (i + 1), ℂ)) := by
  rw [newBlock, Matrix.trace_kronecker, Matrix.trace_one, trace_newLine, mul_one,
    Fintype.card_fin]

/-! ### `H_i` and `E_i` -/

/-- `H_i = ⊕_{j<i} L_{j+1}^{⊕ r_j}`, built by the recursion
`H_{i+1} = π_i^* H_i ⊕ L_{i+1}^{⊕ r_i}`. -/
def Hproj (n : ℕ) : (i : ℕ) → Matrix (HIdx n i) (HIdx n i) C(baseX n i, ℂ)
  | 0 => 0
  | (i + 1) =>
      Matrix.fromBlocks (pullMat (baseProj n i) (Hproj n i)) 0 0 (newBlock n i)

theorem Hproj_zero (n : ℕ) : Hproj n 0 = 0 := rfl

theorem Hproj_succ (n i : ℕ) : Hproj n (i + 1) =
    Matrix.fromBlocks (pullMat (baseProj n i) (Hproj n i)) 0 0 (newBlock n i) := rfl

/-- `E_i = 𝟏^n ⊕ H_i`. -/
def Eproj (n i : ℕ) : Matrix (EIdx n i) (EIdx n i) C(baseX n i, ℂ) :=
  Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(baseX n i, ℂ)) 0 0 (Hproj n i)

theorem Eproj_def (n i : ℕ) : Eproj n i =
    Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(baseX n i, ℂ)) 0 0 (Hproj n i) := rfl

theorem isStarProjection_Hproj (n : ℕ) : ∀ i, IsStarProjection (Hproj n i)
  | 0 => IsStarProjection.zero _
  | (i + 1) => by
      rw [Hproj_succ]
      exact isStarProjection_fromBlocks_diag
        (isStarProjection_pullMat _ (isStarProjection_Hproj n i))
        (isStarProjection_newBlock n i)

theorem isStarProjection_Eproj (n i : ℕ) : IsStarProjection (Eproj n i) :=
  Eproj_def n i ▸ isStarProjection_fromBlocks_diag (IsStarProjection.one _)
    (isStarProjection_Hproj n i)

/-- **`rank H_i = r_i - n`**, in the untruncated form `trace H_i = ∑_{j<i} r_j`. -/
theorem trace_Hproj (n : ℕ) : ∀ i : ℕ,
    Matrix.trace (Hproj n i) = ((hrank n i : ℕ) : C(baseX n i, ℂ))
  | 0 => by rw [Hproj_zero, Matrix.trace_zero, hrank_zero, Nat.cast_zero]
  | (i + 1) => by
      have hblocks : Matrix.trace (Hproj n (i + 1))
          = Matrix.trace (pullMat (baseProj n i) (Hproj n i))
            + Matrix.trace (newBlock n i) :=
        trace_fromBlocks _ _ _ _
      have hpull : Matrix.trace (pullMat (baseProj n i) (Hproj n i))
          = ((hrank n i : ℕ) : C(baseX n (i + 1), ℂ)) := by
        refine ContinuousMap.ext fun w => ?_
        rw [← trace_matEval, matEval_pullMat, trace_matEval, trace_Hproj n i]
        rw [ContinuousMap.natCast_apply, ContinuousMap.natCast_apply]
      rw [hblocks, hpull, trace_newBlock, hrank_succ]
      push_cast
      ring

/-- **`rank E_i = r_i`.** -/
theorem trace_Eproj (n i : ℕ) :
    Matrix.trace (Eproj n i) = ((stageRank n i : ℕ) : C(baseX n i, ℂ)) := by
  rw [Eproj_def, trace_fromBlocks, Matrix.trace_one, trace_Hproj, Fintype.card_fin,
    ← hrank_add_rank n i]
  push_cast
  ring

/-- The pointwise form of `rank E_i = r_i`, which is what the frame construction
(`STW59.exists_frame`) consumes. -/
theorem trace_matEval_Eproj (n i : ℕ) (w : baseX n i) :
    (matEval w (Eproj n i)).trace = ((stageRank n i : ℕ) : ℂ) := by
  rw [trace_matEval, trace_Eproj, ContinuousMap.natCast_apply]

/-- **`E_i` is not the zero projection**, since its rank `r_i` is positive (`n ≠ 0`) and
`X_i` is nonempty.  This is what makes the stage algebra `A_i` nontrivial. -/
theorem Eproj_ne_zero (n i : ℕ) [NeZero n] : Eproj n i ≠ 0 := by
  intro h
  have ht : Matrix.trace (Eproj n i) = ((stageRank n i : ℕ) : C(baseX n i, ℂ)) :=
    trace_Eproj n i
  rw [h, Matrix.trace_zero] at ht
  obtain ⟨w⟩ : Nonempty (baseX n i) := inferInstance
  have hw := congrArg (fun f : C(baseX n i, ℂ) => f w) ht
  rw [ContinuousMap.zero_apply, ContinuousMap.natCast_apply] at hw
  have hz : stageRank n i = 0 := by exact_mod_cast hw.symm
  exact (stageRank_pos n i).ne' hz

/-- **The manuscript's global bundle decomposition**
`E_{i+1} ≅ π_i^* E_i ⊕ (E_i(x_i) ⊗ L_{i+1})`. -/
theorem Eproj_succ (n i : ℕ) :
    Eproj n (i + 1) = Matrix.reindex (eIdxSucc n i) (eIdxSucc n i)
      (Matrix.fromBlocks (pullMat (baseProj n i) (Eproj n i)) 0 0 (newBlock n i)) := by
  rw [Eproj_def, Eproj_def, Hproj_succ, pullMat_fromBlocks, pullMat_one, pullMat_zero,
    pullMat_zero]
  ext a b
  rcases a with a | (a | a) <;> rcases b with b | (b | b) <;> rfl

/-! ### The `Y`-level form of `H_i` -/

/-- The projection `X_i → Y_i`. -/
def baseYproj (n i : ℕ) : C(baseX n i, baseY n i) := ⟨Prod.snd, continuous_snd⟩

/-- The truncation `Y_{i+1} → Y_i`. -/
def baseYtrunc (n i : ℕ) : C(baseY n (i + 1), baseY n i) :=
  ⟨fun y j => y (Fin.castSucc j), continuous_pi fun j => continuous_apply (Fin.castSucc j)⟩

theorem baseYproj_comp_baseProj (n i : ℕ) :
    (baseYproj n i).comp (baseProj n i) = (baseYtrunc n i).comp (baseYproj n (i + 1)) := rfl

/-- The tautological line of the `j`-th projective factor, over `Y_i`. -/
def lineProjY (n i : ℕ) (j : Fin i) :
    Matrix (Fin (stageRank n (j : ℕ) + 1)) (Fin (stageRank n (j : ℕ) + 1))
      C(baseY n i, ℂ) :=
  Matrix.of fun a b =>
    ⟨fun y => ((y j : CP (stageRank n (j : ℕ))) :
        Matrix (Fin (stageRank n (j : ℕ) + 1)) (Fin (stageRank n (j : ℕ) + 1)) ℂ) a b,
      (continuous_subtype_val.comp (continuous_apply j)).matrix_elem a b⟩

theorem lineProj_eq_pullMat (n i : ℕ) (j : Fin i) :
    lineProj n i j = pullMat (baseYproj n i) (lineProjY n i j) := rfl

@[simp]
theorem matEval_lineProjY (n i : ℕ) (j : Fin i) (y : baseY n i) :
    matEval y (lineProjY n i j) = taut (stageRank n (j : ℕ)) (y j) := by
  ext a b
  rfl

theorem isStarProjection_lineProjY (n i : ℕ) (j : Fin i) :
    IsStarProjection (lineProjY n i j) := by
  refine isStarProjection_of_forall_matEval fun y => ?_
  rw [matEval_lineProjY]
  exact isStarProjection_taut _ _

theorem trace_lineProjY (n i : ℕ) (j : Fin i) : Matrix.trace (lineProjY n i j) = 1 := by
  refine ContinuousMap.ext fun y => ?_
  rw [← trace_matEval, matEval_lineProjY, trace_taut]
  rfl

/-- `L_{i+1}` over `Y_{i+1}`. -/
def newLineY (n i : ℕ) :
    Matrix (Fin (stageRank n i + 1)) (Fin (stageRank n i + 1)) C(baseY n (i + 1), ℂ) :=
  lineProjY n (i + 1) (Fin.last i)

theorem newLine_eq_pullMat (n i : ℕ) :
    newLine n i = pullMat (baseYproj n (i + 1)) (newLineY n i) := rfl

theorem isStarProjection_newLineY (n i : ℕ) : IsStarProjection (newLineY n i) :=
  isStarProjection_lineProjY _ _ _

theorem trace_newLineY (n i : ℕ) : Matrix.trace (newLineY n i) = 1 :=
  trace_lineProjY _ _ _

/-- `L_{i+1}^{⊕ r_i}` over `Y_{i+1}`. -/
def newBlockY (n i : ℕ) : Matrix (NIdx n i) (NIdx n i) C(baseY n (i + 1), ℂ) :=
  (1 : Matrix (Fin (stageRank n i)) (Fin (stageRank n i)) C(baseY n (i + 1), ℂ))
    ⊗ₖ newLineY n i

theorem isStarProjection_newBlockY (n i : ℕ) : IsStarProjection (newBlockY n i) :=
  isStarProjection_kronecker (IsStarProjection.one _) (isStarProjection_newLineY n i)

theorem newBlock_eq_pullMat (n i : ℕ) :
    newBlock n i = pullMat (baseYproj n (i + 1)) (newBlockY n i) := by
  rw [newBlock, newBlockY, pullMat_kronecker, pullMat_one, newLine_eq_pullMat]

/-- **`H_i` as a projection over `Y_i` alone.** -/
def HprojY (n : ℕ) : (i : ℕ) → Matrix (HIdx n i) (HIdx n i) C(baseY n i, ℂ)
  | 0 => 0
  | (i + 1) =>
      Matrix.fromBlocks (pullMat (baseYtrunc n i) (HprojY n i)) 0 0 (newBlockY n i)

theorem HprojY_zero (n : ℕ) : HprojY n 0 = 0 := rfl

theorem HprojY_succ (n i : ℕ) : HprojY n (i + 1) =
    Matrix.fromBlocks (pullMat (baseYtrunc n i) (HprojY n i)) 0 0 (newBlockY n i) := rfl

theorem isStarProjection_HprojY (n : ℕ) : ∀ i, IsStarProjection (HprojY n i)
  | 0 => IsStarProjection.zero _
  | (i + 1) => by
      rw [HprojY_succ]
      exact isStarProjection_fromBlocks_diag
        (isStarProjection_pullMat _ (isStarProjection_HprojY n i))
        (isStarProjection_newBlockY n i)

theorem trace_HprojY (n : ℕ) : ∀ i : ℕ,
    Matrix.trace (HprojY n i) = ((hrank n i : ℕ) : C(baseY n i, ℂ))
  | 0 => by rw [HprojY_zero, Matrix.trace_zero, hrank_zero, Nat.cast_zero]
  | (i + 1) => by
      have hblocks : Matrix.trace (HprojY n (i + 1))
          = Matrix.trace (pullMat (baseYtrunc n i) (HprojY n i))
            + Matrix.trace (newBlockY n i) :=
        trace_fromBlocks _ _ _ _
      have hpull : Matrix.trace (pullMat (baseYtrunc n i) (HprojY n i))
          = ((hrank n i : ℕ) : C(baseY n (i + 1), ℂ)) := by
        refine ContinuousMap.ext fun y => ?_
        rw [← trace_matEval, matEval_pullMat, trace_matEval, trace_HprojY n i]
        rw [ContinuousMap.natCast_apply, ContinuousMap.natCast_apply]
      have hnew : Matrix.trace (newBlockY n i)
          = ((stageRank n i : ℕ) : C(baseY n (i + 1), ℂ)) := by
        rw [newBlockY, Matrix.trace_kronecker, Matrix.trace_one, trace_newLineY, mul_one,
          Fintype.card_fin]
      rw [hblocks, hpull, hnew, hrank_succ]
      push_cast
      ring

/-- **`H_i` does not see the `S^{2n}` factor**: it is pulled back from `Y_i`. -/
theorem Hproj_eq_pullMat (n : ℕ) : ∀ i : ℕ, Hproj n i = pullMat (baseYproj n i) (HprojY n i)
  | 0 => by rw [Hproj_zero, HprojY_zero, pullMat_zero]
  | (i + 1) => by
      have key : pullMat (baseYproj n (i + 1)) (HprojY n (i + 1))
          = Matrix.fromBlocks
              (pullMat (baseYproj n (i + 1)) (pullMat (baseYtrunc n i) (HprojY n i)))
              (pullMat (baseYproj n (i + 1))
                (0 : Matrix (HIdx n i) (NIdx n i) C(baseY n (i + 1), ℂ)))
              (pullMat (baseYproj n (i + 1))
                (0 : Matrix (NIdx n i) (HIdx n i) C(baseY n (i + 1), ℂ)))
              (pullMat (baseYproj n (i + 1)) (newBlockY n i)) :=
        pullMat_fromBlocks _ _ _ _ _
      rw [Hproj_succ, key, pullMat_zero, pullMat_zero, ← newBlock_eq_pullMat,
        Hproj_eq_pullMat n i, pullMat_comp, baseYproj_comp_baseProj, ← pullMat_comp]

/-! ### The stage unitaries `w_i = u ⊕ 𝟏_{H_i}` -/

/-- **`w_i = u ⊕ 𝟏_{H_i}`** for `u` a unitary of `M_n(C(X_i))`. -/
def blockUnitary (n i : ℕ) (u : Matrix (Fin n) (Fin n) C(baseX n i, ℂ)) :
    Matrix (EIdx n i) (EIdx n i) C(baseX n i, ℂ) :=
  Matrix.fromBlocks u 0 0 (Hproj n i)

theorem blockUnitary_def (n i : ℕ) (u : Matrix (Fin n) (Fin n) C(baseX n i, ℂ)) :
    blockUnitary n i u = Matrix.fromBlocks u 0 0 (Hproj n i) := rfl

theorem conjTranspose_blockUnitary (n i : ℕ) (u : Matrix (Fin n) (Fin n) C(baseX n i, ℂ)) :
    (blockUnitary n i u)ᴴ = Matrix.fromBlocks uᴴ 0 0 (Hproj n i) := by
  rw [blockUnitary_def, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_zero,
    conjTranspose_eq_of_isStarProjection (isStarProjection_Hproj n i)]

/-- `w_i` is a section of `End E_i`: it lies in the corner cut out by `E_i`. -/
theorem blockUnitary_mem_corner (n i : ℕ) (u : Matrix (Fin n) (Fin n) C(baseX n i, ℂ)) :
    Eproj n i * blockUnitary n i u * Eproj n i = blockUnitary n i u := by
  rw [Eproj_def, blockUnitary_def, fromBlocks_diag_mul, fromBlocks_diag_mul,
    Matrix.one_mul, Matrix.mul_one, (isStarProjection_Hproj n i).isIdempotentElem.eq,
    (isStarProjection_Hproj n i).isIdempotentElem.eq]

/-- `w_i* w_i = E_i`: `w_i` is an isometry of the corner. -/
theorem blockUnitary_star_mul (n i : ℕ) {u : Matrix (Fin n) (Fin n) C(baseX n i, ℂ)}
    (hu : uᴴ * u = 1) : (blockUnitary n i u)ᴴ * blockUnitary n i u = Eproj n i := by
  rw [conjTranspose_blockUnitary, blockUnitary_def, fromBlocks_diag_mul, hu,
    (isStarProjection_Hproj n i).isIdempotentElem.eq, Eproj_def]

/-- `w_i w_i* = E_i`: `w_i` is a unitary of the corner. -/
theorem blockUnitary_mul_star (n i : ℕ) {u : Matrix (Fin n) (Fin n) C(baseX n i, ℂ)}
    (hu : u * uᴴ = 1) : blockUnitary n i u * (blockUnitary n i u)ᴴ = Eproj n i := by
  rw [conjTranspose_blockUnitary, blockUnitary_def, fromBlocks_diag_mul, hu,
    (isStarProjection_Hproj n i).isIdempotentElem.eq, Eproj_def]

/-- The unit `E_i` is `w_i` for `u = 1`. -/
theorem blockUnitary_one (n i : ℕ) :
    blockUnitary n i (1 : Matrix (Fin n) (Fin n) C(baseX n i, ℂ)) = Eproj n i := rfl

/-! ### `F` over `S^{2n+1} ⊂ ℂ^{n+1}` -/

/-- The tautological column vector `x` over `S^{2n+1}`. -/
def hopfCol (n : ℕ) : Matrix (Fin (n + 1)) (Fin 1) C(↥(sphereOdd n), ℂ) :=
  Matrix.of fun a _ =>
    ⟨fun x => (x : Fin (n + 1) → ℂ) a, (continuous_apply a).comp continuous_subtype_val⟩

@[simp]
theorem hopfCol_apply (n : ℕ) (a : Fin (n + 1)) (u : Fin 1) (x : ↥(sphereOdd n)) :
    hopfCol n a u x = (x : Fin (n + 1) → ℂ) a := rfl

/-- The tautological line `x xᴴ` over `S^{2n+1}`. -/
def hopfProj (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) C(↥(sphereOdd n), ℂ) :=
  hopfCol n * (hopfCol n)ᴴ

theorem hopfProj_def (n : ℕ) : hopfProj n = hopfCol n * (hopfCol n)ᴴ := rfl

theorem matEval_hopfProj (n : ℕ) (x : ↥(sphereOdd n)) :
    matEval x (hopfProj n) = rankOneProj ((x : Fin (n + 1) → ℂ)) := by
  rw [hopfProj_def, matEval_mul, matEval_conjTranspose]
  ext a b
  rw [Matrix.mul_apply]
  simp [Matrix.conjTranspose_apply]

theorem isStarProjection_hopfProj (n : ℕ) : IsStarProjection (hopfProj n) := by
  refine isStarProjection_of_forall_matEval fun x => ?_
  rw [matEval_hopfProj]
  exact isStarProjection_rankOneProj x.2

theorem hopfCol_conjTranspose_mul (n : ℕ) : (hopfCol n)ᴴ * hopfCol n = 1 := by
  refine matrix_ext_of_matEval fun x => ?_
  rw [matEval_mul, matEval_conjTranspose, matEval_one]
  ext u v
  rw [Matrix.mul_apply]
  have hterm : ∀ a : Fin (n + 1),
      ((matEval x (hopfCol n))ᴴ) u a * (matEval x (hopfCol n)) a v
        = star ((x : Fin (n + 1) → ℂ) a) * (x : Fin (n + 1) → ℂ) a := by
    intro a
    rw [Matrix.conjTranspose_apply]
    rfl
  rw [Finset.sum_congr rfl (fun a _ => hterm a), sum_star_mul_self x.2]
  have huv : u = v := Subsingleton.elim u v
  subst huv
  rw [Matrix.one_apply_eq]

theorem trace_hopfProj (n : ℕ) : Matrix.trace (hopfProj n) = 1 := by
  refine ContinuousMap.ext fun x => ?_
  rw [← trace_matEval, matEval_hopfProj, trace_rankOneProj x.2]
  rfl

/-- **`F`**: the rank-`n` bundle `F_x = {w ∈ ℂ^{n+1} : ⟨w, x⟩ = 0}` over `S^{2n+1}`,
written as the projection `x ↦ 1 - x xᴴ`. -/
def Fproj (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) C(↥(sphereOdd n), ℂ) :=
  1 - hopfProj n

theorem Fproj_def (n : ℕ) : Fproj n = 1 - hopfProj n := rfl

theorem isStarProjection_Fproj (n : ℕ) : IsStarProjection (Fproj n) :=
  (isStarProjection_hopfProj n).one_sub

/-- `F` has rank `n`. -/
theorem trace_Fproj (n : ℕ) :
    Matrix.trace (Fproj n) = ((n : ℕ) : C(↥(sphereOdd n), ℂ)) := by
  rw [Fproj_def, Matrix.trace_sub, Matrix.trace_one, trace_hopfProj, Fintype.card_fin]
  push_cast
  ring

theorem Fproj_mul_hopfCol (n : ℕ) : Fproj n * hopfCol n = 0 := by
  rw [Fproj_def, Matrix.sub_mul, Matrix.one_mul, hopfProj_def, Matrix.mul_assoc,
    hopfCol_conjTranspose_mul, Matrix.mul_one, sub_self]

theorem hopfCol_conjTranspose_mul_Fproj (n : ℕ) : (hopfCol n)ᴴ * Fproj n = 0 := by
  have h := congrArg Matrix.conjTranspose (Fproj_mul_hopfCol n)
  rw [Matrix.conjTranspose_mul,
    conjTranspose_eq_of_isStarProjection (isStarProjection_Fproj n),
    Matrix.conjTranspose_zero] at h
  exact h

theorem hopfProj_add_Fproj (n : ℕ) : hopfProj n + Fproj n = 1 := by
  rw [Fproj_def]
  abel

/-- **`F ⊕ 𝟏 ≅ 𝟏^{n+1}`**, the cancellation identity of the manuscript's §2, as a
Murray--von Neumann equivalence of projections in `M_{n+2}(C(S^{2n+1}))`.

The implementer is the explicit partial isometry `[[F, x], [0, 0]]`. -/
theorem murrayVonNeumannEquiv_Fproj (n : ℕ) :
    MurrayVonNeumannEquiv
      (Matrix.fromBlocks (Fproj n) 0 0
        (1 : Matrix (Fin 1) (Fin 1) C(↥(sphereOdd n), ℂ)))
      (Matrix.fromBlocks
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) C(↥(sphereOdd n), ℂ)) 0 0
        (0 : Matrix (Fin 1) (Fin 1) C(↥(sphereOdd n), ℂ))) := by
  refine ⟨Matrix.fromBlocks (Fproj n) (hopfCol n) 0 0, ?_, ?_⟩
  · rw [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
      Matrix.conjTranspose_zero,
      conjTranspose_eq_of_isStarProjection (isStarProjection_Fproj n),
      Matrix.fromBlocks_multiply, (isStarProjection_Fproj n).isIdempotentElem.eq,
      Fproj_mul_hopfCol, hopfCol_conjTranspose_mul_Fproj, hopfCol_conjTranspose_mul]
    simp
  · have hkey : Fproj n * Fproj n + hopfCol n * (hopfCol n)ᴴ
        = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) C(↥(sphereOdd n), ℂ)) := by
      rw [(isStarProjection_Fproj n).isIdempotentElem.eq, ← hopfProj_def, Fproj_def]
      abel
    rw [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
      Matrix.conjTranspose_zero,
      conjTranspose_eq_of_isStarProjection (isStarProjection_Fproj n),
      Matrix.fromBlocks_multiply, hkey]
    simp

end Gen

/-! ### The `n = 2` instance

Everything above is generic in the rank `n`; the mod-2 program of
`notes/LIX_FULL_PROGRAM_2026-09-05.md` is the case `n = 2`, and this section pins the names
the rest of the LIX closure is written against to it.  Nothing here has content: every
declaration is `Gen.<same name> 2` and every proof is the generic one applied at `2`.

`Gen.stageRank` is `2 ^ i * n`, so `stageRank i` is **definitionally** `2 ^ (i + 1)`; the
`rfl` that `Analysis/LIXLemmaTwoProp.lean`'s `lixDD_apply` is proved by, and every
downstream use of it, is unaffected by the generalisation. -/

/-- `S^4`, the unit sphere of `ℝ^5`. -/
abbrev sphereFour : Set (EuclideanSpace ℝ (Fin 5)) := Gen.sphereEven 2

/-- `S^5`, the unit sphere of `ℂ³` inside the plain product space `Fin 3 → ℂ`. -/
abbrev sphereFive : Set (Fin 3 → ℂ) := Gen.sphereOdd 2

/-- `r i = 2^{i+1}`, the rank of `E_i` in the manuscript's (4.1). -/
abbrev stageRank (i : ℕ) : ℕ := Gen.stageRank 2 i

@[simp] theorem stageRank_zero : stageRank 0 = 2 := Gen.stageRank_zero 2

theorem stageRank_pos (i : ℕ) : 0 < stageRank i := Gen.stageRank_pos 2 i

theorem stageRank_succ (i : ℕ) : stageRank (i + 1) = 2 * stageRank i :=
  Gen.stageRank_succ 2 i

/-- `rank H_i = ∑_{j<i} r_j`. -/
abbrev hrank (i : ℕ) : ℕ := Gen.hrank 2 i

@[simp] theorem hrank_zero : hrank 0 = 0 := rfl

theorem hrank_succ (i : ℕ) : hrank (i + 1) = hrank i + stageRank i := rfl

/-- The manuscript's `rank H_i = r_i - 2`, stated without truncated subtraction. -/
theorem hrank_add_two (i : ℕ) : hrank i + 2 = stageRank i := Gen.hrank_add_rank 2 i

/-- The manuscript's `dim_ℝ X_i = 2 r_i`. -/
theorem realDim_baseX (i : ℕ) : 4 + 2 * hrank i = 2 * stageRank i := Gen.realDim_baseX 2 i

/-- `Y_i = ∏_{j<i} ℂP^{r_j}`. -/
abbrev baseY (i : ℕ) := Gen.baseY 2 i

/-- `X_i = S^4 × Y_i`. -/
abbrev baseX (i : ℕ) := Gen.baseX 2 i

/-- The coordinate projection `X_i → X_k` for `k ≤ i`, the manuscript's `π_{k,i}`. -/
abbrev basePr {k i : ℕ} (h : k ≤ i) : C(baseX i, baseX k) := Gen.basePr 2 h

@[simp]
theorem basePr_apply {k i : ℕ} (h : k ≤ i) (w : baseX i) :
    basePr h w = (w.1, fun j => w.2 (Fin.castLE h j)) := rfl

theorem basePr_self (i : ℕ) : basePr (le_refl i) = ContinuousMap.id (baseX i) :=
  Gen.basePr_self 2 i

theorem basePr_comp {k i m : ℕ} (h₁ : k ≤ i) (h₂ : i ≤ m) :
    (basePr h₁).comp (basePr h₂) = basePr (h₁.trans h₂) := Gen.basePr_comp 2 h₁ h₂

/-- **The tower of base spaces is surjective.** -/
theorem basePr_surjective {k i : ℕ} (h : k ≤ i) : Function.Surjective (basePr h) :=
  Gen.basePr_surjective 2 h

/-- `π_i : X_{i+1} → X_i`. -/
abbrev baseProj (i : ℕ) : C(baseX (i + 1), baseX i) := Gen.baseProj 2 i

/-- The new block at stage `i`. -/
abbrev NIdx (i : ℕ) : Type := Gen.NIdx 2 i

/-- The index set of `H_i = ⊕_{j<i} L_{j+1}^{⊕ r_j}`. -/
abbrev HIdx (i : ℕ) : Type := Gen.HIdx 2 i

theorem HIdx_succ (i : ℕ) : HIdx (i + 1) = (HIdx i ⊕ NIdx i) := rfl

/-- The index set of `E_i = 𝟏² ⊕ H_i`. -/
abbrev EIdx (i : ℕ) : Type := Gen.EIdx 2 i

/-- `E_{i+1}`'s index set is `E_i`'s plus the new block, by associativity of `⊕`. -/
def eIdxSucc (i : ℕ) : EIdx i ⊕ NIdx i ≃ EIdx (i + 1) := Gen.eIdxSucc 2 i

/-- The tautological line of the `j`-th projective factor, pulled back to `X_i`. -/
def lineProj (i : ℕ) (j : Fin i) :
    Matrix (Fin (stageRank (j : ℕ) + 1)) (Fin (stageRank (j : ℕ) + 1)) C(baseX i, ℂ) :=
  Gen.lineProj 2 i j

@[simp]
theorem matEval_lineProj (i : ℕ) (j : Fin i) (z : baseX i) :
    matEval z (lineProj i j) = taut (stageRank (j : ℕ)) (z.2 j) :=
  Gen.matEval_lineProj 2 i j z

theorem isStarProjection_lineProj (i : ℕ) (j : Fin i) : IsStarProjection (lineProj i j) :=
  Gen.isStarProjection_lineProj 2 i j

theorem trace_lineProj (i : ℕ) (j : Fin i) : Matrix.trace (lineProj i j) = 1 :=
  Gen.trace_lineProj 2 i j

/-- `L_{i+1}`, the tautological line of the newest projective factor of `X_{i+1}`. -/
def newLine (i : ℕ) :
    Matrix (Fin (stageRank i + 1)) (Fin (stageRank i + 1)) C(baseX (i + 1), ℂ) :=
  Gen.newLine 2 i

theorem isStarProjection_newLine (i : ℕ) : IsStarProjection (newLine i) :=
  Gen.isStarProjection_newLine 2 i

theorem trace_newLine (i : ℕ) : Matrix.trace (newLine i) = 1 := Gen.trace_newLine 2 i

/-- The new block of `H_{i+1}`: `r_i` copies of `L_{i+1}`. -/
def newBlock (i : ℕ) : Matrix (NIdx i) (NIdx i) C(baseX (i + 1), ℂ) := Gen.newBlock 2 i

theorem newBlock_def (i : ℕ) :
    newBlock i =
      (1 : Matrix (Fin (stageRank i)) (Fin (stageRank i)) C(baseX (i + 1), ℂ))
        ⊗ₖ newLine i := rfl

theorem isStarProjection_newBlock (i : ℕ) : IsStarProjection (newBlock i) :=
  Gen.isStarProjection_newBlock 2 i

theorem trace_newBlock (i : ℕ) :
    Matrix.trace (newBlock i) = ((stageRank i : ℕ) : C(baseX (i + 1), ℂ)) :=
  Gen.trace_newBlock 2 i

/-- `H_i = ⊕_{j<i} L_{j+1}^{⊕ r_j}`. -/
def Hproj (i : ℕ) : Matrix (HIdx i) (HIdx i) C(baseX i, ℂ) := Gen.Hproj 2 i

theorem Hproj_zero : Hproj 0 = 0 := rfl

theorem Hproj_succ (i : ℕ) : Hproj (i + 1) =
    Matrix.fromBlocks (pullMat (baseProj i) (Hproj i)) 0 0 (newBlock i) := rfl

/-- `E_i = 𝟏² ⊕ H_i`. -/
def Eproj (i : ℕ) : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ) := Gen.Eproj 2 i

theorem Eproj_def (i : ℕ) : Eproj i =
    Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) C(baseX i, ℂ)) 0 0 (Hproj i) := rfl

theorem isStarProjection_Hproj (i : ℕ) : IsStarProjection (Hproj i) :=
  Gen.isStarProjection_Hproj 2 i

theorem isStarProjection_Eproj (i : ℕ) : IsStarProjection (Eproj i) :=
  Gen.isStarProjection_Eproj 2 i

/-- **`rank H_i = r_i - 2`.** -/
theorem trace_Hproj (i : ℕ) : Matrix.trace (Hproj i) = ((hrank i : ℕ) : C(baseX i, ℂ)) :=
  Gen.trace_Hproj 2 i

/-- **`rank E_i = r_i`.** -/
theorem trace_Eproj (i : ℕ) :
    Matrix.trace (Eproj i) = ((stageRank i : ℕ) : C(baseX i, ℂ)) := Gen.trace_Eproj 2 i

/-- The pointwise form of `rank E_i = r_i`. -/
theorem trace_matEval_Eproj (i : ℕ) (w : baseX i) :
    (matEval w (Eproj i)).trace = ((stageRank i : ℕ) : ℂ) := Gen.trace_matEval_Eproj 2 i w

/-- **`E_i` is not the zero projection.** -/
theorem Eproj_ne_zero (i : ℕ) : Eproj i ≠ 0 := Gen.Eproj_ne_zero 2 i

/-- **The manuscript's global bundle decomposition.** -/
theorem Eproj_succ (i : ℕ) :
    Eproj (i + 1) = Matrix.reindex (eIdxSucc i) (eIdxSucc i)
      (Matrix.fromBlocks (pullMat (baseProj i) (Eproj i)) 0 0 (newBlock i)) :=
  Gen.Eproj_succ 2 i

/-- The projection `X_i → Y_i`. -/
def baseYproj (i : ℕ) : C(baseX i, baseY i) := Gen.baseYproj 2 i

/-- The truncation `Y_{i+1} → Y_i`. -/
def baseYtrunc (i : ℕ) : C(baseY (i + 1), baseY i) := Gen.baseYtrunc 2 i

theorem baseYproj_comp_baseProj (i : ℕ) :
    (baseYproj i).comp (baseProj i) = (baseYtrunc i).comp (baseYproj (i + 1)) := rfl

/-- The tautological line of the `j`-th projective factor, over `Y_i`. -/
def lineProjY (i : ℕ) (j : Fin i) :
    Matrix (Fin (stageRank (j : ℕ) + 1)) (Fin (stageRank (j : ℕ) + 1)) C(baseY i, ℂ) :=
  Gen.lineProjY 2 i j

theorem lineProj_eq_pullMat (i : ℕ) (j : Fin i) :
    lineProj i j = pullMat (baseYproj i) (lineProjY i j) := rfl

@[simp]
theorem matEval_lineProjY (i : ℕ) (j : Fin i) (y : baseY i) :
    matEval y (lineProjY i j) = taut (stageRank (j : ℕ)) (y j) :=
  Gen.matEval_lineProjY 2 i j y

theorem isStarProjection_lineProjY (i : ℕ) (j : Fin i) :
    IsStarProjection (lineProjY i j) := Gen.isStarProjection_lineProjY 2 i j

theorem trace_lineProjY (i : ℕ) (j : Fin i) : Matrix.trace (lineProjY i j) = 1 :=
  Gen.trace_lineProjY 2 i j

/-- `L_{i+1}` over `Y_{i+1}`. -/
def newLineY (i : ℕ) :
    Matrix (Fin (stageRank i + 1)) (Fin (stageRank i + 1)) C(baseY (i + 1), ℂ) :=
  Gen.newLineY 2 i

theorem newLine_eq_pullMat (i : ℕ) :
    newLine i = pullMat (baseYproj (i + 1)) (newLineY i) := rfl

theorem isStarProjection_newLineY (i : ℕ) : IsStarProjection (newLineY i) :=
  Gen.isStarProjection_newLineY 2 i

theorem trace_newLineY (i : ℕ) : Matrix.trace (newLineY i) = 1 := Gen.trace_newLineY 2 i

/-- `L_{i+1}^{⊕ r_i}` over `Y_{i+1}`. -/
def newBlockY (i : ℕ) : Matrix (NIdx i) (NIdx i) C(baseY (i + 1), ℂ) := Gen.newBlockY 2 i

theorem isStarProjection_newBlockY (i : ℕ) : IsStarProjection (newBlockY i) :=
  Gen.isStarProjection_newBlockY 2 i

theorem newBlock_eq_pullMat (i : ℕ) :
    newBlock i = pullMat (baseYproj (i + 1)) (newBlockY i) := Gen.newBlock_eq_pullMat 2 i

/-- **`H_i` as a projection over `Y_i` alone.** -/
def HprojY (i : ℕ) : Matrix (HIdx i) (HIdx i) C(baseY i, ℂ) := Gen.HprojY 2 i

theorem HprojY_zero : HprojY 0 = 0 := rfl

theorem HprojY_succ (i : ℕ) : HprojY (i + 1) =
    Matrix.fromBlocks (pullMat (baseYtrunc i) (HprojY i)) 0 0 (newBlockY i) := rfl

theorem isStarProjection_HprojY (i : ℕ) : IsStarProjection (HprojY i) :=
  Gen.isStarProjection_HprojY 2 i

theorem trace_HprojY (i : ℕ) :
    Matrix.trace (HprojY i) = ((hrank i : ℕ) : C(baseY i, ℂ)) := Gen.trace_HprojY 2 i

/-- **`H_i` does not see the `S^4` factor.** -/
theorem Hproj_eq_pullMat (i : ℕ) : Hproj i = pullMat (baseYproj i) (HprojY i) :=
  Gen.Hproj_eq_pullMat 2 i

/-- **`w_i = u ⊕ 𝟏_{H_i}`.** -/
def blockUnitary (i : ℕ) (u : Matrix (Fin 2) (Fin 2) C(baseX i, ℂ)) :
    Matrix (EIdx i) (EIdx i) C(baseX i, ℂ) := Gen.blockUnitary 2 i u

theorem blockUnitary_def (i : ℕ) (u : Matrix (Fin 2) (Fin 2) C(baseX i, ℂ)) :
    blockUnitary i u = Matrix.fromBlocks u 0 0 (Hproj i) := rfl

theorem conjTranspose_blockUnitary (i : ℕ) (u : Matrix (Fin 2) (Fin 2) C(baseX i, ℂ)) :
    (blockUnitary i u)ᴴ = Matrix.fromBlocks uᴴ 0 0 (Hproj i) :=
  Gen.conjTranspose_blockUnitary 2 i u

/-- `w_i` is a section of `End E_i`: it lies in the corner cut out by `E_i`. -/
theorem blockUnitary_mem_corner (i : ℕ) (u : Matrix (Fin 2) (Fin 2) C(baseX i, ℂ)) :
    Eproj i * blockUnitary i u * Eproj i = blockUnitary i u :=
  Gen.blockUnitary_mem_corner 2 i u

/-- `w_i* w_i = E_i`. -/
theorem blockUnitary_star_mul (i : ℕ) {u : Matrix (Fin 2) (Fin 2) C(baseX i, ℂ)}
    (hu : uᴴ * u = 1) : (blockUnitary i u)ᴴ * blockUnitary i u = Eproj i :=
  Gen.blockUnitary_star_mul 2 i hu

/-- `w_i w_i* = E_i`. -/
theorem blockUnitary_mul_star (i : ℕ) {u : Matrix (Fin 2) (Fin 2) C(baseX i, ℂ)}
    (hu : u * uᴴ = 1) : blockUnitary i u * (blockUnitary i u)ᴴ = Eproj i :=
  Gen.blockUnitary_mul_star 2 i hu

/-- The unit `E_i` is `w_i` for `u = 1`. -/
theorem blockUnitary_one (i : ℕ) :
    blockUnitary i (1 : Matrix (Fin 2) (Fin 2) C(baseX i, ℂ)) = Eproj i := rfl

/-- The tautological column vector `x` over `S^5`. -/
def hopfCol : Matrix (Fin 3) (Fin 1) C(↥sphereFive, ℂ) := Gen.hopfCol 2

@[simp]
theorem hopfCol_apply (a : Fin 3) (u : Fin 1) (x : ↥sphereFive) :
    hopfCol a u x = (x : Fin 3 → ℂ) a := rfl

/-- The tautological line `x xᴴ` over `S^5`. -/
def hopfProj : Matrix (Fin 3) (Fin 3) C(↥sphereFive, ℂ) := Gen.hopfProj 2

theorem hopfProj_def : hopfProj = hopfCol * hopfColᴴ := rfl

theorem matEval_hopfProj (x : ↥sphereFive) :
    matEval x hopfProj = rankOneProj ((x : Fin 3 → ℂ)) := Gen.matEval_hopfProj 2 x

theorem isStarProjection_hopfProj : IsStarProjection hopfProj := Gen.isStarProjection_hopfProj 2

theorem hopfCol_conjTranspose_mul : hopfColᴴ * hopfCol = 1 := Gen.hopfCol_conjTranspose_mul 2

theorem trace_hopfProj : Matrix.trace hopfProj = 1 := Gen.trace_hopfProj 2

/-- **`F`**: the rank-two bundle `F_x = {w ∈ ℂ³ : ⟨w, x⟩ = 0}` over `S^5`. -/
def Fproj : Matrix (Fin 3) (Fin 3) C(↥sphereFive, ℂ) := Gen.Fproj 2

theorem Fproj_def : Fproj = 1 - hopfProj := rfl

theorem isStarProjection_Fproj : IsStarProjection Fproj := Gen.isStarProjection_Fproj 2

/-- `F` has rank two. -/
theorem trace_Fproj : Matrix.trace Fproj = 2 := Gen.trace_Fproj 2

theorem Fproj_mul_hopfCol : Fproj * hopfCol = 0 := Gen.Fproj_mul_hopfCol 2

theorem hopfCol_conjTranspose_mul_Fproj : hopfColᴴ * Fproj = 0 :=
  Gen.hopfCol_conjTranspose_mul_Fproj 2

theorem hopfProj_add_Fproj : hopfProj + Fproj = 1 := Gen.hopfProj_add_Fproj 2

/-- **`F ⊕ 𝟏 ≅ 𝟏³`**, the cancellation identity of the manuscript's §2. -/
theorem murrayVonNeumannEquiv_Fproj :
    MurrayVonNeumannEquiv
      (Matrix.fromBlocks Fproj 0 0 (1 : Matrix (Fin 1) (Fin 1) C(↥sphereFive, ℂ)))
      (Matrix.fromBlocks (1 : Matrix (Fin 3) (Fin 3) C(↥sphereFive, ℂ)) 0 0
        (0 : Matrix (Fin 1) (Fin 1) C(↥sphereFive, ℂ))) :=
  Gen.murrayVonNeumannEquiv_Fproj 2

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
