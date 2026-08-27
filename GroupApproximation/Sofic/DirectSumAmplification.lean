import GroupApproximation.Sofic.NormMFUniversalCorona

/-!
# Direct-sum amplification of a finite-dimensional representation

The manuscript proves the first inclusion of `prop:stabradical` — the MF
radical is contained in the finite-dimensional residual — by amplifying:

> A finite-dimensional unitary representation `π` on `ℂ^d` amplifies to
> `π^{⊕n}` on `ℂ^{nd}`; the dimensions `nd` are strictly increasing, so
> `(π^{⊕n})_n` is a homomorphism to `U(Q)` in the sense of
> `eq:unitary-corona`.  Since `‖π^{⊕n}(x) − 1‖ = ‖π(x) − 1‖` for every `n`,
> that sequence is null exactly when `π(x) = 1`.

Two features of that sentence are load-bearing and neither is supplied by a
constant sequence of models: the dimensions must *increase*, because that is
the convention the corona of `eq:unitary-corona` is built on, and the operator
norm must be *exactly* preserved, because the argument reads a null sequence
off a single value.  This file supplies both.

`directSumModel Y n` is `Y^{⊕(n+1)}`, built by iterated binary block sum, so
its cardinality is `(n+1)·|Y|` and strictly increases with `n` whenever `Y` is
nonempty.  `directSumRep` puts `π^{⊕(n+1)}` on it, block-diagonally, and
`opLength_directSumRep` is the printed norm identity: distance from the
identity is a maximum over blocks, and all the blocks are equal.

`Sofic.MatricialStabilityRadical` consumes this to prove the printed
inclusion; nothing else in the development depends on it.
-/

namespace GroupApproximation
namespace DirectSumAmplification

open Matrix
open scoped Matrix.Norms.L2Operator

universe u

variable {G : Type u} [Group G]

/-! ## The amplified model `Y^{⊕(n+1)}` -/

/-- The `(n+1)`-fold direct sum of a finite model with itself. -/
def directSumModel (Y : FiniteModel) : ℕ → FiniteModel
  | 0 => Y
  | n + 1 => blockSumModel (directSumModel Y n) Y

theorem card_directSumModel_succ (Y : FiniteModel) (n : ℕ) :
    Fintype.card (directSumModel Y (n + 1))
      = Fintype.card (directSumModel Y n) + Fintype.card Y := by
  change Fintype.card ((directSumModel Y n : Type) ⊕ (Y : Type)) = _
  exact Fintype.card_sum

/-- The amplified dimensions are the printed ones: `nd` for the `n`-th
amplification of a `d`-dimensional representation. -/
theorem card_directSumModel (Y : FiniteModel) (n : ℕ) :
    Fintype.card (directSumModel Y n) = (n + 1) * Fintype.card Y := by
  induction n with
  | zero =>
      show Fintype.card Y = (0 + 1) * Fintype.card Y
      rw [zero_add, one_mul]
  | succ n ih =>
      rw [card_directSumModel_succ, ih]
      ring

/-- A nonempty model amplifies to nonempty models. -/
theorem card_directSumModel_pos (Y : FiniteModel) (hY : 0 < Fintype.card Y)
    (n : ℕ) : 0 < Fintype.card (directSumModel Y n) := by
  rw [card_directSumModel]
  exact Nat.mul_pos (by omega) hY

/-- **"The dimensions `nd` are strictly increasing."** -/
theorem card_directSumModel_lt_succ (Y : FiniteModel)
    (hY : 0 < Fintype.card Y) (n : ℕ) :
    Fintype.card (directSumModel Y n) < Fintype.card (directSumModel Y (n + 1)) := by
  rw [card_directSumModel_succ]
  omega

theorem strictMono_card_directSumModel (Y : FiniteModel)
    (hY : 0 < Fintype.card Y) :
    StrictMono fun n ↦ Fintype.card (directSumModel Y n) :=
  strictMono_nat_of_lt_succ (card_directSumModel_lt_succ Y hY)

/-! ## The amplified representation `π^{⊕(n+1)}` -/

/-- Block-diagonal juxtaposition of unitaries, as a homomorphism of unitary
groups. -/
def blockDiagHom (Y Z : FiniteModel) :
    Matrix.unitaryGroup Y ℂ × Matrix.unitaryGroup Z ℂ →*
      Matrix.unitaryGroup (blockSumModel Y Z) ℂ where
  toFun u :=
    ⟨blockDiagMatrix Y Z (u.1 : Matrix Y Y ℂ) (u.2 : Matrix Z Z ℂ),
      blockDiagMatrix_mem_unitaryGroup Y Z u.1.property u.2.property⟩
  map_one' := by
    apply Subtype.ext
    exact blockDiagMatrix_one Y Z
  map_mul' a b := by
    apply Subtype.ext
    change
      blockDiagMatrix Y Z
          ((a.1 : Matrix Y Y ℂ) * (b.1 : Matrix Y Y ℂ))
          ((a.2 : Matrix Z Z ℂ) * (b.2 : Matrix Z Z ℂ)) =
        blockDiagMatrix Y Z (a.1 : Matrix Y Y ℂ) (a.2 : Matrix Z Z ℂ) *
          blockDiagMatrix Y Z (b.1 : Matrix Y Y ℂ) (b.2 : Matrix Z Z ℂ)
    rw [blockDiagMatrix_mul]

/-- The amplification `π^{⊕(n+1)}` of a finite-dimensional unitary
representation. -/
def directSumRep (Y : FiniteModel) (phi : G →* Matrix.unitaryGroup Y ℂ) :
    ∀ n, G →* Matrix.unitaryGroup (directSumModel Y n) ℂ
  | 0 => phi
  | n + 1 =>
      (blockDiagHom (directSumModel Y n) Y).comp
        ((directSumRep Y phi n).prod phi)

@[simp] theorem directSumRep_succ_apply (Y : FiniteModel)
    (phi : G →* Matrix.unitaryGroup Y ℂ) (n : ℕ) (g : G) :
    ((directSumRep Y phi (n + 1) g :
        Matrix (directSumModel Y (n + 1)) (directSumModel Y (n + 1)) ℂ))
      = blockDiagMatrix (directSumModel Y n) Y
          (directSumRep Y phi n g :
            Matrix (directSumModel Y n) (directSumModel Y n) ℂ)
          (phi g : Matrix Y Y ℂ) :=
  rfl

/-- **"`‖π^{⊕n}(x) − 1‖ = ‖π(x) − 1‖` for every `n`."**  The distance of a
block diagonal from the identity is the maximum of the block distances, and
every block of an amplification is the same. -/
theorem opLength_directSumRep (Y : FiniteModel)
    (phi : G →* Matrix.unitaryGroup Y ℂ) (g : G) (n : ℕ) :
    opLength (directSumModel Y n) (directSumRep Y phi n g)
      = opLength Y (phi g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      unfold opLength at ih ⊢
      -- `directSumModel Y (n+1)` and `blockSumModel (directSumModel Y n) Y` are
      -- defeq, but `rw` matches syntactically and the norm carries its index
      -- type as an implicit argument -- so rewriting the *term* under the norm
      -- leaves that argument in the old form and every later rewrite misses.
      -- Restating the goal with `show`, which works up to defeq, moves the
      -- index type once and the printed chain then applies verbatim.
      show ‖blockDiagMatrix (directSumModel Y n) Y
              (directSumRep Y phi n g :
                Matrix (directSumModel Y n) (directSumModel Y n) ℂ)
              (phi g : Matrix Y Y ℂ) - 1‖
            = ‖(phi g : Matrix Y Y ℂ) - 1‖
      rw [← blockDiagMatrix_one (directSumModel Y n) Y, blockDiagMatrix_sub,
        l2_opNorm_blockDiag, ih, max_self]

/-! ## The amplified corona representation -/

/-- The homomorphism to the unitary-sequence corona assembled from the
amplifications: this is the printed `(π^{⊕n})_n`. -/
def directSumCoronaRep (Y : FiniteModel)
    (phi : G →* Matrix.unitaryGroup Y ℂ) :
    G →* NormMatrixCoronaUnitary (directSumModel Y) :=
  (QuotientGroup.mk' (nullCofiniteOpSubgroup (directSumModel Y))).comp
    (MonoidHom.pi fun n ↦ directSumRep Y phi n)

/-- **"That sequence is null exactly when `π(x) = 1`."**  Nullity of the
amplified sequence is a statement about a single number, because every
coordinate carries the same operator-norm displacement. -/
theorem opLength_eq_zero_of_null (Y : FiniteModel)
    (phi : G →* Matrix.unitaryGroup Y ℂ) (x : G)
    (hnull : (fun n ↦ directSumRep Y phi n x) ∈
      nullCofiniteOpSubgroup (directSumModel Y)) :
    (phi x : Matrix Y Y ℂ) = 1 := by
  have hlen : ∀ ε : ℝ, 0 < ε → opLength Y (phi x) < ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := (hnull ε hε).exists
    rwa [opLength_directSumRep] at hn
  have hzero : opLength Y (phi x) = 0 := by
    by_contra hne
    have hpos : 0 < opLength Y (phi x) :=
      lt_of_le_of_ne (opLength_nonneg Y (phi x)) (Ne.symm hne)
    exact absurd (hlen _ hpos) (lt_irrefl _)
  have hsub : (phi x : Matrix Y Y ℂ) - 1 = 0 := by
    unfold opLength at hzero
    exact norm_eq_zero.mp hzero
  exact sub_eq_zero.mp hsub

end DirectSumAmplification
end GroupApproximation
