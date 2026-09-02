import GroupApproximation.GGT.VanKampen.CombMap
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.DeriveFintype

/-!
# The finite rotation system of a polygon cactus

This file constructs the dart permutations underlying the explicit cactus
diagram.  There is one outer polygon, one polygon for each relator, and one
stem edge joining the distinguished vertex of every relator polygon to the
distinguished vertex of the outer polygon.  All polygon lengths are positive.

The dart constructors name the two orientations of every polygon edge and
the two orientations of every stem.  Edge reversal swaps the corresponding
constructors.  Vertex rotation has degree two away from attachment vertices,
degree three at a relator attachment, and degree `cellCount + 2` at the outer
attachment.  The resulting face permutation has the outer polygon, all
relator polygons, and one complementary face.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open Equiv

/-- Positive polygon lengths for a finite cactus. -/
structure CactusShape where
  boundaryLength : ℕ
  boundary_pos : 0 < boundaryLength
  cellCount : ℕ
  relatorLength : Fin cellCount → ℕ
  relator_pos : ∀ i, 0 < relatorLength i

/-- Oriented edge-ends of the polygon cactus. -/
inductive CactusDart (S : CactusShape) where
  | outerForward : Fin S.boundaryLength → CactusDart S
  | outerBackward : Fin S.boundaryLength → CactusDart S
  | relatorForward : (i : Fin S.cellCount) →
      Fin (S.relatorLength i) → CactusDart S
  | relatorBackward : (i : Fin S.cellCount) →
      Fin (S.relatorLength i) → CactusDart S
  | stemOut : Fin S.cellCount → CactusDart S
  | stemIn : Fin S.cellCount → CactusDart S
  deriving DecidableEq, Fintype

namespace CactusShape

/-- The distinguished vertex index of the positive outer polygon. -/
def boundaryZero (S : CactusShape) : Fin S.boundaryLength :=
  ⟨0, S.boundary_pos⟩

/-- The distinguished vertex index of a positive relator polygon. -/
def relatorZero (S : CactusShape) (i : Fin S.cellCount) :
    Fin (S.relatorLength i) :=
  ⟨0, S.relator_pos i⟩

/-- The first cell index, supplied only in the positive-cell branch. -/
def cellZero (S : CactusShape) (h : 0 < S.cellCount) : Fin S.cellCount :=
  ⟨0, h⟩

/-- Cyclic successor on a positive finite polygon. -/
def nextFin (n : ℕ) : Fin n → Fin n := finRotate n

/-- Cyclic predecessor on a positive finite polygon. -/
def prevFin (n : ℕ) : Fin n → Fin n := (finRotate n).symm

theorem nextFin_prevFin (n : ℕ) (i : Fin n) :
    nextFin n (prevFin n i) = i :=
  (finRotate n).apply_symm_apply i

theorem prevFin_nextFin (n : ℕ) (i : Fin n) :
    prevFin n (nextFin n i) = i :=
  (finRotate n).symm_apply_apply i

/-- Edge reversal on cactus darts. -/
def alphaFun (S : CactusShape) : CactusDart S → CactusDart S
  | .outerForward j => .outerBackward j
  | .outerBackward j => .outerForward j
  | .relatorForward i j => .relatorBackward i j
  | .relatorBackward i j => .relatorForward i j
  | .stemOut i => .stemIn i
  | .stemIn i => .stemOut i

theorem alphaFun_involutive (S : CactusShape) :
    Function.Involutive S.alphaFun := by
  intro d
  cases d <;> rfl

/-- The fixed-point-free edge-reversal permutation. -/
def alpha (S : CactusShape) : Perm (CactusDart S) :=
  S.alphaFun_involutive.toPerm S.alphaFun

theorem alpha_apply (S : CactusShape) (d : CactusDart S) :
    S.alpha d = S.alphaFun d := rfl

theorem alpha_fixedPointFree (S : CactusShape) (d : CactusDart S) :
    S.alpha d ≠ d := by
  cases d <;> simp [alpha, alphaFun]

/-- Vertex rotation, written as a function before its inverse is supplied.
At the outer attachment it visits the outgoing stems in cyclic index order. -/
def sigmaFun (S : CactusShape) : CactusDart S → CactusDart S
  | .outerForward j =>
      if _hj : j = S.boundaryZero then
        if hn : 0 < S.cellCount then .stemOut (S.cellZero hn)
        else .outerBackward (prevFin S.boundaryLength j)
      else .outerBackward (prevFin S.boundaryLength j)
  | .outerBackward j => .outerForward (nextFin S.boundaryLength j)
  | .relatorForward i j =>
      if _hj : j = S.relatorZero i then .stemIn i
      else .relatorBackward i (prevFin (S.relatorLength i) j)
  | .relatorBackward i j =>
      .relatorForward i (nextFin (S.relatorLength i) j)
  | .stemOut i =>
      if _hi : nextFin S.cellCount i = S.cellZero (Nat.zero_lt_of_lt i.isLt) then
        .outerBackward (prevFin S.boundaryLength S.boundaryZero)
      else .stemOut (nextFin S.cellCount i)
  | .stemIn i =>
      .relatorBackward i (prevFin (S.relatorLength i) (S.relatorZero i))

/-- Explicit inverse of the cactus vertex rotation. -/
def sigmaInvFun (S : CactusShape) : CactusDart S → CactusDart S
  | .outerForward j => .outerBackward (prevFin S.boundaryLength j)
  | .outerBackward j =>
      if _hj : nextFin S.boundaryLength j = S.boundaryZero then
        if hn : 0 < S.cellCount then .stemOut (prevFin S.cellCount (S.cellZero hn))
        else .outerForward S.boundaryZero
      else .outerForward (nextFin S.boundaryLength j)
  | .relatorForward i j =>
      .relatorBackward i (prevFin (S.relatorLength i) j)
  | .relatorBackward i j =>
      if _hj : nextFin (S.relatorLength i) j = S.relatorZero i then .stemIn i
      else .relatorForward i (nextFin (S.relatorLength i) j)
  | .stemOut i =>
      if _hi : i = S.cellZero (Nat.zero_lt_of_lt i.isLt) then
        .outerForward S.boundaryZero
      else .stemOut (prevFin S.cellCount i)
  | .stemIn i => .relatorForward i (S.relatorZero i)

/-- The explicit predecessor is a left inverse to vertex rotation. -/
theorem sigmaInvFun_sigmaFun (S : CactusShape) (d : CactusDart S) :
    S.sigmaInvFun (S.sigmaFun d) = d := by
  cases d with
  | outerForward j =>
      by_cases hj : j = S.boundaryZero
      · subst j
        by_cases hn : 0 < S.cellCount
        · simp [sigmaFun, sigmaInvFun, hn, boundaryZero, cellZero]
        · have hzero : S.cellCount = 0 := Nat.eq_zero_of_not_pos hn
          simp [sigmaFun, sigmaInvFun, hzero, nextFin_prevFin,
            boundaryZero]
      · simp [sigmaFun, sigmaInvFun, hj, nextFin_prevFin]
  | outerBackward j =>
      simp [sigmaFun, sigmaInvFun, prevFin_nextFin]
  | relatorForward i j =>
      by_cases hj : j = S.relatorZero i
      · subst j
        simp [sigmaFun, sigmaInvFun, relatorZero]
      · simp [sigmaFun, sigmaInvFun, hj, nextFin_prevFin]
  | relatorBackward i j =>
      simp [sigmaFun, sigmaInvFun, prevFin_nextFin]
  | stemOut i =>
      let hpos : 0 < S.cellCount := Nat.zero_lt_of_lt i.isLt
      by_cases hi : nextFin S.cellCount i = S.cellZero hpos
      · have hprev : prevFin S.cellCount (S.cellZero hpos) = i := by
          rw [← hi]
          exact prevFin_nextFin S.cellCount i
        rw [sigmaFun, dif_pos hi, sigmaInvFun]
        rw [dif_pos (nextFin_prevFin S.boundaryLength S.boundaryZero)]
        rw [dif_pos hpos]
        exact congrArg CactusDart.stemOut hprev
      · simp [sigmaFun, sigmaInvFun, hi, prevFin_nextFin]
  | stemIn i =>
      simp [sigmaFun, sigmaInvFun, nextFin_prevFin, relatorZero]

/-- The explicit predecessor is also a right inverse to vertex rotation. -/
theorem sigmaFun_sigmaInvFun (S : CactusShape) (d : CactusDart S) :
    S.sigmaFun (S.sigmaInvFun d) = d := by
  cases d with
  | outerForward j =>
      simp [sigmaFun, sigmaInvFun, nextFin_prevFin]
  | outerBackward j =>
      by_cases hj : nextFin S.boundaryLength j = S.boundaryZero
      · by_cases hn : 0 < S.cellCount
        · have hlast : nextFin S.cellCount
              (prevFin S.cellCount (S.cellZero hn)) = S.cellZero hn :=
            nextFin_prevFin S.cellCount (S.cellZero hn)
          have hprev : prevFin S.boundaryLength S.boundaryZero = j := by
            rw [← hj]
            exact prevFin_nextFin S.boundaryLength j
          rw [sigmaInvFun, dif_pos hj, dif_pos hn, sigmaFun]
          have htest : nextFin S.cellCount
              (prevFin S.cellCount (S.cellZero hn)) =
                S.cellZero (Nat.zero_lt_of_lt
                  (prevFin S.cellCount (S.cellZero hn)).isLt) := by
            calc
              nextFin S.cellCount (prevFin S.cellCount (S.cellZero hn)) =
                  S.cellZero hn := hlast
              _ = S.cellZero (Nat.zero_lt_of_lt
                    (prevFin S.cellCount (S.cellZero hn)).isLt) := by
                apply Fin.ext
                rfl
          rw [dif_pos htest]
          exact congrArg CactusDart.outerBackward hprev
        · have hprev : prevFin S.boundaryLength S.boundaryZero = j := by
            rw [← hj]
            exact prevFin_nextFin S.boundaryLength j
          rw [sigmaInvFun, dif_pos hj, dif_neg hn, sigmaFun]
          rw [dif_pos rfl, dif_neg hn]
          exact congrArg CactusDart.outerBackward hprev
      · simp [sigmaFun, sigmaInvFun, hj, prevFin_nextFin]
  | relatorForward i j =>
      simp [sigmaFun, sigmaInvFun, nextFin_prevFin]
  | relatorBackward i j =>
      by_cases hj : nextFin (S.relatorLength i) j = S.relatorZero i
      · have hprev : prevFin (S.relatorLength i) (S.relatorZero i) = j := by
          rw [← hj]
          exact prevFin_nextFin (S.relatorLength i) j
        rw [sigmaInvFun, dif_pos hj, sigmaFun]
        exact congrArg (CactusDart.relatorBackward i) hprev
      · simp [sigmaFun, sigmaInvFun, hj, prevFin_nextFin]
  | stemOut i =>
      let hpos : 0 < S.cellCount := Nat.zero_lt_of_lt i.isLt
      by_cases hi : i = S.cellZero hpos
      · rw [sigmaInvFun, dif_pos hi, sigmaFun, dif_pos rfl, dif_pos hpos]
        exact congrArg CactusDart.stemOut hi.symm
      · have hnext : nextFin S.cellCount (prevFin S.cellCount i) = i :=
          nextFin_prevFin S.cellCount i
        rw [sigmaInvFun, dif_neg hi, sigmaFun]
        have htest : nextFin S.cellCount (prevFin S.cellCount i) ≠
            S.cellZero (Nat.zero_lt_of_lt (prevFin S.cellCount i).isLt) := by
          intro hzero
          apply hi
          calc
            i = nextFin S.cellCount (prevFin S.cellCount i) := hnext.symm
            _ = S.cellZero (Nat.zero_lt_of_lt
                  (prevFin S.cellCount i).isLt) := hzero
            _ = S.cellZero hpos := by
              apply Fin.ext
              rfl
        rw [dif_neg htest]
        exact congrArg CactusDart.stemOut hnext
  | stemIn i =>
      simp [sigmaFun, sigmaInvFun, relatorZero]

/-- Vertex rotation as a permutation. -/
def sigma (S : CactusShape) : Perm (CactusDart S) where
  toFun := S.sigmaFun
  invFun := S.sigmaInvFun
  left_inv := S.sigmaInvFun_sigmaFun
  right_inv := S.sigmaFun_sigmaInvFun

/-- The closed combinatorial map of the cactus rotation system. -/
def toCombMap (S : CactusShape) : CombMap where
  Dart := CactusDart S
  dartFintype := inferInstance
  alpha := S.alpha
  sigma := S.sigma
  alpha_involutive := S.alphaFun_involutive
  alpha_fixedPointFree := S.alpha_fixedPointFree

end CactusShape

end VanKampen
end GGT
end GroupApproximation
