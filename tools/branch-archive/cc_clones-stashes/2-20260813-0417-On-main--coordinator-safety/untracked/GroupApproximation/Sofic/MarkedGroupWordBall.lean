import GroupApproximation.Sofic.MarkedGroupTopology
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Finite reduced-word balls in marked-group space

This file gives an explicit finite enumeration of the elements of the free
group on `k` generators whose canonical reduced words have length at most
`R`.  The enumeration first lists all functions from a finite interval into
the signed generating alphabet and then applies `FreeGroup.mk`.

These word balls refine arbitrary finite relation cylinders, so they provide
the customary finite-radius neighborhoods in fixed-rank marked-group space.
-/

namespace GroupApproximation

namespace MarkedGroupSpace

variable {k : ℕ}

/-- Length of the canonical reduced word representing a free-group element. -/
def reducedWordLength (w : FreeGroup (Fin k)) : ℕ :=
  w.toWord.length

/-- An explicit code for a signed-generator word of length at most `R`.
The first coordinate records its length. -/
private abbrev BoundedWordCode (k R : ℕ) :=
  Σ n : Fin (R + 1), Fin n.1 → Fin k × Bool

/-- The finite ball of free-group elements whose canonical reduced-word
length is at most `R`.  It is constructed by evaluating all finite words of
all lengths at most `R`; no finiteness of an ambient infinite set is used. -/
def wordBall (k R : ℕ) : Finset (FreeGroup (Fin k)) :=
  Finset.univ.image fun code : BoundedWordCode k R =>
    FreeGroup.mk (List.ofFn code.2)

/-- Membership in `wordBall` is exactly the canonical reduced-length bound. -/
@[simp]
theorem mem_wordBall_iff (w : FreeGroup (Fin k)) (R : ℕ) :
    w ∈ wordBall k R ↔ reducedWordLength w ≤ R := by
  constructor
  · intro hw
    change w ∈ Finset.univ.image (fun code : BoundedWordCode k R =>
      FreeGroup.mk (List.ofFn code.2)) at hw
    obtain ⟨code, -, rfl⟩ := Finset.mem_image.mp hw
    calc
      reducedWordLength (FreeGroup.mk (List.ofFn code.2)) =
          FreeGroup.norm (FreeGroup.mk (List.ofFn code.2)) := rfl
      _ ≤ (List.ofFn code.2).length := FreeGroup.norm_mk_le
      _ = code.1 := List.length_ofFn
      _ ≤ R := Nat.lt_succ_iff.mp code.1.isLt
  · intro hw
    let n : Fin (R + 1) :=
      ⟨w.toWord.length, Nat.lt_succ_iff.mpr hw⟩
    let code : BoundedWordCode k R := ⟨n, w.toWord.get⟩
    change w ∈ Finset.univ.image (fun code : BoundedWordCode k R =>
      FreeGroup.mk (List.ofFn code.2))
    apply Finset.mem_image.mpr
    refine ⟨code, Finset.mem_univ code, ?_⟩
    change FreeGroup.mk (List.ofFn w.toWord.get) = w
    rw [List.ofFn_get, FreeGroup.mk_toWord]

/-- Every finite collection of free-group words is contained in a reduced
word ball of some finite radius. -/
theorem exists_subset_wordBall (F : Finset (FreeGroup (Fin k))) :
    ∃ R : ℕ, F ⊆ wordBall k R := by
  refine ⟨F.sum reducedWordLength, ?_⟩
  intro w hw
  rw [mem_wordBall_iff]
  exact Finset.single_le_sum
    (fun v _ => Nat.zero_le (reducedWordLength v)) hw

/-- Agreement on a word ball implies agreement on every finite subset of
that ball. -/
theorem cylinder_wordBall_subset_cylinder
    (M : MarkedGroupSpace k) (F : Finset (FreeGroup (Fin k))) (R : ℕ)
    (hF : F ⊆ wordBall k R) :
    cylinder M (wordBall k R) ⊆ cylinder M F := by
  intro N hN
  rw [mem_cylinder_iff] at hN ⊢
  exact fun w hw => hN w (hF hw)

end MarkedGroupSpace

end GroupApproximation
