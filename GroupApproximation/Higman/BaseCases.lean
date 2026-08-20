import GroupApproximation.Higman.SequenceSpace
import GroupApproximation.Higman.BenignTorsionFree

/-!
# Higman's base cases

Higman builds every recursively enumerable set of sequences from two of them
by his operations, and the family of sets with benign subgroup has to contain
those two to start.  This file proves the first, `Z = {0}`, and records what
the second, `S = {(a, a+1) : a ∈ ℤ}`, needs.

`Z` is immediate once the dictionary is unwound: the zero sequence has empty
support, so `bElt 0 = 1` and `aElt 0 = a`, whence `A_Z = ⟨a⟩` is cyclic ---
finitely generated, therefore benign, with `F₃` itself as the witness.  Since
`F₃` is free it is torsion-free, so the witness is torsion-free too and the
case is settled for `REBenignTF` as well as for `REBenign`.

`S` is not immediate: Higman's witness is a nested HNN extension of `F₃` in
which `a_{(n,n+1)}` is a conjugate of `a_{(0,1)}` by the `n`-th power of a
product of two stable letters, so that `A_S = F₃ ∩ ⟨a_{(0,1)}, d₀d₁⟩` by the
collecting process --- the same shape as `Higman.Row.comap_Lsub`, which is
proved, but over a two-stable-letter extension whose base is `F₃` rather than
`⟨b, c⟩`.  It is not formalized here.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

open GroupApproximation.Higman.Conj

/-! ## 1.  The empty set -/

@[simp] theorem ASub_empty : ASub (∅ : Set E) = ⊥ := by
  unfold ASub
  rw [Set.image_empty, Subgroup.closure_empty]

theorem benignTF_ASub_empty : BenignTF (ASub (∅ : Set E)) := by
  rw [ASub_empty]
  exact benignTF_of_fg IsPowerTorsionFree.of_isMulTorsionFree fg_bot

/-! ## 2.  The zero sequence -/

@[simp] theorem elt_zero : elt (0 : E) = 1 := by
  simp [elt]

@[simp] theorem bElt_zero : bElt (0 : E) = 1 := by
  unfold bElt
  rw [elt_zero, map_one]

@[simp] theorem aElt_zero : aElt (0 : E) = a := by
  unfold aElt
  rw [bElt_zero, inv_one, one_mul, mul_one]

/-- Higman's set `Z`. -/
def Zset : Set E := {0}

theorem ASub_Zset : ASub Zset = Subgroup.closure {a} := by
  unfold ASub Zset
  congr 1
  refine Set.ext fun x => ?_
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [Set.mem_singleton_iff] at hf
    subst hf
    rw [aElt_zero]
    exact rfl
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨0, rfl, aElt_zero⟩

theorem fg_closure_a : (Subgroup.closure {a}).FG :=
  (Subgroup.fg_iff _).mpr ⟨{a}, rfl, Set.finite_singleton _⟩

/-- **Higman's base case `Z`.**  `A_Z = ⟨a⟩` is cyclic, hence benign, and the
witness `F₃` is free, hence torsion-free. -/
theorem benignTF_ASub_Zset : BenignTF (ASub Zset) := by
  rw [ASub_Zset]
  exact benignTF_of_fg IsPowerTorsionFree.of_isMulTorsionFree fg_closure_a

theorem benign_ASub_Zset : Benign (ASub Zset) :=
  (benignTF_ASub_Zset).toBenign

end Seq
end Higman
end GroupApproximation
