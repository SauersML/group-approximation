/-
Apache-2.0 source ported from `akopjan/HamSandwich` commit
`76202dbbb6610ffcebbccfbf7a56f833a4c2a376`.
-/
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic

/-!
# Affine barycentric subdivision maps on topological standard simplices

The v4.32 port replaces the final barycenter rewrite by an explicit `calc`.
This avoids a dependent rewrite regression while preserving the theorem.
-/

open scoped BigOperators
open Finset

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
namespace AffineBarycentricSubdivision

/-- The ambient topological `n`-simplex. -/
abbrev Delta (n : ℕ) := ↑(stdSimplex ℝ (Fin (n + 1)))

/-- The ordered prefix map associated to a permutation of the vertices. -/
def prefixVertex (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    Fin (k.val + 1) → Fin (n + 1) :=
  fun i ↦ π ⟨i.val, by
    have hi : i.val < k.val + 1 := i.isLt
    have hk : k.val < n + 1 := k.isLt
    omega⟩

/-- The barycenter of the first `k+1` vertices in the order given by `π`. -/
noncomputable def prefixBarycenter (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) : Delta n :=
  stdSimplex.map (S := ℝ) (prefixVertex n π k)
    (stdSimplex.barycenter (X := Fin (k.val + 1)) (𝕜 := ℝ))

/-- The defining formula for `prefixBarycenter`. -/
theorem prefixBarycenter_def (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) :
    prefixBarycenter n π k =
      stdSimplex.map (S := ℝ) (prefixVertex n π k)
        (stdSimplex.barycenter (X := Fin (k.val + 1)) (𝕜 := ℝ)) := rfl

/-- The coordinate function of the affine subdivision map. -/
noncomputable def affineSubdivMapFun (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (x : Delta n) : Fin (n + 1) → ℝ :=
  fun j ↦ ∑ k : Fin (n + 1), (x k) * (prefixBarycenter n π k j)

/-- Every coordinate of `affineSubdivMapFun` is nonnegative. -/
theorem affineSubdivMapFun_nonneg (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (x : Delta n) (j : Fin (n + 1)) :
    0 ≤ affineSubdivMapFun n π x j := by
  unfold affineSubdivMapFun
  exact Finset.sum_nonneg fun k _ ↦
    mul_nonneg (stdSimplex.zero_le x k) (stdSimplex.zero_le (prefixBarycenter n π k) j)

/-- The coordinates of `affineSubdivMapFun` sum to one. -/
theorem affineSubdivMapFun_sum_eq_one (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (x : Delta n) :
    (∑ j : Fin (n + 1), affineSubdivMapFun n π x j) = 1 := by
  unfold affineSubdivMapFun
  rw [Finset.sum_comm]
  have hk : ∀ k : Fin (n + 1),
      (∑ j : Fin (n + 1), x k * prefixBarycenter n π k j) = x k := by
    intro k
    rw [← Finset.mul_sum, stdSimplex.sum_eq_one, mul_one]
  rw [Finset.sum_congr rfl (fun k _ ↦ hk k)]
  exact stdSimplex.sum_eq_one x

/-- The affine self-map of the standard simplex associated to `π`. -/
noncomputable def affineSubdivMap (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    Delta n → Delta n :=
  fun x ↦ ⟨affineSubdivMapFun n π x,
    ⟨affineSubdivMapFun_nonneg n π x, affineSubdivMapFun_sum_eq_one n π x⟩⟩

@[simp] theorem affineSubdivMap_apply (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (x : Delta n) (j : Fin (n + 1)) :
    affineSubdivMap n π x j =
      ∑ k : Fin (n + 1), x k * prefixBarycenter n π k j := rfl

/-- Vertices map to the corresponding prefix barycenters. -/
theorem affineSubdivMap_vertex (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) :
    affineSubdivMap n π (stdSimplex.vertex (S := ℝ) k) = prefixBarycenter n π k := by
  apply stdSimplex.ext
  funext j
  simp only [affineSubdivMap_apply]
  rw [Finset.sum_eq_single k]
  · simp [stdSimplex.vertex]
  · intro b _ hb
    simp [stdSimplex.vertex, Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- Naturality under postcomposition of vertex permutations. -/
theorem prefixVertex_comp (n : ℕ) (π τ : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) :
    prefixVertex n (τ.trans π) k = fun i ↦ π (prefixVertex n τ k i) := by
  funext i
  rfl

/-- The first prefix barycenter is the first permuted vertex. -/
theorem prefixBarycenter_zero (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    prefixBarycenter n π 0 = stdSimplex.vertex (S := ℝ) (π 0) := by
  have hb : (stdSimplex.barycenter (X := Fin 1) (𝕜 := ℝ)) =
      stdSimplex.vertex (0 : Fin 1) := by
    apply stdSimplex.ext
    funext i
    fin_cases i
    simp [stdSimplex.barycenter, stdSimplex.vertex]
  calc
    prefixBarycenter n π 0 =
        stdSimplex.map (S := ℝ) (prefixVertex n π 0)
          (stdSimplex.vertex (0 : Fin 1)) :=
      congrArg (stdSimplex.map (S := ℝ) (prefixVertex n π 0)) hb
    _ = stdSimplex.vertex (S := ℝ) (prefixVertex n π 0 0) :=
      stdSimplex.map_vertex (S := ℝ) (prefixVertex n π 0) 0
    _ = stdSimplex.vertex (S := ℝ) (π 0) := by rfl

end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
