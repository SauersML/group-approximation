import GroupApproximation.CharClass.CohomologyKunnethSphere

/-!
# The zero sphere, and Künneth with a sphere factor

`S⁰` is the two-point space `{±1} ⊂ ℝ`, covered by the two opens on which the
single coordinate is positive resp. negative.  Each piece is a nonempty
subsingleton, hence contractible, and the two are **disjoint**, so the
intersection contributes nothing: Mayer–Vietoris in the vanishing form gives
`H^{m+1}(A × S⁰; F₂) = 0` whenever `H^{m+1}(A; F₂) = 0`.  That is the base case
of the induction whose step is `isZero_prod_sphere_succ`, and the induction is
the Künneth vanishing statement with a sphere factor.

## Main declarations

* `sphereZeroPos`, `sphereZeroNeg` — the two opens, with `sphereZero_sup` and
  `sphereZero_inter_empty`.
* `isZero_prod_sphereZero` — the base case.
* `isZero_prod_sphere` — `H^k(A × S^n; F₂) = 0` for `k > p + n`, given that the
  cohomology of `A` vanishes above `p`.
-/

open CategoryTheory Limits TopologicalSpace Metric
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-! ## 1. The two-point structure of `S⁰` -/

/-- The norm on the one-dimensional Euclidean space is the absolute value of the
single coordinate. -/
theorem euclidean_one_norm (x : EuclideanSpace ℝ (Fin 1)) : ‖x‖ = |x 0| := by
  rw [EuclideanSpace.norm_eq]
  simp [Real.sqrt_sq_eq_abs]

theorem sphereZero_abs (p : Sphere 0) : |(p : EuclideanSpace ℝ (Fin 1)) 0| = 1 := by
  have h : ‖(p : EuclideanSpace ℝ (Fin 1))‖ = 1 := mem_sphere_zero_iff_norm.mp p.2
  rwa [euclidean_one_norm] at h

theorem sphereZero_coord_ne_zero (p : Sphere 0) : (p : EuclideanSpace ℝ (Fin 1)) 0 ≠ 0 := by
  intro h0
  have h := sphereZero_abs p
  rw [h0] at h
  simp at h

theorem sphereZero_ext {p q : Sphere 0}
    (h : (p : EuclideanSpace ℝ (Fin 1)) 0 = (q : EuclideanSpace ℝ (Fin 1)) 0) : p = q := by
  apply Subtype.ext
  ext i
  fin_cases i
  exact h

theorem continuous_sphereZeroCoord :
    Continuous fun p : Sphere 0 => (p : EuclideanSpace ℝ (Fin 1)) 0 :=
  (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp continuous_subtype_val

/-- The open half of `S⁰` on which the coordinate is positive. -/
def sphereZeroPos : Opens (Sphere 0) where
  carrier := {p | 0 < (p : EuclideanSpace ℝ (Fin 1)) 0}
  is_open' := isOpen_lt continuous_const continuous_sphereZeroCoord

/-- The open half of `S⁰` on which the coordinate is negative. -/
def sphereZeroNeg : Opens (Sphere 0) where
  carrier := {p | (p : EuclideanSpace ℝ (Fin 1)) 0 < 0}
  is_open' := isOpen_lt continuous_sphereZeroCoord continuous_const

theorem mem_sphereZeroPos {p : Sphere 0} :
    p ∈ (sphereZeroPos : Set (Sphere 0)) ↔ 0 < (p : EuclideanSpace ℝ (Fin 1)) 0 := Iff.rfl

theorem mem_sphereZeroNeg {p : Sphere 0} :
    p ∈ (sphereZeroNeg : Set (Sphere 0)) ↔ (p : EuclideanSpace ℝ (Fin 1)) 0 < 0 := Iff.rfl

theorem sphereZero_sup : sphereZeroPos ⊔ sphereZeroNeg = ⊤ := by
  apply Opens.ext
  apply Set.eq_univ_of_forall
  intro p
  rcases lt_or_gt_of_ne (sphereZero_coord_ne_zero p) with hlt | hgt
  · exact Set.mem_union_right _ (mem_sphereZeroNeg.mpr hlt)
  · exact Set.mem_union_left _ (mem_sphereZeroPos.mpr hgt)

theorem sphereZero_inter_empty :
    ((sphereZeroPos : Set (Sphere 0)) ∩ (sphereZeroNeg : Set (Sphere 0))) = ∅ := by
  ext p
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro h1 h2
  exact absurd (lt_trans (mem_sphereZeroPos.mp h1) (mem_sphereZeroNeg.mp h2)) (lt_irrefl 0)

instance nonempty_sphereZeroPos : Nonempty ↥(sphereZeroPos : Set (Sphere 0)) := by
  refine ⟨⟨⟨EuclideanSpace.single (0 : Fin 1) (1 : ℝ), ?_⟩, ?_⟩⟩
  · rw [mem_sphere_zero_iff_norm, euclidean_one_norm]
    simp
  · rw [mem_sphereZeroPos]
    simp

instance nonempty_sphereZeroNeg : Nonempty ↥(sphereZeroNeg : Set (Sphere 0)) := by
  refine ⟨⟨⟨EuclideanSpace.single (0 : Fin 1) (-1 : ℝ), ?_⟩, ?_⟩⟩
  · rw [mem_sphere_zero_iff_norm, euclidean_one_norm]
    simp
  · rw [mem_sphereZeroNeg]
    simp

instance subsingleton_sphereZeroPos : Subsingleton ↥(sphereZeroPos : Set (Sphere 0)) := by
  constructor
  rintro ⟨p, hp⟩ ⟨q, hq⟩
  apply Subtype.ext
  apply sphereZero_ext
  have hp' : (p : EuclideanSpace ℝ (Fin 1)) 0 = 1 := by
    have h1 := sphereZero_abs p
    rwa [abs_of_pos (mem_sphereZeroPos.mp hp)] at h1
  have hq' : (q : EuclideanSpace ℝ (Fin 1)) 0 = 1 := by
    have h1 := sphereZero_abs q
    rwa [abs_of_pos (mem_sphereZeroPos.mp hq)] at h1
  rw [hp', hq']

instance subsingleton_sphereZeroNeg : Subsingleton ↥(sphereZeroNeg : Set (Sphere 0)) := by
  constructor
  rintro ⟨p, hp⟩ ⟨q, hq⟩
  apply Subtype.ext
  apply sphereZero_ext
  have hp' : (p : EuclideanSpace ℝ (Fin 1)) 0 = -1 := by
    have h1 := sphereZero_abs p
    rw [abs_of_neg (mem_sphereZeroNeg.mp hp)] at h1
    linarith
  have hq' : (q : EuclideanSpace ℝ (Fin 1)) 0 = -1 := by
    have h1 := sphereZero_abs q
    rw [abs_of_neg (mem_sphereZeroNeg.mp hq)] at h1
    linarith
  rw [hp', hq']

/-! ## 2. The base case of the Künneth induction -/

set_option maxHeartbeats 1000000 in
/-- **`H^{m+1}(A × S⁰; F₂) = 0` whenever `H^{m+1}(A; F₂) = 0`.**  The two halves of
`S⁰` are contractible and disjoint. -/
theorem isZero_prod_sphereZero (A : Type) [TopologicalSpace A] (m : ℕ)
    (hA : IsZero (Hmod2 (TopCat.of A) (m + 1))) :
    IsZero (Hmod2 (TopCat.of (A × Sphere 0)) (m + 1)) := by
  refine isZero_mvAmbient (prodOpen A sphereZeroPos) (prodOpen A sphereZeroNeg)
    (prodOpen_sup A sphereZero_sup) m ?_
    (isZero_prodOpen_of_contractible A sphereZeroPos (m + 1) hA)
    (isZero_prodOpen_of_contractible A sphereZeroNeg (m + 1) hA)
  rw [prodOpen_coe_inter, sphereZero_inter_empty, Set.preimage_empty]
  exact isZero_cohomology_of_isEmpty _ m

/-! ## 3. Künneth with a sphere factor, in vanishing form -/

/-- **Künneth with a sphere factor, vanishing form.**  If the mod-2 cohomology of
`A` vanishes above degree `p`, then that of `A × S^n` vanishes above degree
`p + n`. -/
theorem isZero_prod_sphere (A : Type) [TopologicalSpace A] (p : ℕ)
    (hA : ∀ a, p < a → IsZero (Hmod2 (TopCat.of A) a)) :
    ∀ n k : ℕ, p + n < k → IsZero (Hmod2 (TopCat.of (A × Sphere n)) k) := by
  intro n
  induction n with
  | zero =>
      intro k hk
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      exact isZero_prod_sphereZero A m (hA (m + 1) (by omega))
  | succ n ih =>
      intro k hk
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      exact isZero_prod_sphere_succ A n m (ih m (by omega)) (hA (m + 1) (by omega))

/-- The same statement in the shape lane `cc-thom` asked for (`A2` with the second
factor a sphere). -/
theorem isZero_cohomology_prod_sphere (A : Type) [TopologicalSpace A] (p n : ℕ)
    (hA : ∀ a, p < a → IsZero (Hmod2 (TopCat.of A) a))
    (k : ℕ) (hk : p + n < k) :
    IsZero (Hmod2 (TopCat.of (A × Sphere n)) k) :=
  isZero_prod_sphere A p hA n k hk

end

end GroupApproximation.CharClass
