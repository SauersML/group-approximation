import GroupApproximation.Sofic.Sofic

/-!
# Finite-action characters and table holonomy

An exact action of a group on a finite set turns an arbitrary finite table in
that group into a permutation table.  The Hamming errors of the permutation
table are exactly the moved-point fractions of the corresponding holonomy
elements.  These identities isolate the table-dependent target in any attempt
to convert unitary microstates into sofic approximations.
-/

namespace GroupApproximation

/-- The fraction of a finite set fixed by a permutation. -/
noncomputable def fixedPointFraction (Y : FiniteModel) (p : Equiv.Perm Y) : ℝ :=
  ((Finset.univ.filter fun y ↦ p y = y).card : ℝ) / Fintype.card Y

/-- Hamming distance from the identity is the complementary fixed-point
fraction. -/
theorem hammingDistance_one_eq_one_sub_fixedPointFraction
    (Y : FiniteModel) (p : Equiv.Perm Y) (hY : 0 < Fintype.card Y) :
    hammingDistance Y p 1 = 1 - fixedPointFraction Y p := by
  unfold hammingDistance hammingDisagreement fixedPointFraction
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset Y)) (fun y : Y ↦ p y = y)
  have hcast :
      ((Finset.univ.filter fun y : Y ↦ p y = y).card : ℝ) +
          ((Finset.univ.filter fun y : Y ↦ p y ≠ y).card : ℝ) =
        Fintype.card Y := by
    exact_mod_cast hpartition
  have hcardR : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hY
  simp only [Equiv.Perm.one_apply]
  field_simp
  linarith

/-- For a homomorphism to a finite permutation group, the Hamming distance
between two images is the moved-point fraction of their quotient. -/
theorem hammingDistance_map_eq_one_sub_fixedPointFraction
    {G : Type*} [Group G] (Y : FiniteModel) (f : G →* Equiv.Perm Y)
    (a b : G) (hY : 0 < Fintype.card Y) :
    hammingDistance Y (f a) (f b) =
      1 - fixedPointFraction Y (f (b⁻¹ * a)) := by
  rw [← hammingDistance_left_invariant Y (f b)⁻¹ (f a) (f b)]
  simp only [← map_inv, ← map_mul, inv_mul_cancel, map_one]
  exact hammingDistance_one_eq_one_sub_fixedPointFraction Y _ hY

/-- If `u` is an arbitrary table in a group and `f` is an exact finite action,
the multiplication error of the induced permutation table is exactly the
moved-point fraction of the table's holonomy element. -/
theorem hammingDistance_table_mul_eq_one_sub_fixedPointFraction
    {G I : Type*} [Group G] (Y : FiniteModel) (f : G →* Equiv.Perm Y)
    (u : I → G) (product : I → I → I) (a b : I)
    (hY : 0 < Fintype.card Y) :
    hammingDistance Y (f (u a) * f (u b)) (f (u (product a b))) =
      1 - fixedPointFraction Y
        (f ((u (product a b))⁻¹ * (u a * u b))) := by
  rw [← map_mul]
  exact hammingDistance_map_eq_one_sub_fixedPointFraction
    Y f (u a * u b) (u (product a b)) hY

end GroupApproximation
