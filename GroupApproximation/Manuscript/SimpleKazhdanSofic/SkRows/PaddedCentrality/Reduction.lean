import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.PaddedCentrality.Statement

/-!
# Padded centrality from the column/row action (lane `sk-rows-14`)

Khanh, arXiv:2609.08428, Lemma 5.6: for every ring `R` and every `m`, the stabilized image
`stab (K₂(m, R))` is central in `St_{m+1}(R)`.

## Route

Let `y ∈ K₂(m, R)`, so `projection y = 1` and also `projection y⁻¹ = 1`.  The column/row action
formula (lane `sk-rows-13`, `SteinbergColumnActionStatement`) at the identity matrix collapses
to `stab y · s · (stab y)⁻¹ = s` for every boundary root `s` (`prod_colRoot_one`,
`prod_rowRoot_one`).  The boundary roots generate `St_{m+1}(R)` (`closure_boundaryRoots_eq_top`),
so `stab y` is central (`mem_center_of_commute_boundaryRoots`).

## Endpoint and remaining gap

* `stab_K2_le_center_of_columnAction` : `SteinbergColumnActionStatement m R →
  PaddedCentralityStatement m R`.
* The lane text carries the hypothesis `2 ≤ m`.  It is not needed, so it is omitted.  This gives
  a stronger theorem; for `m ≤ 1` the group `K₂(m, R)` is trivial anyway.
* Not closed unconditionally.  Lane `sk-rows-13` is not on disk, so its interface is assumed.
  `SteinbergColumnActionStatement` is strictly smaller in proof content than the target, and true
  (see the truth check in `PaddedCentrality.Statement`).  It is *not* an equivalent restatement.
  It is a conjugation formula for *all* `y ∈ St_m(R)`, proved by induction over Steinberg words
  from the commutator relations.  The present reduction adds the generation of `St_{m+1}(R)` by
  boundary roots and the collapse at `M = 1`.  Once lane 13 lands, the unconditional form is
  `stab_K2_le_center_of_columnAction m R <lane 13 theorem>`, up to matching its product
  convention.
-/

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedCentrality

open GroupApproximation.BooneHigman.SteinbergBasic

variable {m : ℕ} {R : Type*} [Ring R]

/-- Under the column/row action formula, `stab y` fixes every boundary root for `y ∈ K₂(m, R)`. -/
theorem stab_commute_boundaryRoots_of_columnAction (h : SteinbergColumnActionStatement m R)
    {y : St m R} (hy : y ∈ K2n m R) :
    ∀ s ∈ boundaryRoots m R, stab m R y * s = s * stab m R y := by
  have hM : projectionMatrix m R y = 1 := projectionMatrix_eq_one_of_mem_K2 hy
  have hMinv : projectionMatrix m R y⁻¹ = 1 :=
    projectionMatrix_eq_one_of_mem_K2 (inv_mem hy)
  rintro _ (⟨i, a, rfl⟩ | ⟨i, a, rfl⟩)
  · have hcol := (h y i a).1
    rw [hM, prod_colRoot_one] at hcol
    exact mul_inv_eq_iff_eq_mul.mp hcol
  · have hrow := (h y i a).2
    rw [hMinv, prod_rowRoot_one] at hrow
    exact mul_inv_eq_iff_eq_mul.mp hrow

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedCentrality.stab_commute_boundaryRoots_of_columnAction

variable (m R)

/-- **Khanh's padded centrality, reduced to the column/row action (lane 13).**  For every ring `R`
and every `m`, `stab (K₂(m, R)) ≤ Z(St_{m+1}(R))`. -/
theorem stab_K2_le_center_of_columnAction (h : SteinbergColumnActionStatement m R) :
    (K2n m R).map (stab m R) ≤ Subgroup.center (St (m + 1) R) := by
  rintro _ ⟨y, hy, rfl⟩
  exact mem_center_of_commute_boundaryRoots (stab m R y)
    (stab_commute_boundaryRoots_of_columnAction h hy)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedCentrality.stab_K2_le_center_of_columnAction

/-- The same reduction, phrased with the named target `PaddedCentralityStatement`. -/
theorem paddedCentralityStatement_of_columnAction (h : SteinbergColumnActionStatement m R) :
    PaddedCentralityStatement m R :=
  stab_K2_le_center_of_columnAction m R h

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedCentrality.paddedCentralityStatement_of_columnAction

end GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedCentrality
