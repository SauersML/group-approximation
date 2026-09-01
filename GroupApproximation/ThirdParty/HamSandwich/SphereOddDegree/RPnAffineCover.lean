import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.SphereModTwoHomologyAboveDimension
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnFiltrationGeometry
import Mathlib

/-!
# The affine two-set cover of `RP (n+1)`

This file builds the point-set infrastructure for the standard affine two-set
open cover of `RP (n+1)`:

```text
U = RP^(n+1) \ {north projective point}
V = RP^(n+1) \ RP^n
```

`U` is `rpDeletedNorthOpen n` (the complement of the class of the last basis
vector) and `V` is `rpAffineCellOpen n` (the locus where the squared last
coordinate is nonzero, equivalently the complement of the lower projective
subspace `RP^n`).  The main result is the cover theorem
`rpDeletedNorth_sup_rpAffineCellOpen`.

The file also prepares the restricted quotient-map and coordinate infrastructure
used by later prompts: the sphere-level preimages of the two open sets, their
saturation under the antipodal map, and the fact that `proj (n+1)` restricts to a
quotient map over each of these open saturated sets.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ### A general restricted-quotient-map lemma -/

/-- If `f : X → Y` is a quotient map and `s` is open with `f ⁻¹' s = t`, then the
induced map `t → s`, `x ↦ f x`, is a quotient map.  This is the standard fact
that an open subset of a quotient carries the quotient topology from its
preimage. -/
theorem isQuotientMap_restrict_open_preimage
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Topology.IsQuotientMap f) {s : Set Y} (hs : IsOpen s)
    {t : Set X} (ht : f ⁻¹' s = t) :
    Topology.IsQuotientMap
      (fun x : t => (⟨f x.1, ht.ge x.2⟩ : s)) := by
  have hrp : Topology.IsQuotientMap (s.restrictPreimage f) :=
    hf.restrictPreimage_isOpen hs
  have he : Topology.IsQuotientMap (Homeomorph.setCongr ht.symm) :=
    (Homeomorph.setCongr ht.symm).isQuotientMap
  have hcomp := hrp.comp he
  have hfun :
      (fun x : t => (⟨f x.1, ht.ge x.2⟩ : s))
        = (s.restrictPreimage f) ∘ (Homeomorph.setCongr ht.symm) := by
    funext x
    apply Subtype.ext
    rfl
  rw [hfun]
  exact hcomp

/-! ### Coordinate definitions -/

/-- The last coordinate of a sphere point in `S^(n+1) ⊂ ℝ^(n+2)`. -/
noncomputable def sphereLastCoord (n : Nat) (x : Sphere (n + 1)) : Real :=
  (x : EuclideanSpace Real (Fin (n + 2))) (Fin.last (n + 1))

theorem sphereLastCoord_neg (n : Nat) (x : Sphere (n + 1)) :
    sphereLastCoord n (-x) = - sphereLastCoord n x := by
  simp [sphereLastCoord]

/-- The square of the last coordinate, descended to projective space.  Squaring
is essential: it is invariant under the antipodal map `x ↦ -x`. -/
noncomputable def rpLastCoordSq (n : Nat) : C(RP (n + 1), Real) where
  toFun := Quotient.lift
    (fun x : Sphere (n + 1) => (sphereLastCoord n x)^2)
    (by
      intro x y hxy
      rcases hxy with rfl | rfl
      · rfl
      · simp [sphereLastCoord])
  continuous_toFun := by
    apply Continuous.quotient_lift
    have hc : Continuous (fun x : Sphere (n + 1) => sphereLastCoord n x) := by
      unfold sphereLastCoord
      fun_prop
    exact hc.pow 2

@[simp]
theorem rpLastCoordSq_proj (n : Nat) (x : Sphere (n + 1)) :
    rpLastCoordSq n (proj (n + 1) x) = (sphereLastCoord n x) ^ 2 :=
  rfl

/-! ### North point -/

/-- The north pole of the sphere: the last standard basis vector. -/
def rpNorthSphere (n : Nat) : Sphere (n + 1) :=
  ⟨affineElast n, by
    rw [mem_sphere_zero_iff_norm]
    exact affineElast_norm n⟩

/-- The north projective point: the class of the north pole. -/
noncomputable def rpNorth (n : Nat) : RP (n + 1) :=
  proj (n + 1) (rpNorthSphere n)

theorem rpNorthSphere_last (n : Nat) :
    sphereLastCoord n (rpNorthSphere n) = 1 := by
  simp [sphereLastCoord, rpNorthSphere, affineElast]

theorem rpLastCoordSq_rpNorth (n : Nat) :
    rpLastCoordSq n (rpNorth n) = 1 := by
  rw [rpNorth, rpLastCoordSq_proj, rpNorthSphere_last]
  norm_num

/-! ### The affine cell and deleted-north open sets -/

/-- The affine cell `V`, as a subset: the locus where the squared last coordinate
is nonzero. -/
def rpAffineCellSet (n : Nat) : Set (RP (n + 1)) :=
  {q | rpLastCoordSq n q ≠ 0}

/-- The deleted-north set `U`, as a subset: the complement of the north point. -/
def rpDeletedNorthSet (n : Nat) : Set (RP (n + 1)) :=
  {q | q ≠ rpNorth n}

/-- The affine cell `V` as an open set. -/
noncomputable def rpAffineCellOpen (n : Nat) : Opens (TopCat.of (RP (n + 1))) :=
  ⟨rpAffineCellSet n, by
    simpa [rpAffineCellSet] using
      (isOpen_ne_fun (rpLastCoordSq n).continuous continuous_const)⟩

/-- The deleted-north set `U` as an open set. -/
noncomputable def rpDeletedNorthOpen (n : Nat) : Opens (TopCat.of (RP (n + 1))) :=
  ⟨rpDeletedNorthSet n, by
    have h : rpDeletedNorthSet n = ({rpNorth n} : Set (RP (n + 1)))ᶜ := by
      ext q; simp [rpDeletedNorthSet]
    rw [h]; exact isOpen_compl_singleton⟩

/-! ### Space abbreviations -/

abbrev rpAmbientSpace (n : Nat) : TopCat := TopCat.of (RP (n + 1))

abbrev rpDeletedNorthSpace (n : Nat) : Type :=
  (rpDeletedNorthOpen n : Set (rpAmbientSpace n))

abbrev rpAffineCellSpace (n : Nat) : Type :=
  (rpAffineCellOpen n : Set (rpAmbientSpace n))

abbrev rpAffineOverlapSet (n : Nat) : Set (RP (n + 1)) :=
  (rpDeletedNorthOpen n : Set (rpAmbientSpace n)) ∩
    (rpAffineCellOpen n : Set (rpAmbientSpace n))

abbrev rpAffineOverlapSpace (n : Nat) : Type :=
  rpAffineOverlapSet n

/-! ### Relation to the lower subspace -/

theorem sphereInclusion_last_zero (n : Nat) (y : Sphere n) :
    sphereLastCoord n (sphereInclusion n y) = 0 := by
  simp [sphereLastCoord, sphereInclusion_apply_coe, inclIso_apply, inclLin_apply_last]

theorem rpAffineCellSet_eq_compl_lower (n : Nat) :
    rpAffineCellSet n = (affineRpLowerSubspace n)ᶜ := by
  ext q
  obtain ⟨x, rfl⟩ := RP.exists_rep q
  rw [Set.mem_compl_iff, rpAffineCellSet, Set.mem_setOf_eq, rpLastCoordSq_proj,
    pow_ne_zero_iff (by norm_num)]
  constructor
  · intro hx hmem
    rw [affineRpLowerSubspace_eq_image] at hmem
    obtain ⟨w, ⟨y, rfl⟩, hyx⟩ := hmem
    rcases eq_or_eq_neg_of_proj_eq hyx with h | h
    · apply hx
      rw [← h, sphereInclusion_last_zero]
    · apply hx
      rw [show x = -(sphereInclusion n y) by rw [h, neg_neg],
        sphereLastCoord_neg, sphereInclusion_last_zero, neg_zero]
  · intro hx h0
    exact hx (proj_mem_affineLowerSubspace_of_last_zero n x h0)

/-- The affine cell open set as the complement of the lower subspace. -/
noncomputable def rpAffineCellOpen_alt (n : Nat) : Opens (TopCat.of (RP (n + 1))) :=
  ⟨(affineRpLowerSubspace n)ᶜ, (isClosed_affineRpLowerSubspace n).isOpen_compl⟩

theorem rpAffineCellOpen_eq_alt (n : Nat) :
    rpAffineCellOpen n = rpAffineCellOpen_alt n := by
  apply Opens.ext
  simp only [rpAffineCellOpen, rpAffineCellOpen_alt]
  exact rpAffineCellSet_eq_compl_lower n

/-! ### The cover theorem -/

theorem rpDeletedNorth_sup_rpAffineCellOpen (n : Nat) :
    rpDeletedNorthOpen n ⊔ rpAffineCellOpen n = ⊤ := by
  apply Opens.ext
  ext q
  constructor
  · intro _; trivial
  · intro _
    by_cases hq : q = rpNorth n
    · right
      simp [rpAffineCellOpen, rpAffineCellSet, hq, rpLastCoordSq_rpNorth]
    · left
      simpa [rpDeletedNorthOpen, rpDeletedNorthSet] using hq

/-! ### Restricted quotient-map infrastructure -/

/-- The preimage of the affine cell upstairs on the sphere. -/
def sphereAffineCellSet (n : Nat) : Set (Sphere (n + 1)) :=
  {x | sphereLastCoord n x ≠ 0}

/-- The preimage of the deleted-north set upstairs on the sphere. -/
def sphereDeletedNorthSet (n : Nat) : Set (Sphere (n + 1)) :=
  {x | proj (n + 1) x ≠ rpNorth n}

/-- The preimage of the overlap upstairs on the sphere. -/
def sphereAffineOverlapSet (n : Nat) : Set (Sphere (n + 1)) :=
  sphereAffineCellSet n ∩ sphereDeletedNorthSet n

theorem preimage_rpAffineCellSet (n : Nat) :
    (proj (n + 1)) ⁻¹' rpAffineCellSet n = sphereAffineCellSet n := by
  ext x
  simp only [Set.mem_preimage, rpAffineCellSet, sphereAffineCellSet, Set.mem_setOf_eq,
    rpLastCoordSq_proj, pow_ne_zero_iff (by norm_num : (2 : ℕ) ≠ 0)]

theorem preimage_rpDeletedNorthSet (n : Nat) :
    (proj (n + 1)) ⁻¹' rpDeletedNorthSet n = sphereDeletedNorthSet n := by
  rfl

theorem preimage_rpAffineOverlapSet (n : Nat) :
    (proj (n + 1)) ⁻¹' rpAffineOverlapSet n = sphereAffineOverlapSet n := by
  have h1 : (rpAffineOverlapSet n : Set (RP (n + 1)))
      = rpDeletedNorthSet n ∩ rpAffineCellSet n := rfl
  rw [h1, Set.preimage_inter, preimage_rpDeletedNorthSet, preimage_rpAffineCellSet,
    sphereAffineOverlapSet]
  exact Set.inter_comm _ _

theorem sphereAffineCellSet_neg_iff (n : Nat) (x : Sphere (n + 1)) :
    (-x ∈ sphereAffineCellSet n) ↔ x ∈ sphereAffineCellSet n := by
  simp [sphereAffineCellSet, sphereLastCoord_neg]

theorem sphereDeletedNorthSet_neg_iff (n : Nat) (x : Sphere (n + 1)) :
    (-x ∈ sphereDeletedNorthSet n) ↔ x ∈ sphereDeletedNorthSet n := by
  simp only [sphereDeletedNorthSet, Set.mem_setOf_eq, proj_neg]

theorem sphereAffineOverlapSet_neg_iff (n : Nat) (x : Sphere (n + 1)) :
    (-x ∈ sphereAffineOverlapSet n) ↔ x ∈ sphereAffineOverlapSet n := by
  simp only [sphereAffineOverlapSet, Set.mem_inter_iff, sphereAffineCellSet_neg_iff,
    sphereDeletedNorthSet_neg_iff]

theorem proj_restrict_affineCell_isQuotientMap (n : Nat) :
    Topology.IsQuotientMap
      (fun x : sphereAffineCellSet n =>
        (⟨proj (n + 1) x.1,
          by show proj (n + 1) x.1 ∈ rpAffineCellSet n
             rw [← Set.mem_preimage, preimage_rpAffineCellSet]; exact x.2⟩ :
          rpAffineCellSpace n)) :=
  isQuotientMap_restrict_open_preimage (proj_isQuotientMap (n + 1))
    (rpAffineCellOpen n).isOpen (preimage_rpAffineCellSet n)

theorem proj_restrict_deletedNorth_isQuotientMap (n : Nat) :
    Topology.IsQuotientMap
      (fun x : sphereDeletedNorthSet n =>
        (⟨proj (n + 1) x.1,
          by show proj (n + 1) x.1 ∈ rpDeletedNorthSet n
             rw [← Set.mem_preimage, preimage_rpDeletedNorthSet]; exact x.2⟩ :
          rpDeletedNorthSpace n)) :=
  isQuotientMap_restrict_open_preimage (proj_isQuotientMap (n + 1))
    (rpDeletedNorthOpen n).isOpen (preimage_rpDeletedNorthSet n)

theorem proj_restrict_overlap_isQuotientMap (n : Nat) :
    Topology.IsQuotientMap
      (fun x : sphereAffineOverlapSet n =>
        (⟨proj (n + 1) x.1,
          by show proj (n + 1) x.1 ∈ rpAffineOverlapSet n
             rw [← Set.mem_preimage, preimage_rpAffineOverlapSet]; exact x.2⟩ :
          rpAffineOverlapSpace n)) :=
  isQuotientMap_restrict_open_preimage (proj_isQuotientMap (n + 1))
    (by
      have : IsOpen (rpAffineOverlapSet n : Set (RP (n + 1))) :=
        (rpDeletedNorthOpen n).isOpen.inter (rpAffineCellOpen n).isOpen
      exact this)
    (preimage_rpAffineOverlapSet n)

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
