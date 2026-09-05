import Mathlib
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnFiltrationGeometry

/-!
# The `RPⁿ` filtration, equatorial inclusions, and the cofiber setup

This file packages the geometric filtration

```text
RP⁰ ⊂ RP¹ ⊂ ⋯ ⊂ RPⁿ ⊂ RPⁿ⁺¹ ⊂ ⋯
```

built from the equatorial projective inclusions `rpInclusion n : C(RP n, RP (n+1))`
(constructed in `RealProjectiveSpaceInclusion.lean`), and prepares the
quotient/cofiber step

```text
RPⁿ⁺¹ / RPⁿ ≃ Sⁿ⁺¹.
```

## What is built

* `RPnSkeleton n : TopCat` — the `n`-skeleton of the filtration, `TopCat.of (RP n)`.
* `rpInclusionHom n : RPnSkeleton n ⟶ RPnSkeleton (n+1)` — the equatorial
  inclusion as a `TopCat` morphism, together with `rpInclusion_continuous`,
  `rpInclusionHom_apply`, and the fact that it is a **monomorphism**
  (`rpInclusionHom_mono`).
* `rpFiltration : ℕ ⥤ TopCat` — the whole filtration packaged as a functor from
  the ordered category `ℕ` to `TopCat` (via `Functor.ofSequence`), with
  `rpFiltration_obj` and `rpFiltration_map_succ`.
* the lower-dimensional projective subspace — the image of `RPⁿ` inside `RPⁿ⁺¹` —
  is **not** redefined here. It is `affineRpLowerSubspace n : Set (RP (n+1))` from
  `RPnFiltrationGeometry.lean`, together with `affineRpLowerSubspace_eq_image`
  (it is `proj (n+1)` of the equatorial sphere) and the point-set facts
  `isCompact_affineRpLowerSubspace` / `isClosed_affineRpLowerSubspace`. The last
  basis vector and its pairing come from the same module: `affineElast n`,
  `affineElast_norm`, `inner_affineElast`.
* `rpCofiberSetoid n`, `rpCofiber n : TopCat` — the cofiber `RPⁿ⁺¹ / RPⁿ`, the
  quotient of `RPⁿ⁺¹` collapsing the lower subspace `RPⁿ` to a single point, with
  the collapse identity `rpCofiber_collapse` and the (continuous) quotient
  projection `rpCofiberProj`.
* `rpQuotientByLowerSkeleton_target n : Prop` — the **exact cofiber theorem**
  needed downstream: `Nonempty (rpCofiber n ≃ₜ Sⁿ⁺¹)`.

These are genuine topological objects with no placeholder content. The filtration
and the cofiber space are fully constructed and build-clean; the homeomorphism
`rpQuotientByLowerSkeleton_target` is the precisely-stated target the cofiber
identification supplies.

Porting changes for Mathlib v4.32 (no statement is changed):

* the skeleton/filtration block listed above (`RPnSkeleton`,
  `rpInclusion_continuous`, `rpInclusionHom`, `rpInclusionHom_apply`,
  `rpInclusionHom_mono`, `rpFiltration`, `rpFiltration_obj`,
  `rpFiltration_map_succ`) was described by this file's header but absent from
  its body: the vendored copy began at the cofiber section. It is restored here,
  built on Mathlib's `CategoryTheory.Functor.ofSequence`.
  `RPnCellularFiltration.lean` consumes `rpFiltration` and
  `rpFiltration_map_succ` directly, so the gap made that module unbuildable too.
* the lower-subspace and last-basis-vector references were spelled without the
  `affine` prefix that `RPnFiltrationGeometry.lean` gives them after namespace
  isolation (`rpLowerSubspace`, `elast`, `elast_norm`, `inner_elast`,
  `proj_mem_lowerSubspace_of_last_zero`). With `autoImplicit` on, each unresolved
  name was bound as a variable of unknown type rather than reported, so the file
  failed later and obscurely. They now name the declarations that exist. Rather
  than reintroduce a second copy of the same set under the unprefixed name, the
  header above records where they live.
* `inner_affineElast` — the pairing `⟪affineElast n, v⟫ = v (Fin.last (n+1))`,
  used by `cofiberRawMap_norm` and `cofiberSphereMap_equator` — had no
  counterpart at all and is added to `RPnFiltrationGeometry.lean`.
-/

noncomputable section

open CategoryTheory

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ### The skeleta and the filtration functor -/

/-- The `n`-skeleton of the projective filtration, as a `TopCat` object. -/
def RPnSkeleton (n : ℕ) : TopCat.{0} := TopCat.of (RP n)

/-- The equatorial projective inclusion is continuous (it is bundled as a
`ContinuousMap` in `RealProjectiveSpaceInclusion.lean`). -/
theorem rpInclusion_continuous (n : ℕ) : Continuous (rpInclusion n) :=
  (rpInclusion n).continuous

/-- The equatorial inclusion `RPⁿ ↪ RPⁿ⁺¹` as a morphism of `TopCat`. -/
def rpInclusionHom (n : ℕ) : RPnSkeleton n ⟶ RPnSkeleton (n + 1) :=
  TopCat.ofHom (rpInclusion n)

@[simp]
theorem rpInclusionHom_apply (n : ℕ) (x : RP n) :
    (rpInclusionHom n).hom x = rpInclusion n x := rfl

/-- The skeleton inclusion is a monomorphism: the equatorial inclusion is
injective (`rpInclusion_injective`). -/
instance rpInclusionHom_mono (n : ℕ) : Mono (rpInclusionHom n) :=
  (TopCat.mono_iff_injective (rpInclusionHom n)).mpr (rpInclusion_injective n)

/-- The whole projective filtration `RP⁰ ⊂ RP¹ ⊂ ⋯` as a functor `ℕ ⥤ TopCat`,
assembled from the equatorial inclusions. -/
def rpFiltration : ℕ ⥤ TopCat.{0} := Functor.ofSequence rpInclusionHom

@[simp]
theorem rpFiltration_obj (n : ℕ) : rpFiltration.obj n = RPnSkeleton n := rfl

/-- On a one-step inclusion the filtration functor is the equatorial inclusion. -/
theorem rpFiltration_map_succ (n : ℕ) :
    rpFiltration.map (homOfLE (Nat.le_succ n)) = rpInclusionHom n :=
  Functor.ofSequence_map_homOfLE_succ rpInclusionHom n

/-! ### The cofiber `RPⁿ⁺¹ / RPⁿ` -/

/-- The setoid on `RPⁿ⁺¹` that collapses the lower subspace `RPⁿ` to a single
point: `x ~ y` iff `x = y` or both lie in the lower subspace. -/
def rpCofiberSetoid (n : ℕ) : Setoid (RP (n + 1)) where
  r x y := x = y ∨ (x ∈ affineRpLowerSubspace n ∧ y ∈ affineRpLowerSubspace n)
  iseqv :=
    { refl := fun _ => Or.inl rfl
      symm := fun {x y} h =>
        h.elim (fun e => Or.inl e.symm) (fun ⟨hx, hy⟩ => Or.inr ⟨hy, hx⟩)
      trans := fun {x y z} h1 h2 => by
        rcases h1 with rfl | ⟨hx, hy⟩
        · exact h2
        · rcases h2 with rfl | ⟨_, hz⟩
          · exact Or.inr ⟨hx, hy⟩
          · exact Or.inr ⟨hx, hz⟩ }

/-- The cofiber `RPⁿ⁺¹ / RPⁿ`: the quotient of `RPⁿ⁺¹` collapsing the lower
projective subspace `RPⁿ` to a single point, as a `TopCat` object with the
quotient topology. -/
def rpCofiber (n : ℕ) : TopCat := TopCat.of (Quotient (rpCofiberSetoid n))

/-- The quotient projection `RPⁿ⁺¹ ↠ RPⁿ⁺¹ / RPⁿ`. -/
def rpCofiberProj (n : ℕ) : C(RP (n + 1), Quotient (rpCofiberSetoid n)) where
  toFun := Quotient.mk (rpCofiberSetoid n)
  continuous_toFun := continuous_quotient_mk'

/-- All points of the lower subspace are collapsed to the same point in the
cofiber. -/
theorem rpCofiber_collapse (n : ℕ) {a b : RP (n + 1)}
    (ha : a ∈ affineRpLowerSubspace n) (hb : b ∈ affineRpLowerSubspace n) :
    rpCofiberProj n a = rpCofiberProj n b :=
  Quotient.sound (Or.inr ⟨ha, hb⟩)

/-- The cofiber projection is surjective. -/
theorem rpCofiberProj_surjective (n : ℕ) : Function.Surjective (rpCofiberProj n) :=
  Quotient.mk_surjective

/-! ### The cofiber theorem (target for the next stage)

The cofiber `RPⁿ⁺¹ / RPⁿ` is homeomorphic to the sphere `Sⁿ⁺¹`.  This is the
precise statement the cellular/relative-cohomology computation consumes; the
filtration and cofiber objects above are exactly the data it is phrased over, so
the next stage can use it without rebuilding any of this infrastructure. -/

/-- **The exact cofiber theorem** needed downstream: the cofiber `RPⁿ⁺¹ / RPⁿ` is
homeomorphic to the sphere `Sⁿ⁺¹`. -/
def rpQuotientByLowerSkeleton_target (n : ℕ) : Prop :=
  Nonempty ((rpCofiber n : Type) ≃ₜ Sphere (n + 1))

/-! ### Construction of the cofiber homeomorphism `RPⁿ⁺¹ / RPⁿ ≃ Sⁿ⁺¹`

The collapse map is the explicit polynomial map `F(x) = 2⟪e, x⟫ • x − e`, where
`e` is the last standard basis vector of `ℝⁿ⁺²`.  It lands on the unit sphere
(`cofiberRawMap_norm`), is invariant under the antipodal map `x ↦ −x`
(`cofiberRawMap_neg`), collapses the equatorial `RPⁿ` — the points with vanishing
last coordinate — to the south pole `−e` (`cofiberSphereMap_equator`), and is
injective elsewhere.  As a continuous bijection from the compact cofiber to the
Hausdorff sphere it is a homeomorphism (`rpCofiberHomeo`). -/

/-- The raw collapse map `F(x) = 2⟪e,x⟫ • x − e` on the ambient sphere. -/
def cofiberRawMap (n : ℕ) (x : Sphere (n + 1)) : EuclideanSpace ℝ (Fin (n + 2)) :=
  (2 * inner ℝ (affineElast n) (x : EuclideanSpace ℝ (Fin (n + 2)))) •
      (x : EuclideanSpace ℝ (Fin (n + 2))) - affineElast n

theorem cofiberRawMap_norm (n : ℕ) (x : Sphere (n + 1)) : ‖cofiberRawMap n x‖ = 1 := by
  have hx : ‖(x : EuclideanSpace ℝ (Fin (n + 2)))‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
  have he : ‖affineElast n‖ = 1 := affineElast_norm n
  have hinner : inner ℝ (affineElast n) (x : EuclideanSpace ℝ (Fin (n+2)))
      = (x : EuclideanSpace ℝ (Fin (n+2))) (Fin.last (n+1)) := inner_affineElast n _
  have key : ‖cofiberRawMap n x‖ ^ 2 = 1 := by
    rw [cofiberRawMap, norm_sub_sq_real, norm_smul, inner_smul_left]
    simp only [RCLike.conj_to_real]
    rw [hinner, he, hx, real_inner_comm, hinner, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  nlinarith [norm_nonneg (cofiberRawMap n x), key]

theorem cofiberRawMap_continuous (n : ℕ) : Continuous (cofiberRawMap n) := by
  have h1 : Continuous (fun x : Sphere (n+1) => (x : EuclideanSpace ℝ (Fin (n+2)))) :=
    continuous_subtype_val
  exact ((continuous_const.mul (continuous_const.inner h1)).smul h1).sub continuous_const

/-- The collapse map as a continuous self-map of `Sⁿ⁺¹`. -/
def cofiberSphereMap (n : ℕ) : C(Sphere (n + 1), Sphere (n + 1)) where
  toFun x := ⟨cofiberRawMap n x, by
    rw [mem_sphere_zero_iff_norm]; exact cofiberRawMap_norm n x⟩
  continuous_toFun := (cofiberRawMap_continuous n).subtype_mk _

@[simp]
theorem cofiberSphereMap_coe (n : ℕ) (x : Sphere (n + 1)) :
    (cofiberSphereMap n x : EuclideanSpace ℝ (Fin (n + 2))) = cofiberRawMap n x := rfl

theorem cofiberRawMap_neg (n : ℕ) (x : Sphere (n + 1)) :
    cofiberRawMap n (-x) = cofiberRawMap n x := by
  have hc : ((-x : Sphere (n+1)) : EuclideanSpace ℝ (Fin (n+2)))
      = -(x : EuclideanSpace ℝ (Fin (n+2))) := by simp
  simp only [cofiberRawMap, hc, inner_neg_right, mul_neg, neg_smul, smul_neg, neg_neg]

theorem cofiberSphereMap_neg (n : ℕ) (x : Sphere (n + 1)) :
    cofiberSphereMap n (-x) = cofiberSphereMap n x :=
  Subtype.ext (cofiberRawMap_neg n x)

/-- The south pole `−e ∈ Sⁿ⁺¹`, the image of the collapsed equator. -/
def cofiberSouth (n : ℕ) : Sphere (n + 1) :=
  ⟨-affineElast n, by rw [mem_sphere_zero_iff_norm, norm_neg]; exact affineElast_norm n⟩

theorem cofiberSphereMap_equator (n : ℕ) (y : Sphere n) :
    cofiberSphereMap n (sphereInclusion n y) = cofiberSouth n := by
  apply Subtype.ext
  rw [cofiberSphereMap_coe, cofiberRawMap]
  have ht : inner ℝ (affineElast n) ((sphereInclusion n y : EuclideanSpace ℝ (Fin (n+2)))) = 0 := by
    rw [inner_affineElast, sphereInclusion_apply_coe, inclIso_apply, inclLin_apply_last]
  rw [ht]
  simp [cofiberSouth]

/-- The collapse map descended to `RPⁿ⁺¹` (it is antipodal-invariant). -/
def rpCollapseToSphere (n : ℕ) : C(RP (n + 1), Sphere (n + 1)) where
  toFun := Quotient.lift (cofiberSphereMap n) (by
    intro a b hab
    rcases hab with rfl | rfl
    · rfl
    · exact cofiberSphereMap_neg n b)
  continuous_toFun := (cofiberSphereMap n).continuous.quotient_lift _

@[simp]
theorem rpCollapseToSphere_proj (n : ℕ) (x : Sphere (n + 1)) :
    rpCollapseToSphere n (proj (n + 1) x) = cofiberSphereMap n x := rfl

theorem rpCollapseToSphere_lowerSubspace (n : ℕ) {q : RP (n + 1)}
    (hq : q ∈ affineRpLowerSubspace n) : rpCollapseToSphere n q = cofiberSouth n := by
  rw [affineRpLowerSubspace_eq_image] at hq
  obtain ⟨w, ⟨z, rfl⟩, rfl⟩ := hq
  rw [rpCollapseToSphere_proj]
  exact cofiberSphereMap_equator n z

/-- The collapse map descended through the cofiber quotient `RPⁿ⁺¹ / RPⁿ`. -/
def cofiberToSphere (n : ℕ) : C(Quotient (rpCofiberSetoid n), Sphere (n + 1)) where
  toFun := Quotient.lift (rpCollapseToSphere n) (by
    intro a b hab
    rcases hab with rfl | ⟨ha, hb⟩
    · rfl
    · rw [rpCollapseToSphere_lowerSubspace n ha, rpCollapseToSphere_lowerSubspace n hb])
  continuous_toFun := (rpCollapseToSphere n).continuous.quotient_lift _

@[simp]
theorem cofiberToSphere_mk (n : ℕ) (q : RP (n + 1)) :
    cofiberToSphere n (Quotient.mk (rpCofiberSetoid n) q) = rpCollapseToSphere n q := rfl

/-
The collapse map is injective on the cofiber: if two classes have the same
image on `Sⁿ⁺¹`, they are equal in `RPⁿ⁺¹ / RPⁿ`.
-/
theorem cofiberToSphere_injective (n : ℕ) : Function.Injective (cofiberToSphere n) := by
  intro x y hxy;
  obtain ⟨q₁, rfl⟩ := Quotient.exists_rep x
  obtain ⟨q₂, rfl⟩ := Quotient.exists_rep y
  obtain ⟨x₁, rfl⟩ := RP.exists_rep q₁
  obtain ⟨x₂, rfl⟩ := RP.exists_rep q₂
  simp_all +decide;
  have h_eq_or_antipodal : (2 * (x₁ : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1))) • (x₁ : EuclideanSpace ℝ (Fin (n + 2))) = (2 * (x₂ : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1))) • (x₂ : EuclideanSpace ℝ (Fin (n + 2))) := by
    have h_eq_or_antipodal : cofiberRawMap n x₁ = cofiberRawMap n x₂ := by
      convert congr_arg Subtype.val hxy using 1;
    convert congr_arg ( fun v => v + affineElast n ) h_eq_or_antipodal using 1 <;> norm_num [ cofiberRawMap ];
    · rw [ inner_affineElast ];
    · rw [ inner_affineElast ];
  by_cases h : ( x₁ : EuclideanSpace ℝ ( Fin ( n + 2 ) ) ) ( Fin.last ( n + 1 ) ) = 0 <;> by_cases h' : ( x₂ : EuclideanSpace ℝ ( Fin ( n + 2 ) ) ) ( Fin.last ( n + 1 ) ) = 0 <;> simp_all +decide [ mul_eq_zero ];
  · exact Quotient.sound ( Or.inr ⟨ proj_mem_affineLowerSubspace_of_last_zero n x₁ h, proj_mem_affineLowerSubspace_of_last_zero n x₂ h' ⟩ );
  · rw [ eq_comm, smul_eq_zero ] at h_eq_or_antipodal ; aesop;
  · have h_eq_or_antipodal : (x₁ : EuclideanSpace ℝ (Fin (n + 2))) = (x₂ : EuclideanSpace ℝ (Fin (n + 2))) ∨ (x₁ : EuclideanSpace ℝ (Fin (n + 2))) = -(x₂ : EuclideanSpace ℝ (Fin (n + 2))) := by
      have h_eq_or_antipodal : (x₁ : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1)) = (x₂ : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1)) ∨ (x₁ : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1)) = -(x₂ : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1)) := by
        replace h_eq_or_antipodal := congr_arg ( fun v => v ( Fin.last ( n + 1 ) ) ) h_eq_or_antipodal ; simp_all +decide [ mul_comm, mul_left_comm ];
        exact eq_or_eq_neg_of_sq_eq_sq _ _ <| by linear_combination' h_eq_or_antipodal;
      cases h_eq_or_antipodal <;> simp_all +decide;
      exact Or.inr ( by ext i; have := congr_arg ( fun v => v i ) h_eq_or_antipodal; norm_num at *; cases lt_or_gt_of_ne h' <;> nlinarith );
    cases h_eq_or_antipodal <;> simp_all +decide [ Quotient.eq ];
    · exact Or.inl ( by aesop );
    · exact Or.inl ( by rw [ show x₁ = -x₂ from Subtype.ext ‹_› ] ; exact proj_neg x₂ )

/-
The collapse map is surjective onto `Sⁿ⁺¹`.
-/
theorem cofiberToSphere_surjective (n : ℕ) : Function.Surjective (cofiberToSphere n) := by
  intro w
  obtain ⟨x, hx⟩ : ∃ x : Sphere (n + 1), cofiberSphereMap n x = w := by
    by_cases hw : (w : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1)) = -1;
    · -- If $c = -1$, then $w = -affineElast n$.
      have hw_eq : w = -affineElast n := by
        have hw_neg : ‖(w : EuclideanSpace ℝ (Fin (n + 2))) - (-affineElast n)‖ ^ 2 = 0 := by
          rw [ @norm_sub_sq ℝ ] ; norm_num [ hw, affineElast ];
          rw [ EuclideanSpace.inner_single_right ] ; norm_num [ hw ];
        exact sub_eq_zero.mp ( norm_eq_zero.mp ( sq_eq_zero_iff.mp hw_neg ) );
      use sphereInclusion n ⟨EuclideanSpace.single (Fin.last n) 1, by
        norm_num [ EuclideanSpace.norm_eq ]⟩
      generalize_proofs at *;
      convert cofiberSphereMap_equator n ⟨ EuclideanSpace.single ( Fin.last n ) 1, by assumption ⟩ using 1;
      exact Subtype.ext hw_eq;
    · -- Set `t := Real.sqrt ((c+1)/2) > 0`, so `2 * t^2 = c + 1` and `t > 0`.
      set t := Real.sqrt (((w : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1)) + 1) / 2)
      have ht_pos : 0 < t := by
        have h_abs : |(w : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1))| ≤ 1 := by
          have h_abs : ‖(w : EuclideanSpace ℝ (Fin (n + 2)))‖ = 1 := by
            exact mem_sphere_zero_iff_norm.mp w.2;
          convert h_abs ▸ ( abs_real_inner_le_norm ( w : EuclideanSpace ℝ ( Fin ( n + 2 ) ) ) ( EuclideanSpace.single ( Fin.last ( n + 1 ) ) 1 ) ) using 1;
          · simp +decide [ inner ];
          · norm_num [ EuclideanSpace.norm_eq ];
        exact Real.sqrt_pos.mpr ( by cases lt_or_gt_of_ne hw <;> linarith [ abs_le.mp h_abs ] )
      have ht_sq : 2 * t^2 = (w : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1)) + 1 := by
        rw [ Real.sq_sqrt ];
        · ring;
        · exact le_of_not_gt fun h => ht_pos.ne' <| Real.sqrt_eq_zero_of_nonpos h.le;
      -- Define `x.1 := (1/(2*t)) • ((w : _) + affineElast n)`.
      set x_val : EuclideanSpace ℝ (Fin (n + 2)) := (1 / (2 * t)) • ((w : EuclideanSpace ℝ (Fin (n + 2))) + affineElast n)
      have hx_val_norm : ‖x_val‖ = 1 := by
        have hx_val_norm : ‖(w : EuclideanSpace ℝ (Fin (n + 2))) + affineElast n‖^2 = 4 * t^2 := by
          rw [ @norm_add_sq ℝ ] ; norm_num [ affineElast ] ; ring_nf;
          rw [ EuclideanSpace.inner_single_right ] ; norm_num ; linarith!;
        rw [ norm_smul, Real.norm_of_nonneg ( by positivity ), div_mul_eq_mul_div, div_eq_iff ] <;> nlinarith [ norm_nonneg ( w + affineElast n ) ];
      refine' ⟨ ⟨ x_val, _ ⟩, _ ⟩ <;> simp_all +decide;
      ext i; simp [cofiberSphereMap, cofiberRawMap, x_val];
      simp +decide [ inner_add_right, inner_smul_right, affineElast ] ; ring_nf;
      split_ifs <;> simp_all +decide [ inner ]; all_goals grind;
  use Quotient.mk _ (proj (n + 1) x);
  convert hx using 1

/-- The cofiber-to-sphere bijection. -/
def rpCofiberEquiv (n : ℕ) : Quotient (rpCofiberSetoid n) ≃ Sphere (n + 1) :=
  Equiv.ofBijective (cofiberToSphere n)
    ⟨cofiberToSphere_injective n, cofiberToSphere_surjective n⟩

/-- **The cofiber homeomorphism** `RPⁿ⁺¹ / RPⁿ ≃ₜ Sⁿ⁺¹`: a continuous bijection
from the compact cofiber to the Hausdorff sphere. -/
def rpCofiberHomeo (n : ℕ) : Quotient (rpCofiberSetoid n) ≃ₜ Sphere (n + 1) :=
  Continuous.homeoOfEquivCompactToT2 (f := rpCofiberEquiv n) (cofiberToSphere n).continuous

/-- The exact cofiber theorem is proved: `RPⁿ⁺¹ / RPⁿ ≃ₜ Sⁿ⁺¹`. -/
theorem rpQuotientByLowerSkeleton (n : ℕ) : rpQuotientByLowerSkeleton_target n :=
  ⟨rpCofiberHomeo n⟩

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
