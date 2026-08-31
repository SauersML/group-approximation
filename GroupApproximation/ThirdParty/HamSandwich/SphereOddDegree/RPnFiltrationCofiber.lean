import Mathlib
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnInclusionCohomology
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.Hausdorff

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
* `rpLowerSubspace n : Set (RP (n+1))` — the image of `RPⁿ` inside `RPⁿ⁺¹`, the
  lower-dimensional projective subspace, with the identification
  `rpLowerSubspace_eq_image` (it is `proj (n+1)` of the equatorial sphere), and
  the point-set facts `isCompact_rpLowerSubspace` / `isClosed_rpLowerSubspace`.
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
-/

noncomputable section

open CategoryTheory

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ### The skeleta and the inclusion morphisms -/

/-- The `n`-skeleton of the real-projective filtration, as a `TopCat` object. -/
def RPnSkeleton (n : ℕ) : TopCat := TopCat.of (RP n)

@[simp]
theorem RPnSkeleton_carrier (n : ℕ) : (RPnSkeleton n : Type) = RP n := rfl

/-- The equatorial inclusion `RPⁿ ↪ RPⁿ⁺¹` is continuous. -/
theorem rpInclusion_continuous (n : ℕ) : Continuous (rpInclusion n) :=
  (rpInclusion n).continuous

/-- The equatorial inclusion `RPⁿ ↪ RPⁿ⁺¹` packaged as a `TopCat` morphism. -/
def rpInclusionHom (n : ℕ) : RPnSkeleton n ⟶ RPnSkeleton (n + 1) :=
  TopCat.ofHom (rpInclusion n)

@[simp]
theorem rpInclusionHom_apply (n : ℕ) (q : RP n) :
    (rpInclusionHom n) q = rpInclusion n q := rfl

/-- The inclusion morphism is a monomorphism in `TopCat` (it is injective). -/
theorem rpInclusionHom_mono (n : ℕ) : Mono (rpInclusionHom n) :=
  (TopCat.mono_iff_injective _).mpr (rpInclusion_injective n)

/-! ### The filtration as a functor `ℕ ⥤ TopCat` -/

/-- The real-projective filtration `RP⁰ ⊂ RP¹ ⊂ ⋯`, packaged as a functor from
the ordered category `ℕ` to `TopCat`. -/
def rpFiltration : ℕ ⥤ TopCat := Functor.ofSequence rpInclusionHom

@[simp]
theorem rpFiltration_obj (n : ℕ) : rpFiltration.obj n = RPnSkeleton n := rfl

/-- The successor step of the filtration functor is the equatorial inclusion. -/
theorem rpFiltration_map_succ (n : ℕ) :
    rpFiltration.map (homOfLE (Nat.le_succ n)) = rpInclusionHom n :=
  Functor.ofSequence_map_homOfLE_succ rpInclusionHom n

/-! ### The lower-dimensional projective subspace -/

/-- The image of `RPⁿ` inside `RPⁿ⁺¹` under the equatorial inclusion: the
lower-dimensional projective subspace. -/
def rpLowerSubspace (n : ℕ) : Set (RP (n + 1)) := Set.range (rpInclusion n)

/-- The lower subspace is exactly `proj (n+1)` applied to the equatorial sphere
`Sⁿ ⊂ Sⁿ⁺¹`: the expected description of `RPⁿ ⊂ RPⁿ⁺¹`. -/
theorem rpLowerSubspace_eq_image (n : ℕ) :
    rpLowerSubspace n = proj (n + 1) '' Set.range (sphereInclusion n) := by
  ext q
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨x, rfl⟩ := RP.exists_rep a
    exact ⟨sphereInclusion n x, ⟨x, rfl⟩, (rpInclusion_proj n x)⟩
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨proj n x, rpInclusion_proj n x⟩

/-- The lower projective subspace is compact (a continuous image of the compact
`RPⁿ`). -/
theorem isCompact_rpLowerSubspace (n : ℕ) : IsCompact (rpLowerSubspace n) := by
  rw [rpLowerSubspace, ← Set.image_univ]
  exact isCompact_univ.image (rpInclusion n).continuous

/-- The lower projective subspace is closed (compact in the Hausdorff `RPⁿ⁺¹`). -/
theorem isClosed_rpLowerSubspace (n : ℕ) : IsClosed (rpLowerSubspace n) :=
  (isCompact_rpLowerSubspace n).isClosed

/-! ### The cofiber `RPⁿ⁺¹ / RPⁿ` -/

/-- The setoid on `RPⁿ⁺¹` that collapses the lower subspace `RPⁿ` to a single
point: `x ~ y` iff `x = y` or both lie in the lower subspace. -/
def rpCofiberSetoid (n : ℕ) : Setoid (RP (n + 1)) where
  r x y := x = y ∨ (x ∈ rpLowerSubspace n ∧ y ∈ rpLowerSubspace n)
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
    (ha : a ∈ rpLowerSubspace n) (hb : b ∈ rpLowerSubspace n) :
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

/-- The last standard basis vector `e = (0,…,0,1)` of `ℝⁿ⁺²`. -/
def elast (n : ℕ) : EuclideanSpace ℝ (Fin (n + 2)) :=
  EuclideanSpace.single (Fin.last (n + 1)) 1

theorem elast_norm (n : ℕ) : ‖elast n‖ = 1 := by simp [elast]

theorem inner_elast (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 2))) :
    inner ℝ (elast n) v = v (Fin.last (n + 1)) := by
  rw [elast, EuclideanSpace.inner_single_left]; simp

/-- The raw collapse map `F(x) = 2⟪e,x⟫ • x − e` on the ambient sphere. -/
def cofiberRawMap (n : ℕ) (x : Sphere (n + 1)) : EuclideanSpace ℝ (Fin (n + 2)) :=
  (2 * inner ℝ (elast n) (x : EuclideanSpace ℝ (Fin (n + 2)))) •
      (x : EuclideanSpace ℝ (Fin (n + 2))) - elast n

theorem cofiberRawMap_norm (n : ℕ) (x : Sphere (n + 1)) : ‖cofiberRawMap n x‖ = 1 := by
  have hx : ‖(x : EuclideanSpace ℝ (Fin (n + 2)))‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
  have he : ‖elast n‖ = 1 := elast_norm n
  have hinner : inner ℝ (elast n) (x : EuclideanSpace ℝ (Fin (n+2)))
      = (x : EuclideanSpace ℝ (Fin (n+2))) (Fin.last (n+1)) := inner_elast n _
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
  ⟨-elast n, by rw [mem_sphere_zero_iff_norm, norm_neg]; exact elast_norm n⟩

theorem cofiberSphereMap_equator (n : ℕ) (y : Sphere n) :
    cofiberSphereMap n (sphereInclusion n y) = cofiberSouth n := by
  apply Subtype.ext
  rw [cofiberSphereMap_coe, cofiberRawMap]
  have ht : inner ℝ (elast n) ((sphereInclusion n y : EuclideanSpace ℝ (Fin (n+2)))) = 0 := by
    rw [inner_elast, sphereInclusion_apply_coe, inclIso_apply, inclLin_apply_last]
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
    (hq : q ∈ rpLowerSubspace n) : rpCollapseToSphere n q = cofiberSouth n := by
  rw [rpLowerSubspace_eq_image] at hq
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
A sphere point whose last coordinate vanishes lies on the equator, hence its
projective class lies in the lower subspace `RPⁿ ⊂ RPⁿ⁺¹`.
-/
theorem proj_mem_lowerSubspace_of_last_zero (n : ℕ) (x : Sphere (n + 1))
    (hx : (x : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1)) = 0) :
    proj (n + 1) x ∈ rpLowerSubspace n := by
  refine' ⟨ _, _ ⟩;
  exact proj n ⟨ ( x.1 |> fun y => WithLp.equiv 2 _ |>.symm <| Fin.init <| WithLp.equiv 2 _ y ), by
    cases x ; simp_all +decide [ EuclideanSpace.norm_eq, Fin.sum_univ_castSucc ];
    rename_i h; replace h := mem_sphere_zero_iff_norm.mp h; simp_all +decide [ EuclideanSpace.norm_eq, Fin.sum_univ_castSucc ] ;
    convert h using 1 ⟩;
  convert rpInclusion_proj n _;
  ext i; induction i using Fin.lastCases <;> aesop;

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
    convert congr_arg ( fun v => v + elast n ) h_eq_or_antipodal using 1 <;> norm_num [ cofiberRawMap ];
    · rw [ inner_elast ];
    · rw [ inner_elast ];
  by_cases h : ( x₁ : EuclideanSpace ℝ ( Fin ( n + 2 ) ) ) ( Fin.last ( n + 1 ) ) = 0 <;> by_cases h' : ( x₂ : EuclideanSpace ℝ ( Fin ( n + 2 ) ) ) ( Fin.last ( n + 1 ) ) = 0 <;> simp_all +decide [ mul_eq_zero ];
  · exact Quotient.sound ( Or.inr ⟨ proj_mem_lowerSubspace_of_last_zero n x₁ h, proj_mem_lowerSubspace_of_last_zero n x₂ h' ⟩ );
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
    · -- If $c = -1$, then $w = -elast n$.
      have hw_eq : w = -elast n := by
        have hw_neg : ‖(w : EuclideanSpace ℝ (Fin (n + 2))) - (-elast n)‖ ^ 2 = 0 := by
          rw [ @norm_sub_sq ℝ ] ; norm_num [ hw, elast ];
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
      -- Define `x.1 := (1/(2*t)) • ((w : _) + elast n)`.
      set x_val : EuclideanSpace ℝ (Fin (n + 2)) := (1 / (2 * t)) • ((w : EuclideanSpace ℝ (Fin (n + 2))) + elast n)
      have hx_val_norm : ‖x_val‖ = 1 := by
        have hx_val_norm : ‖(w : EuclideanSpace ℝ (Fin (n + 2))) + elast n‖^2 = 4 * t^2 := by
          rw [ @norm_add_sq ℝ ] ; norm_num [ elast ] ; ring_nf;
          rw [ EuclideanSpace.inner_single_right ] ; norm_num ; linarith!;
        rw [ norm_smul, Real.norm_of_nonneg ( by positivity ), div_mul_eq_mul_div, div_eq_iff ] <;> nlinarith [ norm_nonneg ( w + elast n ) ];
      refine' ⟨ ⟨ x_val, _ ⟩, _ ⟩ <;> simp_all +decide;
      ext i; simp [cofiberSphereMap, cofiberRawMap, x_val];
      simp +decide [ inner_add_right, inner_smul_right, elast ] ; ring_nf;
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
