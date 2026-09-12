import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnAffineCover
import Mathlib

/-!
# The deleted-north chart of `RP (n+1)` deformation retracts onto `RP n`

We prove that the deleted-north chart `U = RP^(n+1) \ {north point}`
(`rpDeletedNorthSpace n`) is homotopy equivalent to the lower projective subspace
`RP n`.

The construction is performed upstairs on the antipodal-saturated *band*

```text
sphereDeletedNorthSet n = S^(n+1) \ {±e_last}
```

which is homotopy equivalent to `S^n` by dropping the last coordinate and
normalizing.  All the maps and the homotopy are odd (antipodal-equivariant), so
they descend to the projective quotients, yielding
`rpDeletedNorth_homotopyEquiv_lower`.
-/

noncomputable section

open CategoryTheory TopologicalSpace Metric Topology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

variable (n : Nat)

/-! ## The lower squared-norm on the band -/

/-- The squared norm of the first `n+1` coordinates of a point of `S^(n+1)`. -/
noncomputable def lowerNormSq (n : Nat) (x : Sphere (n + 1)) : Real :=
  ∑ i : Fin (n + 1),
    ((x : EuclideanSpace Real (Fin (n + 2))) i.castSucc)^2

theorem lowerNormSq_eq_one_sub_last_sq (n : Nat) (x : Sphere (n + 1)) :
    lowerNormSq n x = 1 - (sphereLastCoord n x)^2 := by
  have h_sum : ∑ i : Fin (n + 2), (x.val i)^2 = 1 := by
    convert congr_arg ( fun y : ℝ => y ^ 2 ) ( show ‖x.val‖ = 1 from by simp ) using 1;
    · rw [ EuclideanSpace.norm_eq ] ; norm_num [ Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ];
    · norm_num;
  rw [ ← h_sum, Fin.sum_univ_castSucc ];
  unfold lowerNormSq sphereLastCoord; ring;

/-
If the last coordinate has squared value `1`, the point projects to the north
point.
-/
theorem mem_sphereDeletedNorth_of_last_zero (n : Nat) (z : Sphere (n + 1))
    (hz : sphereLastCoord n z = 0) : z ∈ sphereDeletedNorthSet n := by
  intro h_eq;
  have := rpLastCoordSq_proj n z; have := rpLastCoordSq_rpNorth n; simp_all +decide ;

/-
If some lower coordinate is nonzero, the point is not the north point (up to
sign), hence lies in the deleted-north band.
-/
theorem mem_sphereDeletedNorth_of_castSucc_ne_zero (n : Nat) (z : Sphere (n + 1))
    (i : Fin (n + 1)) (hz : (z : EuclideanSpace Real (Fin (n + 2))) i.castSucc ≠ 0) :
    z ∈ sphereDeletedNorthSet n := by
  contrapose! hz;
  cases' eq_or_eq_neg_of_proj_eq ( n := n + 1 ) ( show proj ( n + 1 ) z = proj ( n + 1 ) ⟨ affineElast n, by rw [ mem_sphere_zero_iff_norm ] ; exact affineElast_norm n ⟩ from Classical.not_not.1 hz ) with h h <;> simp_all +decide [ affineElast ]

theorem lowerNormSq_pos_of_deletedNorth
    (n : Nat) (x : Sphere (n + 1))
    (hx : x ∈ sphereDeletedNorthSet n) :
    0 < lowerNormSq n x := by
  contrapose! hx;
  -- Since `lowerNormSq n x ≤ 0`, we have `x.val i.castSucc = 0` for all `i : Fin (n + 1)`.
  have h_castSucc_zero : ∀ i : Fin (n + 1), (x : EuclideanSpace ℝ (Fin (n + 2))) i.castSucc = 0 := by
    exact fun i => sq_eq_zero_iff.mp ( le_antisymm ( le_trans ( Finset.single_le_sum ( fun a _ => sq_nonneg ( x.val ( Fin.castSucc a ) ) ) ( Finset.mem_univ i ) ) hx ) ( sq_nonneg _ ) );
  -- Since `x.val i.castSucc = 0` for all `i : Fin (n + 1)`, we have `x = ± affineElast n`.
  have h_x_eq_elast : x = affineElast n ∨ x = -affineElast n := by
    have h_x_eq_elast : (x : EuclideanSpace ℝ (Fin (n + 2))) = (sphereLastCoord n x) • affineElast n := by
      ext i; by_cases hi : i.val < n + 1 <;> simp_all +decide [ Fin.ext_iff, affineElast ] ;
      · rw [ if_neg ( by linarith ) ] ; exact h_castSucc_zero ⟨ i, by linarith ⟩;
      · simp_all +decide [ Fin.eq_last_of_not_lt ];
        rfl;
    have h_x_eq_elast : (sphereLastCoord n x)^2 = 1 := by
      have := congr_arg ( fun y => ‖y‖ ^ 2 ) h_x_eq_elast ; norm_num at this;
      rw [ norm_smul, Real.norm_eq_abs, affineElast_norm ] at this ; norm_num at this ; linarith;
    cases eq_or_eq_neg_of_sq_eq_sq ( sphereLastCoord n x ) 1 ( by linarith ) <;> aesop ( simp_config := { singlePass := true } ) ;
  have hp : proj (n + 1) x = rpNorth n := by
    rcases h_x_eq_elast with h | h
    · have hxN : x = rpNorthSphere n := by
        apply Subtype.ext
        exact h
      rw [hxN]
      rfl
    · have hxN : x = -(rpNorthSphere n) := by
        apply Subtype.ext
        exact h
      rw [hxN, proj_neg]
      rfl
  simpa only [sphereDeletedNorthSet, Set.mem_setOf_eq, not_ne_iff] using hp

/-! ## The band → `S^n` map -/

/-- Drop the last coordinate of a band point and normalize. -/
noncomputable def deletedNorthBandToSphereFun
    (n : Nat) (x : sphereDeletedNorthSet n) : EuclideanSpace Real (Fin (n + 1)) :=
  (WithLp.equiv 2 (Fin (n + 1) → Real)).symm
    (fun i =>
      ((x.1 : EuclideanSpace Real (Fin (n + 2))) i.castSucc) /
        Real.sqrt (lowerNormSq n x.1))

theorem deletedNorthBandToSphereFun_mem
    (n : Nat) (x : sphereDeletedNorthSet n) :
    deletedNorthBandToSphereFun n x ∈
      Metric.sphere (0 : EuclideanSpace Real (Fin (n + 1))) 1 := by
  unfold deletedNorthBandToSphereFun;
  simp +decide [ EuclideanSpace.norm_eq ];
  norm_num [ div_pow, Real.sq_sqrt <| show 0 ≤ lowerNormSq n x from Finset.sum_nonneg fun _ _ => sq_nonneg _ ];
  rw [ ← Finset.sum_div _ _ _, div_eq_iff ] <;> norm_num [ lowerNormSq ];
  exact ne_of_gt ( lowerNormSq_pos_of_deletedNorth n x x.2 )

theorem continuous_deletedNorthBandToSphere (n : Nat) :
    Continuous (fun x : sphereDeletedNorthSet n =>
      (⟨deletedNorthBandToSphereFun n x, deletedNorthBandToSphereFun_mem n x⟩ : Sphere n)) := by
  all_goals generalize_proofs at *;
  refine' Continuous.subtype_mk _ _;
  -- The function `deletedNorthBandToSphereFun n` is continuous because it is a composition of continuous functions.
  have h_cont : Continuous (fun x : sphereDeletedNorthSet n => (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (fun i => (x.1.1 i.castSucc) / Real.sqrt (lowerNormSq n x.1))) := by
    have h_cont_lowerNormSq : Continuous (fun x : sphereDeletedNorthSet n => lowerNormSq n x.1) := by
      refine' continuous_finsetSum _ fun i _ => Continuous.pow _ _;
      fun_prop
    have h_cont_div : Continuous (fun x : sphereDeletedNorthSet n => fun i : Fin (n + 1) => (x.1.1 i.castSucc) / Real.sqrt (lowerNormSq n x.1)) := by
      refine' continuous_pi fun i => Continuous.div _ _ _;
      · fun_prop;
      · exact Real.continuous_sqrt.comp h_cont_lowerNormSq;
      · exact fun x => ne_of_gt <| Real.sqrt_pos.mpr <| lowerNormSq_pos_of_deletedNorth n x.1 x.2
    generalize_proofs at *;
    exact continuous_induced_rng.mpr h_cont_div
  generalize_proofs at *;
  change Continuous (fun x : sphereDeletedNorthSet n =>
    (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm
      (fun i => x.1.1 i.castSucc / Real.sqrt (lowerNormSq n x.1)))
  exact h_cont

/-- The continuous map `band → S^n`. -/
noncomputable def deletedNorthBandToSphere (n : Nat) :
    C(sphereDeletedNorthSet n, Sphere n) :=
  ⟨fun x => ⟨deletedNorthBandToSphereFun n x, deletedNorthBandToSphereFun_mem n x⟩,
    continuous_deletedNorthBandToSphere n⟩

@[simp]
theorem deletedNorthBandToSphere_coe (n : Nat) (x : sphereDeletedNorthSet n) :
    (deletedNorthBandToSphere n x : EuclideanSpace Real (Fin (n + 1)))
      = deletedNorthBandToSphereFun n x := rfl

/-! ## The `S^n → band` map -/

/-- Append a zero last coordinate. -/
noncomputable def sphereToDeletedNorthBandFun
    (n : Nat) (y : Sphere n) : EuclideanSpace Real (Fin (n + 2)) :=
  (WithLp.equiv 2 (Fin (n + 2) → Real)).symm
    (Fin.snoc (fun i : Fin (n + 1) =>
      (y : EuclideanSpace Real (Fin (n + 1))) i) 0)

theorem sphereToDeletedNorthBandFun_mem_sphere (n : Nat) (y : Sphere n) :
    sphereToDeletedNorthBandFun n y ∈
      Metric.sphere (0 : EuclideanSpace Real (Fin (n + 2))) 1 := by
  unfold sphereToDeletedNorthBandFun;
  simp +decide [ EuclideanSpace.norm_eq, Fin.sum_univ_castSucc ];
  convert congr_arg ( fun x : ℝ => x ^ 2 ) y.2 using 1;
  · rw [ dist_zero_right, EuclideanSpace.norm_eq ];
    rw [ Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ] ; rw [ Fin.sum_univ_castSucc ] ; norm_num;
  · norm_num

theorem sphereToDeletedNorthBandFun_last (n : Nat) (y : Sphere n) :
    sphereLastCoord n ⟨sphereToDeletedNorthBandFun n y,
      sphereToDeletedNorthBandFun_mem_sphere n y⟩ = 0 := by
  unfold sphereLastCoord sphereToDeletedNorthBandFun; simp +decide [ Fin.snoc ] ;

theorem sphereToDeletedNorthBandFun_mem_band (n : Nat) (y : Sphere n) :
    (⟨sphereToDeletedNorthBandFun n y, sphereToDeletedNorthBandFun_mem_sphere n y⟩ :
      Sphere (n + 1)) ∈ sphereDeletedNorthSet n :=
  mem_sphereDeletedNorth_of_last_zero n _ (sphereToDeletedNorthBandFun_last n y)

theorem continuous_sphereToDeletedNorthBand (n : Nat) :
    Continuous (fun y : Sphere n =>
      (⟨⟨sphereToDeletedNorthBandFun n y, sphereToDeletedNorthBandFun_mem_sphere n y⟩,
        sphereToDeletedNorthBandFun_mem_band n y⟩ : sphereDeletedNorthSet n)) := by
  refine' Continuous.subtype_mk _ _
  generalize_proofs at *;
  refine' Continuous.subtype_mk _ _ ; unfold sphereToDeletedNorthBandFun ; norm_num [ Fin.snoc ] ;
  refine' Continuous.comp ( continuous_induced_rng.mpr _ ) _;
  · fun_prop (disch := solve_by_elim);
  · refine' continuous_pi_iff.mpr _;
    intro i; induction i using Fin.lastCases <;> simp +decide [ * ] ;
    · exact continuous_const;
    · fun_prop

/-- The continuous map `S^n → band`. -/
noncomputable def sphereToDeletedNorthBand (n : Nat) :
    C(Sphere n, sphereDeletedNorthSet n) :=
  ⟨fun y => ⟨⟨sphereToDeletedNorthBandFun n y, sphereToDeletedNorthBandFun_mem_sphere n y⟩,
    sphereToDeletedNorthBandFun_mem_band n y⟩, continuous_sphereToDeletedNorthBand n⟩

@[simp]
theorem sphereToDeletedNorthBand_coe (n : Nat) (y : Sphere n) :
    ((sphereToDeletedNorthBand n y).1 : EuclideanSpace Real (Fin (n + 2)))
      = sphereToDeletedNorthBandFun n y := rfl

/-! ## Oddness (antipodal equivariance) -/

theorem deletedNorthBandToSphere_neg (n : Nat) (x : sphereDeletedNorthSet n) :
    deletedNorthBandToSphere n ⟨-x.1, by
        simpa using (sphereDeletedNorthSet_neg_iff n x.1).2 x.2⟩
      = - deletedNorthBandToSphere n x := by
  ext i; simp +decide [ deletedNorthBandToSphere ];
  unfold deletedNorthBandToSphereFun; norm_num;
  unfold lowerNormSq; norm_num [ Finset.sum_neg_distrib, neg_div ] ;

theorem sphereToDeletedNorthBand_neg (n : Nat) (y : Sphere n) :
    sphereToDeletedNorthBand n (-y) =
      ⟨- (sphereToDeletedNorthBand n y).1, by
        simpa using (sphereDeletedNorthSet_neg_iff n (sphereToDeletedNorthBand n y).1).2
          (sphereToDeletedNorthBand n y).2⟩ := by
  ext i; exact (by
  induction i using Fin.lastCases <;> simp_all +decide;
  · unfold sphereToDeletedNorthBandFun; simp +decide [ Fin.snoc ] ;
  · unfold sphereToDeletedNorthBandFun; aesop;)

/-! ## The first composition is the identity -/

theorem deletedNorthBandToSphere_comp_sphereToDeletedNorthBand (n : Nat) :
    (deletedNorthBandToSphere n).comp (sphereToDeletedNorthBand n)
      = ContinuousMap.id (Sphere n) := by
  ext y i
  simp +decide [deletedNorthBandToSphere, sphereToDeletedNorthBand, deletedNorthBandToSphereFun,
    sphereToDeletedNorthBandFun]
  rw [lowerNormSq_eq_one_sub_last_sq]
  unfold sphereLastCoord
  simp +decide [Fin.snoc_last]

/-! ## The homotopy `sphereToDeletedNorthBand ∘ deletedNorthBandToSphere ≃ id` -/

/-- The (unnormalized) straight-line homotopy on the band. -/
noncomputable def deletedNorthBandHomotopyFun
    (n : Nat) (p : unitInterval × sphereDeletedNorthSet n) :
    EuclideanSpace Real (Fin (n + 2)) :=
  (1 - (p.1 : Real)) •
      ((sphereToDeletedNorthBand n (deletedNorthBandToSphere n p.2)).val.val)
    + (p.1 : Real) • p.2.val.val

theorem deletedNorthBandHomotopyFun_ne_zero
    (n : Nat) (p : unitInterval × sphereDeletedNorthSet n) :
    deletedNorthBandHomotopyFun n p ≠ 0 := by
  -- Let's choose any coordinate `i` such that `p.2.1.val i.castSucc ≠ 0`.
  obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), p.2.1.val i.castSucc ≠ 0 := by
    have := lowerNormSq_pos_of_deletedNorth n p.2.1 p.2.2; contrapose! this; simp_all +decide [ lowerNormSq ] ;
  intro h; have := congr_arg ( fun x => x i.castSucc ) h; norm_num [ deletedNorthBandHomotopyFun ] at this; simp_all +decide ;
  simp_all +decide [ sphereToDeletedNorthBandFun, deletedNorthBandToSphereFun ];
  -- Since $p.1 \in [0, 1]$, we have $1 - p.1 \geq 0$ and $p.1 \geq 0$. Therefore, the term $(1 - p.1) / \sqrt{lowerNormSq n p.2} + p.1$ is positive.
  have h_pos : 0 < (1 - p.1.val) / Real.sqrt (lowerNormSq n p.2) + p.1.val := by
    by_cases h : p.1.val = 0 <;> simp_all +decide [ div_eq_mul_inv ];
    · exact absurd this ( ne_of_gt ( Real.sqrt_pos.mpr ( lowerNormSq_pos_of_deletedNorth n p.2.1 p.2.2 ) ) );
    · exact add_pos_of_nonneg_of_pos ( mul_nonneg ( sub_nonneg.2 <| p.1.2.2 ) <| inv_nonneg.2 <| Real.sqrt_nonneg _ ) <| lt_of_le_of_ne ( p.1.2.1 ) <| Ne.symm <| by aesop;
  exact hi ( by ring_nf at *; nlinarith )

theorem deletedNorthBandHomotopy_mem_sphere
    (n : Nat) (p : unitInterval × sphereDeletedNorthSet n) :
    (‖deletedNorthBandHomotopyFun n p‖⁻¹ • deletedNorthBandHomotopyFun n p) ∈
      Metric.sphere (0 : EuclideanSpace Real (Fin (n + 2))) 1 := by
  simp +decide [norm_smul, deletedNorthBandHomotopyFun_ne_zero]

theorem deletedNorthBandHomotopy_mem_band
    (n : Nat) (p : unitInterval × sphereDeletedNorthSet n) :
    (⟨‖deletedNorthBandHomotopyFun n p‖⁻¹ • deletedNorthBandHomotopyFun n p,
        deletedNorthBandHomotopy_mem_sphere n p⟩ : Sphere (n + 1))
      ∈ sphereDeletedNorthSet n := by
  obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), p.2.1.val i.castSucc ≠ 0 := by
    have := lowerNormSq_pos_of_deletedNorth n p.2.1 p.2.2; contrapose! this; simp_all +decide [ lowerNormSq ] ;
  have h_coord : ((‖deletedNorthBandHomotopyFun n p‖⁻¹ • deletedNorthBandHomotopyFun n p) (i.castSucc)) ≠ 0 := by
    simp_all +decide [ deletedNorthBandHomotopyFun ];
    by_cases h : ( 1 - p.1 : ℝ ) = 0 <;> simp_all +decide [ sphereToDeletedNorthBandFun ];
    · exact ⟨ ⟨ by rintro h'; norm_num [ h' ] at h, by rintro h'; exact hi <| by simp [ h' ] ⟩, by rintro h'; norm_num [ h' ] at h ⟩;
    · simp_all +decide [ deletedNorthBandToSphereFun ];
      field_simp;
      simp_all +decide [ mul_div_assoc ];
      constructor;
      · rw [ div_add', div_eq_iff ] <;> norm_num;
        · exact ne_of_gt ( add_pos_of_pos_of_nonneg ( lt_of_le_of_ne ( sub_nonneg.mpr p.1.2.2 ) ( Ne.symm h ) ) ( mul_nonneg p.1.2.1 ( Real.sqrt_nonneg _ ) ) );
        · exact ne_of_gt <| Real.sqrt_pos.mpr <| lowerNormSq_pos_of_deletedNorth n _ p.2.2;
        · exact ne_of_gt <| Real.sqrt_pos.mpr <| lowerNormSq_pos_of_deletedNorth n _ p.2.2;
      · intro H; have := congr_arg ( fun x => x i.castSucc ) H; norm_num [ hi, h ] at this;
        -- Simplify the equation obtained from the homotopy.
        have h_simplified : (1 - p.1.val) * (1 / Real.sqrt (lowerNormSq n p.2.val)) + p.1.val = 0 := by
          exact mul_left_cancel₀ hi <| by linear_combination' this;
        exact h ( by nlinarith [ show 0 < 1 / Real.sqrt ( lowerNormSq n p.2.val ) from one_div_pos.mpr ( Real.sqrt_pos.mpr ( lowerNormSq_pos_of_deletedNorth n p.2.val p.2.property ) ), show ( p.1 : ℝ ) ≥ 0 from p.1.2.1, show ( p.1 : ℝ ) ≤ 1 from p.1.2.2 ] );
  exact mem_sphereDeletedNorth_of_castSucc_ne_zero n _ i h_coord

theorem continuous_deletedNorthBandHomotopy (n : Nat) :
    Continuous (fun p : unitInterval × sphereDeletedNorthSet n =>
      (⟨⟨‖deletedNorthBandHomotopyFun n p‖⁻¹ • deletedNorthBandHomotopyFun n p,
        deletedNorthBandHomotopy_mem_sphere n p⟩,
        deletedNorthBandHomotopy_mem_band n p⟩ : sphereDeletedNorthSet n)) := by
  have hfun : Continuous (deletedNorthBandHomotopyFun n) := by
    unfold deletedNorthBandHomotopyFun
    have hleft : Continuous (fun p : unitInterval × sphereDeletedNorthSet n =>
        ((sphereToDeletedNorthBand n) ((deletedNorthBandToSphere n) p.2)).1.1) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp
        ((sphereToDeletedNorthBand n).continuous.comp
          ((deletedNorthBandToSphere n).continuous.comp continuous_snd)))
    have hright : Continuous (fun p : unitInterval × sphereDeletedNorthSet n => p.2.1.1) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
    exact (by fun_prop : Continuous (fun p : unitInterval × sphereDeletedNorthSet n =>
      (1 - (p.1 : ℝ)))).smul hleft |>.add
        ((by fun_prop : Continuous (fun p : unitInterval × sphereDeletedNorthSet n =>
          (p.1 : ℝ))).smul hright)
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact (hfun.norm.inv₀ fun p => norm_ne_zero_iff.mpr
    (deletedNorthBandHomotopyFun_ne_zero n p)).smul hfun

theorem deletedNorthBandHomotopy_zero (n : Nat) (x : sphereDeletedNorthSet n) :
    (⟨⟨‖deletedNorthBandHomotopyFun n (0, x)‖⁻¹ • deletedNorthBandHomotopyFun n (0, x),
        deletedNorthBandHomotopy_mem_sphere n (0, x)⟩,
        deletedNorthBandHomotopy_mem_band n (0, x)⟩ : sphereDeletedNorthSet n)
      = (sphereToDeletedNorthBand n).comp (deletedNorthBandToSphere n) x := by
  unfold deletedNorthBandHomotopyFun;
  have h_norm : ‖(sphereToDeletedNorthBand n (deletedNorthBandToSphere n x)).val.val‖ = 1 := by
    exact mem_sphere_zero_iff_norm.mp ( sphereToDeletedNorthBand n ( deletedNorthBandToSphere n x ) |>.1 |>.2 );
  aesop

theorem deletedNorthBandHomotopy_one (n : Nat) (x : sphereDeletedNorthSet n) :
    (⟨⟨‖deletedNorthBandHomotopyFun n (1, x)‖⁻¹ • deletedNorthBandHomotopyFun n (1, x),
        deletedNorthBandHomotopy_mem_sphere n (1, x)⟩,
        deletedNorthBandHomotopy_mem_band n (1, x)⟩ : sphereDeletedNorthSet n)
      = ContinuousMap.id _ x := by
  unfold deletedNorthBandHomotopyFun ;
  simp +decide

/-- The homotopy `sphereToDeletedNorthBand ∘ deletedNorthBandToSphere ≃ id`. -/
noncomputable def deletedNorthBandHomotopy (n : Nat) :
    ContinuousMap.Homotopy
      ((sphereToDeletedNorthBand n).comp (deletedNorthBandToSphere n))
      (ContinuousMap.id _) where
  toFun p := ⟨⟨‖deletedNorthBandHomotopyFun n p‖⁻¹ • deletedNorthBandHomotopyFun n p,
    deletedNorthBandHomotopy_mem_sphere n p⟩, deletedNorthBandHomotopy_mem_band n p⟩
  continuous_toFun := continuous_deletedNorthBandHomotopy n
  map_zero_left := deletedNorthBandHomotopy_zero n
  map_one_left := deletedNorthBandHomotopy_one n

/-- The band `S^(n+1) \ {±e_last}` is homotopy equivalent to `S^n`. -/
noncomputable def deletedNorthBand_homotopyEquiv_sphere (n : Nat) :
    ContinuousMap.HomotopyEquiv (sphereDeletedNorthSet n) (Sphere n) where
  toFun := deletedNorthBandToSphere n
  invFun := sphereToDeletedNorthBand n
  left_inv := ⟨deletedNorthBandHomotopy n⟩
  right_inv :=
    deletedNorthBandToSphere_comp_sphereToDeletedNorthBand n ▸ ContinuousMap.Homotopic.refl _

/-
The homotopy is antipodal-equivariant.
-/
theorem deletedNorthBandHomotopy_neg
    (n : Nat) (t : unitInterval) (x : sphereDeletedNorthSet n) :
    deletedNorthBandHomotopy n (t, ⟨-x.1, by
        simpa using (sphereDeletedNorthSet_neg_iff n x.1).2 x.2⟩)
      = ⟨- (deletedNorthBandHomotopy n (t, x)).1, by
        simpa using (sphereDeletedNorthSet_neg_iff n (deletedNorthBandHomotopy n (t, x)).1).2
          (deletedNorthBandHomotopy n (t, x)).2⟩ := by
  generalize_proofs at *;
  -- By definition of `deletedNorthBandHomotopy`, we know that
  have h_homotopy : (deletedNorthBandHomotopyFun n (t, ⟨-x.1, by
    assumption⟩)) = - (deletedNorthBandHomotopyFun n (t, x)) := by
    unfold deletedNorthBandHomotopyFun;
    simp +decide [ deletedNorthBandToSphere_neg, sphereToDeletedNorthBand_neg ];
    abel1
  apply Subtype.ext
  apply Subtype.ext
  change ‖deletedNorthBandHomotopyFun n (t, ⟨-x.1, _⟩)‖⁻¹ •
      deletedNorthBandHomotopyFun n (t, ⟨-x.1, _⟩) =
    -(‖deletedNorthBandHomotopyFun n (t, x)‖⁻¹ • deletedNorthBandHomotopyFun n (t, x))
  rw [h_homotopy, norm_neg]
  simp


end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
