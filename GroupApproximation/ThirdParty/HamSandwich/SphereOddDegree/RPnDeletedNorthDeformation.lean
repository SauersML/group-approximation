import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnAffineCover
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.SphereModTwoHomologyAboveDimension
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
  cases' eq_or_eq_neg_of_proj_eq ( n := n + 1 ) ( show proj ( n + 1 ) z = proj ( n + 1 ) ⟨ elast n, by rw [ mem_sphere_zero_iff_norm ] ; exact elast_norm n ⟩ from Classical.not_not.1 hz ) with h h <;> simp_all +decide [ elast ]

theorem lowerNormSq_pos_of_deletedNorth
    (n : Nat) (x : Sphere (n + 1))
    (hx : x ∈ sphereDeletedNorthSet n) :
    0 < lowerNormSq n x := by
  contrapose! hx;
  -- Since `lowerNormSq n x ≤ 0`, we have `x.val i.castSucc = 0` for all `i : Fin (n + 1)`.
  have h_castSucc_zero : ∀ i : Fin (n + 1), (x : EuclideanSpace ℝ (Fin (n + 2))) i.castSucc = 0 := by
    exact fun i => sq_eq_zero_iff.mp ( le_antisymm ( le_trans ( Finset.single_le_sum ( fun a _ => sq_nonneg ( x.val ( Fin.castSucc a ) ) ) ( Finset.mem_univ i ) ) hx ) ( sq_nonneg _ ) );
  -- Since `x.val i.castSucc = 0` for all `i : Fin (n + 1)`, we have `x = ± elast n`.
  have h_x_eq_elast : x = elast n ∨ x = -elast n := by
    have h_x_eq_elast : (x : EuclideanSpace ℝ (Fin (n + 2))) = (sphereLastCoord n x) • elast n := by
      ext i; by_cases hi : i.val < n + 1 <;> simp_all +decide [ Fin.ext_iff, elast ] ;
      · rw [ if_neg ( by linarith ) ] ; exact h_castSucc_zero ⟨ i, by linarith ⟩;
      · simp_all +decide [ Fin.eq_last_of_not_lt ];
        rfl;
    have h_x_eq_elast : (sphereLastCoord n x)^2 = 1 := by
      have := congr_arg ( fun y => ‖y‖ ^ 2 ) h_x_eq_elast ; norm_num at this;
      rw [ norm_smul, Real.norm_eq_abs, elast_norm ] at this ; norm_num at this ; linarith;
    cases eq_or_eq_neg_of_sq_eq_sq ( sphereLastCoord n x ) 1 ( by linarith ) <;> aesop ( simp_config := { singlePass := true } ) ;
  cases h_x_eq_elast <;> simp_all +decide [ sphereDeletedNorthSet ];
  · convert Quotient.sound' _;
    exact Or.inl ( Subtype.ext <| by aesop );
  · convert Quotient.sound' _;
    exact Or.inr ( by aesop )

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
      refine' continuous_finset_sum _ fun i _ => Continuous.pow _ _;
      fun_prop
    have h_cont_div : Continuous (fun x : sphereDeletedNorthSet n => fun i : Fin (n + 1) => (x.1.1 i.castSucc) / Real.sqrt (lowerNormSq n x.1)) := by
      refine' continuous_pi fun i => Continuous.div _ _ _;
      · fun_prop;
      · exact Real.continuous_sqrt.comp h_cont_lowerNormSq;
      · exact fun x => ne_of_gt <| Real.sqrt_pos.mpr <| lowerNormSq_pos_of_deletedNorth n x.1 x.2
    generalize_proofs at *;
    exact continuous_induced_rng.mpr h_cont_div
  generalize_proofs at *;
  convert h_cont using 1

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
  refine' Continuous.subtype_mk ( Continuous.subtype_mk _ _ ) _;
  apply_rules [ Continuous.smul, Continuous.inv₀, continuous_const ];
  · apply_rules [ Continuous.norm, Continuous.add, Continuous.smul, continuous_const, continuous_fst, continuous_snd ];
    · fun_prop;
    · exact Continuous.comp ( continuous_subtype_val ) ( Continuous.comp ( continuous_subtype_val ) ( sphereToDeletedNorthBand n |> ContinuousMap.continuous ) |> Continuous.comp <| deletedNorthBandToSphere n |> ContinuousMap.continuous |> Continuous.comp <| continuous_snd );
    · fun_prop;
    · fun_prop;
  · exact fun x => norm_ne_zero_iff.mpr ( deletedNorthBandHomotopyFun_ne_zero n x );
  · apply_rules [ Continuous.add, Continuous.smul, continuous_const, continuous_subtype_val.comp continuous_fst, continuous_subtype_val.comp continuous_snd ];
    · fun_prop;
    · exact Continuous.comp ( continuous_subtype_val ) ( Continuous.comp ( continuous_subtype_val ) ( sphereToDeletedNorthBand n |> ContinuousMap.continuous ) |> Continuous.comp <| deletedNorthBandToSphere n |> ContinuousMap.continuous |> Continuous.comp <| continuous_snd );
    · fun_prop

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
  generalize_proofs at *;
  simp_all +decide [ Subtype.ext_iff ];
  convert congr_arg ( fun v : EuclideanSpace ℝ ( Fin ( n + 2 ) ) => ‖v‖⁻¹ • v ) h_homotopy using 1;
  simp +decide [ norm_neg, deletedNorthBandHomotopy ];
  rfl

/-! ## The restricted quotient map upstairs -/

/-- The restricted quotient map `band → rpDeletedNorthSpace n`. -/
noncomputable def deletedNorthProj (n : Nat) :
    C(sphereDeletedNorthSet n, rpDeletedNorthSpace n) where
  toFun x := ⟨proj (n + 1) x.1, by
    show proj (n + 1) x.1 ∈ rpDeletedNorthSet n
    rw [← Set.mem_preimage, preimage_rpDeletedNorthSet]; exact x.2⟩
  continuous_toFun := (proj_restrict_deletedNorth_isQuotientMap n).continuous

theorem deletedNorthProj_isQuotientMap (n : Nat) :
    Topology.IsQuotientMap (deletedNorthProj n) :=
  proj_restrict_deletedNorth_isQuotientMap n

@[simp]
theorem deletedNorthProj_coe (n : Nat) (x : sphereDeletedNorthSet n) :
    ((deletedNorthProj n x : rpDeletedNorthSpace n) : RP (n + 1)) = proj (n + 1) x.1 := rfl

/-! ## The map `rpDeletedNorthSpace n → RP n` -/

/-- The map `band → RP n`, `x ↦ proj n (deletedNorthBandToSphere n x)`. -/
noncomputable def rpDeletedNorthToLowerAux (n : Nat) :
    C(sphereDeletedNorthSet n, RP n) :=
  (proj n).comp (deletedNorthBandToSphere n)

theorem rpDeletedNorthToLower_factors (n : Nat) :
    Function.FactorsThrough (rpDeletedNorthToLowerAux n) (deletedNorthProj n) := by
  intro a b hab;
  unfold rpDeletedNorthToLowerAux deletedNorthProj at *;
  grind +suggestions

/-- The descended map `rpDeletedNorthSpace n → RP n`. -/
noncomputable def rpDeletedNorthToLower (n : Nat) : C(rpDeletedNorthSpace n, RP n) :=
  (deletedNorthProj_isQuotientMap n).lift (rpDeletedNorthToLowerAux n)
    (rpDeletedNorthToLower_factors n)

@[simp]
theorem rpDeletedNorthToLower_proj
    (n : Nat) (x : sphereDeletedNorthSet n) :
    rpDeletedNorthToLower n
      ⟨proj (n + 1) x.1, by
        show proj (n + 1) x.1 ∈ rpDeletedNorthSet n
        rw [← Set.mem_preimage, preimage_rpDeletedNorthSet]; exact x.2⟩
      = proj n (deletedNorthBandToSphere n x) := by
  -- By definition of the quotient map, we have that the composition of the quotient map and the projection is equal to the projection.
  apply DFunLike.congr_fun (Topology.IsQuotientMap.lift_comp (deletedNorthProj_isQuotientMap n) (rpDeletedNorthToLowerAux n) (rpDeletedNorthToLower_factors n)) x

/-! ## The map `RP n → rpDeletedNorthSpace n` -/

theorem lowerToRpDeletedNorth_wd (n : Nat) (a b : Sphere n) (hab : a ≈ b) :
    (⟨proj (n + 1) (sphereToDeletedNorthBand n a).1, by
        show proj (n + 1) (sphereToDeletedNorthBand n a).1 ∈ rpDeletedNorthSet n
        rw [← Set.mem_preimage, preimage_rpDeletedNorthSet]
        exact (sphereToDeletedNorthBand n a).2⟩ : rpDeletedNorthSpace n)
      = ⟨proj (n + 1) (sphereToDeletedNorthBand n b).1, by
        show proj (n + 1) (sphereToDeletedNorthBand n b).1 ∈ rpDeletedNorthSet n
        rw [← Set.mem_preimage, preimage_rpDeletedNorthSet]
        exact (sphereToDeletedNorthBand n b).2⟩ := by
  cases' hab with h h;
  · aesop;
  · simp +decide [ h, sphereToDeletedNorthBand_neg ];
    exact Or.inr rfl

theorem continuous_lowerToRpDeletedNorth (n : Nat) :
    Continuous (fun y : Sphere n =>
      (⟨proj (n + 1) (sphereToDeletedNorthBand n y).1, by
        show proj (n + 1) (sphereToDeletedNorthBand n y).1 ∈ rpDeletedNorthSet n
        rw [← Set.mem_preimage, preimage_rpDeletedNorthSet]
        exact (sphereToDeletedNorthBand n y).2⟩ : rpDeletedNorthSpace n)) := by
  -- The composition of continuous functions is continuous.
  apply Continuous.subtype_mk;
  exact Continuous.comp (proj (n + 1)).continuous
    (continuous_subtype_val.comp (continuous_sphereToDeletedNorthBand n))

/-- The descended map `RP n → rpDeletedNorthSpace n`. -/
noncomputable def lowerToRpDeletedNorth (n : Nat) : C(RP n, rpDeletedNorthSpace n) where
  toFun := Quotient.lift
    (fun y : Sphere n => (⟨proj (n + 1) (sphereToDeletedNorthBand n y).1, by
        show proj (n + 1) (sphereToDeletedNorthBand n y).1 ∈ rpDeletedNorthSet n
        rw [← Set.mem_preimage, preimage_rpDeletedNorthSet]
        exact (sphereToDeletedNorthBand n y).2⟩ : rpDeletedNorthSpace n))
    (lowerToRpDeletedNorth_wd n)
  continuous_toFun := by
    apply Continuous.quotient_lift
    exact continuous_lowerToRpDeletedNorth n

@[simp]
theorem lowerToRpDeletedNorth_proj (n : Nat) (y : Sphere n) :
    lowerToRpDeletedNorth n (proj n y)
      = ⟨proj (n + 1) (sphereToDeletedNorthBand n y).1, by
          show proj (n + 1) (sphereToDeletedNorthBand n y).1 ∈ rpDeletedNorthSet n
          rw [← Set.mem_preimage, preimage_rpDeletedNorthSet]
          exact (sphereToDeletedNorthBand n y).2⟩ :=
  rfl

/-! ## The right inverse is an equality -/

theorem rpDeletedNorth_right_inv_homotopic (n : Nat) :
    ContinuousMap.Homotopic
      ((rpDeletedNorthToLower n).comp (lowerToRpDeletedNorth n))
      (ContinuousMap.id (RP n)) := by
  convert RP.hom_ext ?_;
  convert Iff.rfl;
  -- The composition of the two maps is the identity map on RP n.
  apply Iff.intro;
  convert fun h => ?_;
  convert ContinuousMap.Homotopic.refl _;
  · intro h_homotopy
    apply RP.hom_ext
    intro y
    simp;
    convert DFunLike.congr_fun ( deletedNorthBandToSphere_comp_sphereToDeletedNorthBand n ) y using 1;
    constructor <;> intro h <;> simp_all +decide [ RP ];
    · convert DFunLike.congr_fun ( deletedNorthBandToSphere_comp_sphereToDeletedNorthBand n ) y using 1;
    · convert congr_arg ( fun x : Sphere n => Quotient.mk' x ) h.symm using 1;
      convert rpDeletedNorthToLower_proj n ( sphereToDeletedNorthBand n y ) using 1;
  · intro x; rw [ ContinuousMap.comp_apply, lowerToRpDeletedNorth_proj, rpDeletedNorthToLower_proj ] ;
    have := DFunLike.congr_fun ( deletedNorthBandToSphere_comp_sphereToDeletedNorthBand n ) x; aesop;

/-! ## The descended homotopy for the left inverse -/

/-
The key fiberwise compatibility: the upstairs homotopy descends.
-/
theorem deletedNorthProj_homotopy_compat
    (n : Nat) (t : unitInterval) {x x' : sphereDeletedNorthSet n}
    (h : deletedNorthProj n x = deletedNorthProj n x') :
    deletedNorthProj n (deletedNorthBandHomotopy n (t, x))
      = deletedNorthProj n (deletedNorthBandHomotopy n (t, x')) := by
  -- By `eq_or_eq_neg_of_proj_eq`, `x.1 = x'.1 ∨ x.1 = -x'.1`.
  have h_cases : x.1 = x'.1 ∨ x.1 = -x'.1 := by
    apply eq_or_eq_neg_of_proj_eq;
    convert congr_arg Subtype.val h using 1
  cases' h_cases with h_eq h_neg
  all_goals generalize_proofs at *;
  · cases x ; cases x' ; aesop;
  · -- By `deletedNorthBandHomotopy_neg n t x'`, `deletedNorthBandHomotopy n (t, ⟨-x'.1,_⟩) = ⟨-(deletedNorthBandHomotopy n (t, x')).1, _⟩`.
    have h_homotopy_neg : deletedNorthBandHomotopy n (t, x) = ⟨-(deletedNorthBandHomotopy n (t, x')).1, by
      exact (sphereDeletedNorthSet_neg_iff n _).2 (deletedNorthBandHomotopy_mem_band n (t, x'))⟩ := by
      grind +suggestions
    generalize_proofs at *;
    simp_all +decide [ deletedNorthProj ];
    exact Or.inr rfl

/-- The descended homotopy value function. -/
noncomputable def deletedNorthRPHomotopyFun
    (n : Nat) (p : unitInterval × rpDeletedNorthSpace n) : rpDeletedNorthSpace n :=
  deletedNorthProj n
    (deletedNorthBandHomotopy n
      (p.1, Function.surjInv (deletedNorthProj_isQuotientMap n).surjective p.2))

theorem deletedNorthRPHomotopyFun_proj
    (n : Nat) (t : unitInterval) (x : sphereDeletedNorthSet n) :
    deletedNorthRPHomotopyFun n (t, deletedNorthProj n x)
      = deletedNorthProj n (deletedNorthBandHomotopy n (t, x)) := by
  convert deletedNorthProj_homotopy_compat n t _ using 1;
  exact Function.surjInv_eq ( deletedNorthProj_isQuotientMap n |>.surjective ) _

theorem continuous_deletedNorthRPHomotopyFun (n : Nat) :
    Continuous (deletedNorthRPHomotopyFun n) := by
  apply (deletedNorthProj_isQuotientMap n).continuous_lift_prod_right
  have hfun : (fun p : unitInterval × sphereDeletedNorthSet n =>
      deletedNorthRPHomotopyFun n (p.1, deletedNorthProj n p.2))
      = fun p => deletedNorthProj n (deletedNorthBandHomotopy n p) := by
    funext p
    exact deletedNorthRPHomotopyFun_proj n p.1 p.2
  rw [hfun]
  exact (deletedNorthProj n).continuous.comp (deletedNorthBandHomotopy n).continuous

theorem deletedNorthRPHomotopy_zero (n : Nat) (q : rpDeletedNorthSpace n) :
    deletedNorthRPHomotopyFun n (0, q)
      = (lowerToRpDeletedNorth n).comp (rpDeletedNorthToLower n) q := by
  -- Use surjectivity of `deletedNorthProj n` to obtain `x : sphereDeletedNorthSet n` so that `deletedNorthProj n x = q`, then substitute `q` with `deletedNorthProj n x` in the goal.
  -- After this substitution, the WSLEY (WLOG) step ‘alpha hat dialing hat burlap’ should match our key lemma `deletedNorthRPHomotopyFun zero`.
  obtain ⟨x, hx⟩ := (deletedNorthProj_isQuotientMap n).surjective q;
  rw [ ← hx, deletedNorthRPHomotopyFun_proj ];
  grind +suggestions

theorem deletedNorthRPHomotopy_one (n : Nat) (q : rpDeletedNorthSpace n) :
    deletedNorthRPHomotopyFun n (1, q) = ContinuousMap.id _ q := by
  obtain ⟨x, hx⟩ := ( deletedNorthProj_isQuotientMap n ).surjective q;
  rw [ ← hx, deletedNorthRPHomotopyFun_proj ];
  exact congr_arg _ ( deletedNorthBandHomotopy_one n x )

/-- The descended homotopy `(lowerToRpDeletedNorth ∘ rpDeletedNorthToLower) ≃ id`. -/
noncomputable def deletedNorthRPHomotopy (n : Nat) :
    ContinuousMap.Homotopy
      ((lowerToRpDeletedNorth n).comp (rpDeletedNorthToLower n))
      (ContinuousMap.id (rpDeletedNorthSpace n)) where
  toFun := deletedNorthRPHomotopyFun n
  continuous_toFun := continuous_deletedNorthRPHomotopyFun n
  map_zero_left := deletedNorthRPHomotopy_zero n
  map_one_left := deletedNorthRPHomotopy_one n

theorem rpDeletedNorth_left_inv_homotopic (n : Nat) :
    ContinuousMap.Homotopic
      ((lowerToRpDeletedNorth n).comp (rpDeletedNorthToLower n))
      (ContinuousMap.id (rpDeletedNorthSpace n)) :=
  ⟨deletedNorthRPHomotopy n⟩

/-! ## The final homotopy equivalence -/

/-- The deleted-north chart deformation retracts onto `RP n`. -/
noncomputable def rpDeletedNorth_homotopyEquiv_lower (n : Nat) :
    ContinuousMap.HomotopyEquiv (rpDeletedNorthSpace n) (RP n) where
  toFun := rpDeletedNorthToLower n
  invFun := lowerToRpDeletedNorth n
  left_inv := rpDeletedNorth_left_inv_homotopic n
  right_inv := rpDeletedNorth_right_inv_homotopic n

/-! ## Homology corollaries -/

/-- The mod-2 homology of the deleted-north chart agrees with that of `RP n`. -/
noncomputable def rpDeletedNorth_homologyIso_lower (n k : Nat) :
    homologyZMod2 (TopCat.of (rpDeletedNorthSpace n)) k
      ≅ homologyZMod2 (TopCat.of (RP n)) k :=
  homologyIsoOfHomotopyEquivModule
    (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)) k
    (rpDeletedNorth_homotopyEquiv_lower n)

/-- Subchain-homology form of the previous isomorphism. -/
noncomputable def rpDeletedNorth_subspaceHomologyIso_lower (n k : Nat) :
    (subChainComplex (ZMod 2) (rpAmbientSpace n)
      (rpDeletedNorthOpen n : Set (rpAmbientSpace n))).homology k
      ≅ homologyZMod2 (TopCat.of (RP n)) k :=
  subspaceHomologyIso _ k ≪≫ rpDeletedNorth_homologyIso_lower n k

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
