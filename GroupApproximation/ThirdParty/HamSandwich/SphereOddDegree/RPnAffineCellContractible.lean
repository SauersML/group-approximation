import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnDeletedNorthProjectiveHomotopy
import Mathlib

/-!
# The affine chart `V = RP^(n+1) \ RP^n ≃ R^(n+1)` and its contractibility

We construct the affine chart identifying the affine cell `rpAffineCellSpace n`
(the locus where the squared last coordinate is nonzero) with Euclidean space
`R^(n+1)`, and deduce that the affine cell is contractible.

The chart is built upstairs on the antipodal-saturated set
`sphereAffineCellSet n = { x ∈ S^(n+1) | last coordinate ≠ 0 }` by

```text
[v, t] ↦ v / t
```

which is invariant under the antipodal replacement `(v,t) ↦ (-v,-t)`, so it
descends to the projective quotient.  The inverse sends `a ∈ R^(n+1)` to the
projective class of `(a, 1) / sqrt(1 + ‖a‖²)`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Metric Topology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

variable (n : Nat)

/-! ## The restricted quotient map upstairs -/

/-- The restricted quotient map `sphereAffineCellSet → rpAffineCellSpace n`. -/
noncomputable def affineCellProj (n : Nat) :
    C(sphereAffineCellSet n, rpAffineCellSpace n) where
  toFun x := ⟨proj (n + 1) x.1, by
    show proj (n + 1) x.1 ∈ rpAffineCellSet n
    rw [← Set.mem_preimage, preimage_rpAffineCellSet]; exact x.2⟩
  continuous_toFun := (proj_restrict_affineCell_isQuotientMap n).continuous

theorem affineCellProj_isQuotientMap (n : Nat) :
    Topology.IsQuotientMap (affineCellProj n) :=
  proj_restrict_affineCell_isQuotientMap n

@[simp]
theorem affineCellProj_coe (n : Nat) (x : sphereAffineCellSet n) :
    ((affineCellProj n x : rpAffineCellSpace n) : RP (n + 1)) = proj (n + 1) x.1 := rfl

/-! ## The forward chart upstairs -/

/-- The forward chart upstairs: `[v,t] ↦ v / t` (dividing each of the first
`n+1` coordinates by the last one). -/
noncomputable def affineForwardFun
    (n : Nat) (x : sphereAffineCellSet n) : EuclideanSpace Real (Fin (n + 1)) :=
  (WithLp.equiv 2 (Fin (n + 1) → Real)).symm
    (fun i =>
      ((x.1 : EuclideanSpace Real (Fin (n + 2))) i.castSucc) /
        sphereLastCoord n x.1)

theorem affineForwardFun_neg (n : Nat) (x : sphereAffineCellSet n) :
    affineForwardFun n
      ⟨-x.1, by simpa using (sphereAffineCellSet_neg_iff n x.1).2 x.2⟩
      = affineForwardFun n x := by
  simp [affineForwardFun, sphereLastCoord_neg]

theorem continuous_affineForwardFun (n : Nat) :
    Continuous (affineForwardFun n) := by
  refine' continuous_induced_rng.mpr _;
  refine' continuous_pi _;
  intro i
  unfold affineForwardFun
  simp [sphereLastCoord];
  refine' Continuous.div _ _ _;
  · fun_prop;
  · fun_prop;
  · exact fun x => x.2

/-- The forward chart upstairs as a continuous map. -/
noncomputable def affineForwardMap (n : Nat) :
    C(sphereAffineCellSet n, EuclideanSpace Real (Fin (n + 1))) :=
  ⟨affineForwardFun n, continuous_affineForwardFun n⟩

theorem rpAffineCellToEuclidean_factors (n : Nat) :
    Function.FactorsThrough (affineForwardMap n) (affineCellProj n) := by
  intro a b hab
  change affineForwardFun n a = affineForwardFun n b
  have hp : proj (n + 1) a.1 = proj (n + 1) b.1 :=
    congrArg Subtype.val hab
  rcases eq_or_eq_neg_of_proj_eq hp with h | h
  · have hab' : a = b := Subtype.ext h
    rw [hab']
  · have ha : a = ⟨-b.1, by
        simpa using (sphereAffineCellSet_neg_iff n b.1).2 b.2⟩ :=
      Subtype.ext h
    rw [ha]
    exact affineForwardFun_neg n b

/-- The descended forward chart `rpAffineCellSpace n → R^(n+1)`. -/
noncomputable def rpAffineCellToEuclidean (n : Nat) :
    C(rpAffineCellSpace n, EuclideanSpace Real (Fin (n + 1))) :=
  (affineCellProj_isQuotientMap n).lift (affineForwardMap n)
    (rpAffineCellToEuclidean_factors n)

@[simp]
theorem rpAffineCellToEuclidean_proj (n : Nat) (x : sphereAffineCellSet n) :
    rpAffineCellToEuclidean n
      ⟨proj (n + 1) x.1, by
        show proj (n + 1) x.1 ∈ rpAffineCellSet n
        rw [← Set.mem_preimage, preimage_rpAffineCellSet]; exact x.2⟩
      = affineForwardFun n x := by
  apply DFunLike.congr_fun
    (Topology.IsQuotientMap.lift_comp (affineCellProj_isQuotientMap n)
      (affineForwardMap n) (rpAffineCellToEuclidean_factors n)) x

/-! ## The inverse chart -/

/-- The raw normalized inverse vector `(a, 1) / sqrt(1 + ‖a‖²)`. -/
noncomputable def affineInverseSphereVec
    (n : Nat) (a : EuclideanSpace Real (Fin (n + 1))) :
    EuclideanSpace Real (Fin (n + 2)) :=
  (Real.sqrt (‖(a : EuclideanSpace Real (Fin (n + 1)))‖ ^ 2 + 1))⁻¹ •
    (WithLp.equiv 2 (Fin (n + 2) → Real)).symm
      (Fin.snoc (fun i : Fin (n + 1) =>
        (a : EuclideanSpace Real (Fin (n + 1))) i) 1)

theorem affineInverseSphereVec_mem (n : Nat)
    (a : EuclideanSpace Real (Fin (n + 1))) :
    affineInverseSphereVec n a ∈
      Metric.sphere (0 : EuclideanSpace Real (Fin (n + 2))) 1 := by
  -- By definition of sphere, we need to show that the norm of `affineInverseSphereVec n a` is 1.
  simp [affineInverseSphereVec];
  rw [ norm_smul, Real.norm_of_nonneg ( by positivity ), EuclideanSpace.norm_eq ];
  norm_num [ EuclideanSpace.norm_eq, Fin.sum_univ_castSucc ];
  rw [ Real.sq_sqrt <| by positivity, inv_mul_eq_div, div_eq_iff ] <;> ring ; positivity

/-- The inverse chart lands on the sphere. -/
noncomputable def affineInverseSphere (n : Nat)
    (a : EuclideanSpace Real (Fin (n + 1))) : Sphere (n + 1) :=
  ⟨affineInverseSphereVec n a, affineInverseSphereVec_mem n a⟩

theorem affineInverseSphere_last_ne_zero
    (n : Nat) (a : EuclideanSpace Real (Fin (n + 1))) :
    sphereLastCoord n (affineInverseSphere n a) ≠ 0 := by
  unfold sphereLastCoord affineInverseSphere affineInverseSphereVec;
  simp +decide [ Fin.snoc ];
  positivity

theorem affineInverseSphere_mem_cell (n : Nat)
    (a : EuclideanSpace Real (Fin (n + 1))) :
    affineInverseSphere n a ∈ sphereAffineCellSet n :=
  affineInverseSphere_last_ne_zero n a

theorem continuous_euclideanToRpAffineCell (n : Nat) :
    Continuous (fun a : EuclideanSpace Real (Fin (n + 1)) =>
      (⟨proj (n + 1) (affineInverseSphere n a), by
          show proj (n + 1) (affineInverseSphere n a) ∈ rpAffineCellSet n
          rw [← Set.mem_preimage, preimage_rpAffineCellSet]
          exact affineInverseSphere_mem_cell n a⟩ : rpAffineCellSpace n)) := by
  refine' Continuous.subtype_mk ( Continuous.comp _ _ ) _;
  · exact ContinuousMap.continuous (proj (n + 1));
  · refine' continuous_induced_rng.mpr _;
    refine' continuous_induced_rng.mpr _;
    refine' continuous_pi fun i => _;
    refine' Continuous.mul _ _;
    · exact Continuous.inv₀ ( Real.continuous_sqrt.comp <| by continuity ) fun x => by positivity;
    · induction i using Fin.lastCases <;> simp +decide [ * ];
      · exact continuous_const;
      · fun_prop

/-- The inverse chart `R^(n+1) → rpAffineCellSpace n`. -/
noncomputable def euclideanToRpAffineCell (n : Nat) :
    C(EuclideanSpace Real (Fin (n + 1)), rpAffineCellSpace n) where
  toFun a := ⟨proj (n + 1) (affineInverseSphere n a), by
    show proj (n + 1) (affineInverseSphere n a) ∈ rpAffineCellSet n
    rw [← Set.mem_preimage, preimage_rpAffineCellSet]
    exact affineInverseSphere_mem_cell n a⟩
  continuous_toFun := continuous_euclideanToRpAffineCell n

@[simp]
theorem euclideanToRpAffineCell_apply (n : Nat)
    (a : EuclideanSpace Real (Fin (n + 1))) :
    ((euclideanToRpAffineCell n a : rpAffineCellSpace n) : RP (n + 1))
      = proj (n + 1) (affineInverseSphere n a) := rfl

/-! ## The inverse laws -/

/-
Forward after inverse is the identity.
-/
theorem rpAffineCell_forward_inverse (n : Nat) :
    (rpAffineCellToEuclidean n).comp (euclideanToRpAffineCell n)
      = ContinuousMap.id (EuclideanSpace Real (Fin (n + 1))) := by
  apply ContinuousMap.ext
  intro x
  rw [ContinuousMap.comp_apply]
  let y : sphereAffineCellSet n :=
    ⟨affineInverseSphere n x, affineInverseSphere_mem_cell n x⟩
  change rpAffineCellToEuclidean n (affineCellProj n y) = x
  have hchart : rpAffineCellToEuclidean n (affineCellProj n y) =
      affineForwardFun n y := by
    change rpAffineCellToEuclidean n ⟨proj (n + 1) y.1, _⟩ =
      affineForwardFun n y
    exact rpAffineCellToEuclidean_proj n y
  rw [hchart]
  change affineForwardFun n
      ⟨affineInverseSphere n x, affineInverseSphere_mem_cell n x⟩ = x
  unfold affineForwardFun affineInverseSphere affineInverseSphereVec sphereLastCoord
  simp +decide [Fin.snoc_castSucc, Fin.snoc_last]
  ext i
  simp +decide [mul_comm,
    ne_of_gt (Real.sqrt_pos.mpr (show 0 < ‖x‖ ^ 2 + 1 by positivity))]

/-
The inverse of the forward chart of a representative is antipodal to it.
-/
theorem affineInverse_forward_antipodal
    (n : Nat) (x : sphereAffineCellSet n) :
    AntipodalRel (affineInverseSphere n (affineForwardFun n x)) x.1 := by
  have h_norm : ‖(affineForwardFun n x : EuclideanSpace ℝ (Fin (n + 1)))‖^2 + 1 = 1 / (sphereLastCoord n x.1)^2 := by
    have h_norm : ‖(affineForwardFun n x : EuclideanSpace ℝ (Fin (n + 1)))‖^2 = lowerNormSq n x.1 / (sphereLastCoord n x.1)^2 := by
      unfold affineForwardFun lowerNormSq sphereLastCoord; simp +decide [ EuclideanSpace.norm_eq, Fin.sum_univ_castSucc ] ; ring;
      rw [ Real.sq_sqrt <| by positivity ] ; norm_num [ ← Finset.sum_mul _ _ _ ] ; ring;
    rw [ h_norm, lowerNormSq_eq_one_sub_last_sq ];
    rw [ div_add_one ] <;> ring ; aesop;
  cases lt_or_gt_of_ne ( show sphereLastCoord n x.1 ≠ 0 from x.2 ) <;> simp_all +decide [ AntipodalRel ];
  · refine Or.inr <| Subtype.ext <| ?_;
    ext i; exact (by
    induction i using Fin.lastCases <;> simp +decide [ *, affineInverseSphere, affineInverseSphereVec ];
    · rw [ Real.sqrt_sq_eq_abs, abs_of_neg ] <;> aesop;
    · rw [ Real.sqrt_sq_eq_abs, abs_of_neg ] <;> simp_all +decide [ affineForwardFun ];
      rw [ mul_div_cancel₀ _ ( ne_of_lt ‹_› ) ]);
  · left; ext i; simp [affineInverseSphere, affineInverseSphereVec];
    refine' Fin.lastCases _ _ i <;> simp_all +decide [ Fin.snoc ];
    · rw [ Real.sqrt_sq ( le_of_lt ‹_› ) ] ; rfl;
    · intro i; rw [ Real.sqrt_sq ( le_of_lt ‹_› ) ] ; simp +decide [ affineForwardFun, sphereLastCoord ] ;
      rw [ if_pos ( Nat.le_of_lt_succ i.2 ), mul_div_cancel₀ _ ( by linarith! ) ]

/-
Inverse after forward is the identity.
-/
theorem rpAffineCell_inverse_forward (n : Nat) :
    (euclideanToRpAffineCell n).comp (rpAffineCellToEuclidean n)
      = ContinuousMap.id (rpAffineCellSpace n) := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨x, rfl⟩ := (affineCellProj_isQuotientMap n).surjective q
  rw [ContinuousMap.comp_apply]
  have hforward : rpAffineCellToEuclidean n (affineCellProj n x) =
      affineForwardFun n x :=
    rpAffineCellToEuclidean_proj n x
  rw [hforward]
  apply Subtype.ext
  exact proj_eq_of_antipodalRel (affineInverse_forward_antipodal n x)

/-! ## The homeomorphism and contractibility -/

/-- The affine chart `V = RP^(n+1) \ RP^n ≃ₜ R^(n+1)`. -/
noncomputable def rpAffineCellHomeomorphEuclidean (n : Nat) :
    rpAffineCellSpace n ≃ₜ EuclideanSpace Real (Fin (n + 1)) where
  toEquiv :=
    { toFun := rpAffineCellToEuclidean n
      invFun := euclideanToRpAffineCell n
      left_inv := by
        intro x
        have h := congrArg (fun f => f x) (rpAffineCell_inverse_forward n)
        simpa using h
      right_inv := by
        intro a
        have h := congrArg (fun f => f a) (rpAffineCell_forward_inverse n)
        simpa using h }
  continuous_toFun := (rpAffineCellToEuclidean n).continuous
  continuous_invFun := (euclideanToRpAffineCell n).continuous

/-- The affine cell `V` is contractible. -/
instance rpAffineCell_contractibleSpace (n : Nat) :
    ContractibleSpace (rpAffineCellSpace n) :=
  Homeomorph.contractibleSpace (rpAffineCellHomeomorphEuclidean n)

/-! ## Homology corollary -/

/-- The positive-degree mod-2 subchain homology of the affine cell vanishes. -/
theorem rpAffineCell_subspaceHomology_isZero_pos
    (n m : Nat) (hm : 1 ≤ m) :
    IsZero ((subChainComplex (ZMod 2) (rpAmbientSpace n)
      (rpAffineCellOpen n : Set (rpAmbientSpace n))).homology m) :=
  isZero_subChainComplex_homologyZMod2_of_contractible
    (rpAmbientSpace n) (rpAffineCellOpen n : Set (rpAmbientSpace n)) m hm

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
