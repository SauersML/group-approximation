import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnAffineCellContractible
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SphereHomologyMVStep
import Mathlib

/-!
# The affine overlap `U ∩ V` is homotopy equivalent to `Sⁿ`

We prove that the Mayer–Vietoris overlap

```text
U ∩ V = (RP^(n+1) \ {north}) ∩ (RP^(n+1) \ RP^n)
```

is homotopy equivalent to `Sⁿ`.

Under the affine chart `rpAffineCellHomeomorphEuclidean` the overlap corresponds
to the punctured Euclidean space `R^(n+1) \ {0}`, because the deleted projective
north point is exactly the affine coordinate `0`.  The punctured Euclidean space
radially deformation retracts onto `Sⁿ`.
-/

noncomputable section

open CategoryTheory TopologicalSpace Metric Topology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

variable (n : Nat)

/-! ## Punctured Euclidean space -/

/-- Punctured Euclidean space `R^(n+1) \ {0}`. -/
abbrev puncturedEuclidean (n : Nat) : Type :=
  {a : EuclideanSpace Real (Fin (n + 1)) // a ≠ 0}

theorem norm_inv_smul_eq_one {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {a : E} (ha : a ≠ 0) : ‖‖a‖⁻¹ • a‖ = 1 := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg a))]
  rw [inv_mul_eq_one₀]
  exact norm_ne_zero_iff.mpr ha

/-- The radial map `R^(n+1) \ {0} → Sⁿ`, `a ↦ a / ‖a‖`. -/
noncomputable def puncturedToSphere (n : Nat) : C(puncturedEuclidean n, Sphere n) where
  toFun a :=
    ⟨‖a.1‖⁻¹ • a.1, by
      rw [mem_sphere_zero_iff_norm]
      exact norm_inv_smul_eq_one a.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (Continuous.inv₀ (Continuous.norm continuous_subtype_val)
      (fun a => norm_ne_zero_iff.mpr a.2)).smul continuous_subtype_val

/-- The inclusion `Sⁿ → R^(n+1) \ {0}`. -/
noncomputable def sphereToPunctured (n : Nat) : C(Sphere n, puncturedEuclidean n) where
  toFun y := ⟨(y : EuclideanSpace Real (Fin (n + 1))), by
    intro h
    have hy : ‖(y : EuclideanSpace Real (Fin (n + 1)))‖ = 1 := by
      exact mem_sphere_zero_iff_norm.mp y.2
    simp [h] at hy⟩
  continuous_toFun := by
    exact Continuous.subtype_mk continuous_subtype_val _

theorem puncturedToSphere_comp_sphereToPunctured (n : Nat) :
    (puncturedToSphere n).comp (sphereToPunctured n) = ContinuousMap.id (Sphere n) := by
  ext y i
  have hy : ‖(y : EuclideanSpace Real (Fin (n + 1)))‖ = 1 := by
    exact mem_sphere_zero_iff_norm.mp y.2
  simp [puncturedToSphere, sphereToPunctured, hy]

/-! ## The radial deformation retraction homotopy -/

/-- The homotopy scalar-times-vector `H(t,a) = ((1-t)/‖a‖ + t) • a`. -/
noncomputable def puncturedRadialHomotopyFun
    (n : Nat) (p : unitInterval × puncturedEuclidean n) :
    EuclideanSpace Real (Fin (n + 1)) :=
  (((1 - (p.1 : Real)) * ‖p.2.1‖⁻¹ + (p.1 : Real)) : Real) • p.2.1

theorem puncturedRadialHomotopyFun_ne_zero
    (n : Nat) (p : unitInterval × puncturedEuclidean n) :
    puncturedRadialHomotopyFun n p ≠ 0 := by
  intro h
  have hscalar_pos :
      0 < ((1 - (p.1 : Real)) * ‖p.2.1‖⁻¹ + (p.1 : Real)) := by
    have ht0 : 0 ≤ (p.1 : Real) := p.1.2.1
    have ht1 : (p.1 : Real) ≤ 1 := p.1.2.2
    have hn : 0 < ‖p.2.1‖ := norm_pos_iff.mpr p.2.2
    have hinv : 0 < ‖p.2.1‖⁻¹ := inv_pos.mpr hn
    have hnonneg : 0 ≤ (1 - (p.1 : Real)) * ‖p.2.1‖⁻¹ :=
      mul_nonneg (sub_nonneg.mpr ht1) (le_of_lt hinv)
    by_cases ht : (p.1 : Real) = 0
    · rw [ht]; simpa using hinv
    · exact add_pos_of_nonneg_of_pos hnonneg (lt_of_le_of_ne ht0 (Ne.symm ht))
  exact p.2.2 (smul_eq_zero.mp h |>.resolve_left hscalar_pos.ne')

theorem continuous_puncturedRadialHomotopy (n : Nat) :
    Continuous (fun p : unitInterval × puncturedEuclidean n =>
      (⟨puncturedRadialHomotopyFun n p, puncturedRadialHomotopyFun_ne_zero n p⟩ :
        puncturedEuclidean n)) := by
  refine Continuous.subtype_mk ?_ _
  have hv : Continuous (fun p : unitInterval × puncturedEuclidean n =>
      (p.2.1 : EuclideanSpace Real (Fin (n + 1)))) :=
    continuous_subtype_val.comp continuous_snd
  have ht : Continuous (fun p : unitInterval × puncturedEuclidean n => (p.1 : Real)) :=
    continuous_subtype_val.comp continuous_fst
  have hnorm : Continuous (fun p : unitInterval × puncturedEuclidean n => ‖p.2.1‖⁻¹) :=
    hv.norm.inv₀ (fun p => norm_ne_zero_iff.mpr p.2.2)
  have hscalar : Continuous (fun p : unitInterval × puncturedEuclidean n =>
      ((1 - (p.1 : Real)) * ‖p.2.1‖⁻¹ + (p.1 : Real))) :=
    ((continuous_const.sub ht).mul hnorm).add ht
  exact hscalar.smul hv

theorem puncturedRadialHomotopy_zero (n : Nat) (a : puncturedEuclidean n) :
    (⟨puncturedRadialHomotopyFun n (0, a), puncturedRadialHomotopyFun_ne_zero n (0, a)⟩ :
        puncturedEuclidean n)
      = ((sphereToPunctured n).comp (puncturedToSphere n)) a := by
  apply Subtype.ext
  simp [puncturedRadialHomotopyFun, puncturedToSphere, sphereToPunctured]

theorem puncturedRadialHomotopy_one (n : Nat) (a : puncturedEuclidean n) :
    (⟨puncturedRadialHomotopyFun n (1, a), puncturedRadialHomotopyFun_ne_zero n (1, a)⟩ :
        puncturedEuclidean n)
      = ContinuousMap.id (puncturedEuclidean n) a := by
  apply Subtype.ext
  simp [puncturedRadialHomotopyFun]

/-- The radial deformation retraction homotopy `sphereToPunctured ∘ puncturedToSphere ≃ id`. -/
noncomputable def puncturedRadialHomotopy (n : Nat) :
    ContinuousMap.Homotopy
      ((sphereToPunctured n).comp (puncturedToSphere n))
      (ContinuousMap.id (puncturedEuclidean n)) where
  toFun p := ⟨puncturedRadialHomotopyFun n p,
    puncturedRadialHomotopyFun_ne_zero n p⟩
  continuous_toFun := continuous_puncturedRadialHomotopy n
  map_zero_left := puncturedRadialHomotopy_zero n
  map_one_left := puncturedRadialHomotopy_one n

/-- **Punctured Euclidean space is homotopy equivalent to `Sⁿ`.** -/
noncomputable def puncturedEuclidean_homotopyEquiv_sphere (n : Nat) :
    ContinuousMap.HomotopyEquiv (puncturedEuclidean n) (Sphere n) where
  toFun := puncturedToSphere n
  invFun := sphereToPunctured n
  left_inv := ⟨puncturedRadialHomotopy n⟩
  right_inv :=
    puncturedToSphere_comp_sphereToPunctured n ▸ ContinuousMap.Homotopic.refl _

/-! ## Identifying the overlap with punctured Euclidean space -/

/-
`euclideanToRpAffineCell n 0` is the projective north point.
-/
theorem euclideanToRpAffineCell_zero_coe (n : Nat) :
    ((euclideanToRpAffineCell n 0 : rpAffineCellSpace n) : RP (n + 1)) = rpNorth n := by
  convert euclideanToRpAffineCell_apply n 0 using 1;
  unfold affineInverseSphere;
  convert proj_eq_of_antipodalRel _ using 1;
  unfold rpNorthSphere affineInverseSphereVec;
  unfold AntipodalRel; norm_num [ elast ];
  left; ext i; induction i using Fin.lastCases <;> simp +decide [ *, Fin.snoc ] ;
  exact Nat.le_of_lt_succ ( Fin.is_lt _ )

/-
**The vanishing criterion.** The affine coordinate of `x` is `0` iff `x` is the
projective north point.
-/
theorem rpAffineCellToEuclidean_eq_zero_iff
    (n : Nat) (x : rpAffineCellSpace n) :
    rpAffineCellToEuclidean n x = 0 ↔ (x : RP (n + 1)) = rpNorth n := by
  constructor <;> intro h;
  · have := congr_arg ( fun f => f x ) ( rpAffineCell_inverse_forward n ) ; simp_all +decide ;
    exact this ▸ euclideanToRpAffineCell_zero_coe n;
  · have h_eq : x = (euclideanToRpAffineCell n 0 : rpAffineCellSpace n) := by
      exact Subtype.ext <| h.trans <| euclideanToRpAffineCell_zero_coe n ▸ rfl;
    rw [ h_eq, ← ContinuousMap.comp_apply, rpAffineCell_forward_inverse ] ; aesop

/-- The forward map `U ∩ V → R^(n+1) \ {0}` via the affine chart. -/
noncomputable def rpAffineOverlapToPuncturedEuclidean (n : Nat) :
    C(rpAffineOverlapSpace n, puncturedEuclidean n) where
  toFun x := ⟨rpAffineCellToEuclidean n ⟨x.1, x.2.2⟩, by
    rw [ne_eq, rpAffineCellToEuclidean_eq_zero_iff]
    exact x.2.1⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (rpAffineCellToEuclidean n).continuous.comp
      (Continuous.subtype_mk continuous_subtype_val _)

/-- The inverse map `R^(n+1) \ {0} → U ∩ V` via the affine chart. -/
noncomputable def puncturedEuclideanToRpAffineOverlap (n : Nat) :
    C(puncturedEuclidean n, rpAffineOverlapSpace n) where
  toFun a := ⟨(euclideanToRpAffineCell n a.1 : rpAffineCellSpace n),
    ⟨by
      show ((euclideanToRpAffineCell n a.1 : rpAffineCellSpace n) : RP (n + 1)) ≠ rpNorth n
      rw [ne_eq, ← rpAffineCellToEuclidean_eq_zero_iff]
      have h := congrArg (fun f => f a.1) (rpAffineCell_forward_inverse n)
      simp only [ContinuousMap.comp_apply, ContinuousMap.id_apply] at h
      rw [h]; exact a.2,
     (euclideanToRpAffineCell n a.1).2⟩⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp
      ((euclideanToRpAffineCell n).continuous.comp continuous_subtype_val)

theorem rpAffineOverlap_forward_inverse (n : Nat) :
    (rpAffineOverlapToPuncturedEuclidean n).comp
        (puncturedEuclideanToRpAffineOverlap n)
      = ContinuousMap.id (puncturedEuclidean n) := by
  ext a;
  convert congr_arg ( fun f => f a.1 ) ( rpAffineCell_forward_inverse n ) using 1;
  refine' ⟨ fun h => _, fun h => _ ⟩;
  · exact congr_arg ( fun f => f a.1 ) ( rpAffineCell_forward_inverse n );
  · convert congr_arg ( fun x : EuclideanSpace ℝ ( Fin ( n + 1 ) ) => x ‹_› ) h using 1

theorem rpAffineOverlap_inverse_forward (n : Nat) :
    (puncturedEuclideanToRpAffineOverlap n).comp
        (rpAffineOverlapToPuncturedEuclidean n)
      = ContinuousMap.id (rpAffineOverlapSpace n) := by
  ext x;
  convert congr_arg Subtype.val ( congr_arg ( fun f => f ⟨ x.1, x.2.2 ⟩ ) ( rpAffineCell_inverse_forward n ) ) using 1

/-- **The overlap is homeomorphic to punctured Euclidean space.** -/
noncomputable def rpAffineOverlapHomeomorphPuncturedEuclidean (n : Nat) :
    rpAffineOverlapSpace n ≃ₜ puncturedEuclidean n where
  toEquiv :=
    { toFun := rpAffineOverlapToPuncturedEuclidean n
      invFun := puncturedEuclideanToRpAffineOverlap n
      left_inv := by
        intro x
        have h := congrArg (fun f => f x) (rpAffineOverlap_inverse_forward n)
        simpa using h
      right_inv := by
        intro a
        have h := congrArg (fun f => f a) (rpAffineOverlap_forward_inverse n)
        simpa using h }
  continuous_toFun := (rpAffineOverlapToPuncturedEuclidean n).continuous
  continuous_invFun := (puncturedEuclideanToRpAffineOverlap n).continuous

/-! ## Final assembly -/

/-- **The affine overlap is homotopy equivalent to `Sⁿ`.** -/
noncomputable def rpAffineOverlap_homotopyEquiv_sphere (n : Nat) :
    ContinuousMap.HomotopyEquiv (rpAffineOverlapSpace n) (Sphere n) :=
  (rpAffineOverlapHomeomorphPuncturedEuclidean n).toHomotopyEquiv.trans
    (puncturedEuclidean_homotopyEquiv_sphere n)

/-! ## Homology corollary -/

/-- The mod-2 subchain homology of the overlap is isomorphic to `Hₖ(Sⁿ; F₂)`. -/
noncomputable def rpAffineOverlap_subspaceHomologyIso_sphere
    (n k : Nat) :
    (subChainComplex (ZMod 2) (rpAmbientSpace n)
      ((rpDeletedNorthOpen n : Set (rpAmbientSpace n)) ∩
       (rpAffineCellOpen n : Set (rpAmbientSpace n)))).homology k
      ≅ homologyZMod2 (TopCat.of (Sphere n)) k :=
  subspaceHomologyIso _ k ≪≫
    homologyIsoOfHomotopyEquivModule
      (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)) k
      (rpAffineOverlap_homotopyEquiv_sphere n)

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
