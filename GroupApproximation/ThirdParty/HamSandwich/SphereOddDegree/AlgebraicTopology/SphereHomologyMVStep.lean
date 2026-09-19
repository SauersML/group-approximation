import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SubChainSubspaceBridge
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.SphereTopHomology

/-!
# The Mayer–Vietoris recursive step for sphere homology

For `n ≥ 1` we prove `Hₙ₊₁(Sⁿ⁺¹; ℤ) ≅ Hₙ(Sⁿ; ℤ)` (`sphereTopHomology_step_MV`),
the recursive `step` of `SphereSuspensionTower`.

Cover `Sⁿ⁺¹` by the two punctured spheres `U = Sⁿ⁺¹ \ {north}` and
`V = Sⁿ⁺¹ \ {south}`.  Both are contractible (stereographic projection), so their
positive homology vanishes, and the Mayer–Vietoris connecting isomorphism
(`mvHomologyIso_succ`) gives `Hₙ₊₁(Sⁿ⁺¹) ≅ Hₙ(U ∩ V)`.  The intersection
`U ∩ V` is the equatorial band, homotopy equivalent to `Sⁿ`; the subspace bridge
(`subspaceHomologyIsoℤ`) and homotopy invariance then identify its homology with
`Hₙ(Sⁿ)`.
-/

open CategoryTheory AlgebraicTopology Limits Metric

noncomputable section
namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

open AffineBarycentricSubdivision

variable (n : ℕ)

/-- The north pole of `Sⁿ⁺¹` as a unit vector `e₀`. -/
def northVec : EuclideanSpace ℝ (Fin (n + 2)) := EuclideanSpace.single 0 1

theorem norm_northVec : ‖northVec n‖ = 1 := by
  simp [northVec]

/-- The north pole of `Sⁿ⁺¹`. -/
def northPole : Sphere (n + 1) := ⟨northVec n, by simp [norm_northVec]⟩

/-- The south pole of `Sⁿ⁺¹`, the antipode of the north pole. -/
def southPole : Sphere (n + 1) := ⟨-northVec n, by simp [norm_northVec]⟩

theorem northPole_ne_southPole : northPole n ≠ southPole n := by
  intro h
  apply_fun Subtype.val at h
  simp only [northPole, southPole] at h
  have hv : northVec n = 0 := by
    have h2 : (2 : ℝ) • northVec n = 0 := by rw [two_smul]; nth_rewrite 2 [h]; abel
    rcases smul_eq_zero.mp h2 with h0 | h0
    · norm_num at h0
    · exact h0
  have hnorm := norm_northVec n
  rw [hv, norm_zero] at hnorm
  norm_num at hnorm

/-- The upper punctured sphere `Sⁿ⁺¹ \ {north}`. -/
def upperPunctured : Set (Sphere (n + 1)) := {northPole n}ᶜ

/-- The lower punctured sphere `Sⁿ⁺¹ \ {south}`. -/
def lowerPunctured : Set (Sphere (n + 1)) := {southPole n}ᶜ

theorem isOpen_upperPunctured : IsOpen (upperPunctured n) :=
  isOpen_compl_singleton

theorem isOpen_lowerPunctured : IsOpen (lowerPunctured n) :=
  isOpen_compl_singleton

theorem upper_union_lower : upperPunctured n ∪ lowerPunctured n = Set.univ := by
  rw [upperPunctured, lowerPunctured, ← Set.compl_inter]
  rw [Set.compl_univ_iff, Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx1, hx2⟩
  rw [Set.mem_singleton_iff] at hx1 hx2
  exact northPole_ne_southPole n (hx1 ▸ hx2)

/-- The equatorial band `Sⁿ⁺¹ \ {north, south}`. -/
def sphereBand : Set (Sphere (n + 1)) := upperPunctured n ∩ lowerPunctured n

/-! ## Contractibility of the punctured spheres -/

instance contractible_upperPunctured : ContractibleSpace (upperPunctured n) := by
  let hnorm := norm_northVec n
  letI : ContractibleSpace ((stereographic hnorm).target) := by
    rw [stereographic_target]
    exact Homeomorph.contractibleSpace (Homeomorph.Set.univ _)
  have hsource : upperPunctured n = (stereographic hnorm).source := by
    rw [stereographic_source]
    ext x
    simp only [upperPunctured, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor <;> intro h hx <;> apply h <;> apply Subtype.ext <;>
      exact congrArg Subtype.val hx
  exact Homeomorph.contractibleSpace
    ((Homeomorph.setCongr hsource).trans (stereographic hnorm).toHomeomorphSourceTarget)

instance contractible_lowerPunctured : ContractibleSpace (lowerPunctured n) := by
  let hnorm : ‖-northVec n‖ = 1 := by simp [norm_northVec]
  letI : ContractibleSpace ((stereographic hnorm).target) := by
    rw [stereographic_target]
    exact Homeomorph.contractibleSpace (Homeomorph.Set.univ _)
  have hsource : lowerPunctured n = (stereographic hnorm).source := by
    rw [stereographic_source]
    ext x
    simp only [lowerPunctured, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor <;> intro h hx <;> apply h <;> apply Subtype.ext <;>
      exact congrArg Subtype.val hx
  exact Homeomorph.contractibleSpace
    ((Homeomorph.setCongr hsource).trans (stereographic hnorm).toHomeomorphSourceTarget)

/-! ## The equatorial band is homotopy equivalent to `Sⁿ` -/

/-
The equatorial band `Sⁿ⁺¹ \ {north, south}` is homotopy equivalent to `Sⁿ`.
-/
/-! ### Construction of the band ≃ Sⁿ homotopy equivalence -/

/-- The squared norm of the equatorial part (coordinates `1 .. n+1`) of a point of
`Sⁿ⁺¹`. -/
def eqNormSq (x : Sphere (n + 1)) : ℝ := ∑ i : Fin (n + 1), (x.val i.succ) ^ 2

theorem eqNormSq_eq (x : Sphere (n + 1)) : eqNormSq n x = 1 - (x.val 0) ^ 2 := by
  have h_norm_sq : ‖x.val‖^2 = ∑ i : Fin (n + 2), (x.val i)^2 := by
    rw [ EuclideanSpace.norm_eq ];
    rw [ Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _, Finset.sum_congr rfl fun _ _ => by rw [ Real.norm_eq_abs, sq_abs ] ];
  simp_all +decide [ Fin.sum_univ_succ, eqNormSq ]

theorem eqNormSq_pos {x : Sphere (n + 1)} (hx : x ∈ sphereBand n) : 0 < eqNormSq n x := by
  contrapose! hx;
  -- Since `eqNormSq n x ≤ 0`, we have `x.val i.succ = 0` for all `i : Fin (n + 1)`.
  have h_zero : ∀ i : Fin (n + 1), x.val i.succ = 0 := by
    exact fun i => sq_eq_zero_iff.mp ( le_antisymm ( le_trans ( Finset.single_le_sum ( fun a _ => sq_nonneg ( x.val ( Fin.succ a ) ) ) ( Finset.mem_univ i ) ) hx ) ( sq_nonneg _ ) );
  -- Since `x.val i.succ = 0` for all `i : Fin (n + 1)`, we have `x.val = northVec n` or `x.val = -northVec n`.
  have h_eq : x.val = northVec n ∨ x.val = -northVec n := by
    have h_eq : x.val 0 = 1 ∨ x.val 0 = -1 := by
      have h_eq : (x.val 0)^2 = 1 := by
        have := eqNormSq_eq n x;
        linarith [ show 0 ≤ eqNormSq n x from Finset.sum_nonneg fun _ _ => sq_nonneg _ ];
      exact sq_eq_one_iff.mp h_eq;
    exact Or.imp ( fun h => by ext i; induction i using Fin.inductionOn <;> aesop ) ( fun h => by ext i; induction i using Fin.inductionOn <;> aesop ) h_eq;
  intro hband
  rcases h_eq with hN | hS
  · have heq : x = northPole n := by
      apply Subtype.ext
      exact hN
    have hnot : x ≠ northPole n := by
      simpa only [upperPunctured, Set.mem_compl_iff, Set.mem_singleton_iff] using hband.1
    exact hnot heq
  · have heq : x = southPole n := by
      apply Subtype.ext
      exact hS
    have hnot : x ≠ southPole n := by
      simpa only [lowerPunctured, Set.mem_compl_iff, Set.mem_singleton_iff] using hband.2
    exact hnot heq

/-- The equatorial-projection map underlying `band → Sⁿ`: drop coordinate `0` and
normalize. -/
def fFun (x : Sphere (n + 1)) : EuclideanSpace ℝ (Fin (n + 1)) :=
  (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (fun i => x.val i.succ / Real.sqrt (eqNormSq n x))

theorem fFun_mem {x : Sphere (n + 1)} (hx : x ∈ sphereBand n) :
    fFun n x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
      simp +decide [ fFun, EuclideanSpace.norm_eq ];
      norm_num [ div_pow, Real.sq_sqrt ( show 0 ≤ eqNormSq n x from Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ];
      rw [ ← Finset.sum_div _ _ _, eqNormSq ];
      exact div_self <| ne_of_gt <| eqNormSq_pos n hx

theorem continuous_fFun_band :
    Continuous (fun x : ↥(sphereBand n) => (⟨fFun n x.val, fFun_mem n x.2⟩ : Sphere n)) := by
      refine' Continuous.subtype_mk _ _;
      refine' continuous_iff_continuousAt.mpr _;
      intro x
      have h_cont : ContinuousAt (fun x : EuclideanSpace ℝ (Fin (n + 2)) => (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (fun i => x i.succ / Real.sqrt (∑ i : Fin (n + 1), (x i.succ) ^ 2))) x.val := by
        refine' ContinuousAt.comp ( _ : ContinuousAt ( fun x : Fin ( n + 1 ) → ℝ => ( WithLp.equiv 2 ( Fin ( n + 1 ) → ℝ ) ).symm x ) _ ) _;
        · exact Continuous.continuousAt ( by continuity );
        · refine' tendsto_pi_nhds.mpr fun i => ContinuousAt.div _ _ _;
          · exact Continuous.continuousAt ( by exact continuous_apply _ |> Continuous.comp <| by continuity );
          · fun_prop;
          · exact ne_of_gt <| Real.sqrt_pos.mpr <| eqNormSq_pos n x.2;
      exact h_cont.tendsto.comp ( continuous_subtype_val.continuousAt.comp ( continuous_subtype_val.continuousAt ) )

/-- The continuous map `band → Sⁿ`. -/
def bandToSphere : C(↥(sphereBand n), Sphere n) :=
  ⟨fun x => ⟨fFun n x.val, fFun_mem n x.2⟩, continuous_fFun_band n⟩

/-- The inclusion map underlying `Sⁿ → band`: prepend a `0` coordinate. -/
def gFun (y : Sphere n) : EuclideanSpace ℝ (Fin (n + 2)) :=
  (WithLp.equiv 2 (Fin (n + 2) → ℝ)).symm (Fin.cons 0 (fun i => y.val i))

theorem gFun_mem_sphere (y : Sphere n) :
    gFun n y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 := by
      simp +decide [ gFun, EuclideanSpace.norm_eq ];
      convert y.2 using 1;
      rw [ mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq ] ; norm_num [ Fin.sum_univ_succ ]

theorem gFun_mem_band (y : Sphere n) :
    (⟨gFun n y, gFun_mem_sphere n y⟩ : Sphere (n + 1)) ∈ sphereBand n := by
      constructor <;> intro h <;> simp_all +decide;
      · injection h with h ; replace h := congr_arg ( fun z => z 0 ) h ;
        simp_all +decide [gFun, northVec];
      · injection h with h ; have := congr_arg ( fun x => x 0 ) h ; norm_num [ southPole ] at this;
        simp +decide [ gFun, northVec ] at this

theorem continuous_gFun :
    Continuous (fun y : Sphere n =>
      (⟨⟨gFun n y, gFun_mem_sphere n y⟩, gFun_mem_band n y⟩ : ↥(sphereBand n))) := by
        refine' Continuous.subtype_mk ( Continuous.subtype_mk _ _ ) _;
        -- The function y ↦ Fin.cons 0 (fun i => y.val i) is continuous because it is a composition of continuous functions.
        have h_cont : Continuous (fun y : Sphere n => Fin.cons 0 (fun i => y.val i) : Sphere n → Fin (n + 2) → ℝ) := by
          refine' continuous_pi_iff.mpr _;
          intro i; induction i using Fin.inductionOn <;> simp_all +decide [ Fin.cons ] ;
          · exact continuous_const;
          · fun_prop;
        convert h_cont using 1;
        exact iff_of_true ( Continuous.comp ( by continuity ) h_cont ) h_cont

/-- The continuous map `Sⁿ → band`. -/
def sphereToBand : C(Sphere n, ↥(sphereBand n)) :=
  ⟨fun y => ⟨⟨gFun n y, gFun_mem_sphere n y⟩, gFun_mem_band n y⟩, continuous_gFun n⟩

theorem bandToSphere_comp_sphereToBand :
    (bandToSphere n).comp (sphereToBand n) = ContinuousMap.id (Sphere n) := by
      ext i; simp [bandToSphere, sphereToBand, fFun, gFun];
      rw [ eqNormSq_eq ] ; norm_num [ Fin.sum_univ_succ ]

/-- The straight-line-on-the-sphere homotopy from `sphereToBand ∘ bandToSphere` to the
identity of the band. -/
def bandHomotopyFun (p : unitInterval × ↥(sphereBand n)) : EuclideanSpace ℝ (Fin (n + 2)) :=
  (1 - (p.1 : ℝ)) • ((sphereToBand n (bandToSphere n p.2)).val.val) + (p.1 : ℝ) • p.2.val.val

theorem bandHomotopyFun_ne_zero (p : unitInterval × ↥(sphereBand n)) :
    bandHomotopyFun n p ≠ 0 := by
      unfold bandHomotopyFun;
      obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), p.2.val.val i.succ ≠ 0 := by
        have h_pos : 0 < ∑ i : Fin (n + 1), (p.2.val.val i.succ) ^ 2 := by
          exact eqNormSq_pos n p.2.2;
        exact not_forall.mp fun h => h_pos.ne' <| Finset.sum_eq_zero fun i _ => by simp +decide [ h i ] ;
      intro h; have := congr_arg ( fun x => x i.succ ) h; norm_num [ hi, sphereToBand, bandToSphere, fFun, gFun ] at this;
      by_cases h : p.1.val = 0 <;> simp_all +decide [div_eq_mul_inv, mul_comm];
      · exact absurd this ( ne_of_gt ( Real.sqrt_pos.mpr ( eqNormSq_pos n p.2.2 ) ) );
      · exact hi ( by nlinarith [ show 0 < ( 1 - p.1.val ) * ( Real.sqrt ( eqNormSq n p.2.val ) ) ⁻¹ + p.1.val from by exact add_pos_of_nonneg_of_pos ( mul_nonneg ( sub_nonneg.2 <| p.1.2.2 ) <| inv_nonneg.2 <| Real.sqrt_nonneg _ ) <| lt_of_le_of_ne ( p.1.2.1 ) <| Ne.symm <| by aesop ] )

theorem bandHomotopy_mem_sphere (p : unitInterval × ↥(sphereBand n)) :
    (‖bandHomotopyFun n p‖⁻¹ • bandHomotopyFun n p) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 := by
        simp +decide [norm_smul, bandHomotopyFun_ne_zero]

theorem bandHomotopy_mem_band (p : unitInterval × ↥(sphereBand n)) :
    (⟨‖bandHomotopyFun n p‖⁻¹ • bandHomotopyFun n p, bandHomotopy_mem_sphere n p⟩ : Sphere (n + 1))
      ∈ sphereBand n := by
        obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), p.2.val.val i.succ ≠ 0 := by
          exact not_forall.mp fun h => absurd ( eqNormSq_pos n p.2.2 ) ( by simp +decide [ h, eqNormSq ] );
        have h_coord : (‖bandHomotopyFun n p‖⁻¹ • bandHomotopyFun n p) (Fin.succ i) ≠ 0 := by
          simp_all +decide [ bandHomotopyFun, sphereToBand, bandToSphere, fFun, gFun ];
          field_simp;
          rw [ div_eq_iff ] <;> norm_num [ hi ];
          · by_cases h : p.1.val = 0 <;> simp_all +decide [div_eq_mul_inv];
            · exact ne_of_gt <| Real.sqrt_pos.mpr <| eqNormSq_pos n p.2.2;
            · exact ne_of_gt ( add_pos_of_nonneg_of_pos ( mul_nonneg ( sub_nonneg.2 <| p.1.2.2 ) <| inv_nonneg.2 <| Real.sqrt_nonneg _ ) <| lt_of_le_of_ne ( p.1.2.1 ) <| Ne.symm <| by aesop );
          · change bandHomotopyFun n p ≠ 0
            exact bandHomotopyFun_ne_zero n p;
        constructor <;> intro h <;> simp_all +decide [ sphereBand ];
        · injection h with h ; replace h := congr_arg ( fun z => z i.succ ) h ;
          simp_all +decide [ northVec ];
        · injection h with h ; replace h := congr_arg ( fun x => x ( Fin.succ i ) ) h ; simp_all +decide [ northVec ]

theorem continuous_bandHomotopy :
    Continuous (fun p : unitInterval × ↥(sphereBand n) =>
      (⟨⟨‖bandHomotopyFun n p‖⁻¹ • bandHomotopyFun n p, bandHomotopy_mem_sphere n p⟩,
        bandHomotopy_mem_band n p⟩ : ↥(sphereBand n))) := by
  have ht : Continuous (fun p : unitInterval × ↥(sphereBand n) => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hcomp : Continuous (fun p : unitInterval × ↥(sphereBand n) =>
      ((sphereToBand n) ((bandToSphere n) p.2)).val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp
      ((sphereToBand n).continuous.comp ((bandToSphere n).continuous.comp continuous_snd)))
  have hp2 : Continuous (fun p : unitInterval × ↥(sphereBand n) => p.2.val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  have hfun : Continuous (bandHomotopyFun n) := by
    unfold bandHomotopyFun
    exact ((continuous_const.sub ht).smul hcomp).add (ht.smul hp2)
  have hscale : Continuous (fun p : unitInterval × ↥(sphereBand n) =>
      ‖bandHomotopyFun n p‖⁻¹) :=
    Continuous.inv₀ hfun.norm fun p => norm_ne_zero_iff.mpr (bandHomotopyFun_ne_zero n p)
  exact Continuous.subtype_mk
    (Continuous.subtype_mk (hscale.smul hfun) _) _

theorem bandHomotopy_zero (x : ↥(sphereBand n)) :
    (⟨⟨‖bandHomotopyFun n (0, x)‖⁻¹ • bandHomotopyFun n (0, x), bandHomotopy_mem_sphere n (0, x)⟩,
        bandHomotopy_mem_band n (0, x)⟩ : ↥(sphereBand n))
      = (sphereToBand n).comp (bandToSphere n) x := by
        -- Since $t = 0$, we have $bandHomotopyFun n (0, x) = gfx$ by definition.
        have h_bandHomotopy_zero : bandHomotopyFun n (0, x) = (sphereToBand n (bandToSphere n x)).val.val := by
          unfold bandHomotopyFun; norm_num [ sphereToBand, bandToSphere, fFun, gFun ] ;
        simp +decide [ h_bandHomotopy_zero ]

theorem bandHomotopy_one (x : ↥(sphereBand n)) :
    (⟨⟨‖bandHomotopyFun n (1, x)‖⁻¹ • bandHomotopyFun n (1, x), bandHomotopy_mem_sphere n (1, x)⟩,
        bandHomotopy_mem_band n (1, x)⟩ : ↥(sphereBand n))
      = ContinuousMap.id _ x := by
        norm_num [ bandHomotopyFun ]

/-- The homotopy `sphereToBand ∘ bandToSphere ≃ id`. -/
def bandHomotopy :
    ContinuousMap.Homotopy ((sphereToBand n).comp (bandToSphere n)) (ContinuousMap.id _) where
  toFun p := ⟨⟨‖bandHomotopyFun n p‖⁻¹ • bandHomotopyFun n p, bandHomotopy_mem_sphere n p⟩,
    bandHomotopy_mem_band n p⟩
  continuous_toFun := continuous_bandHomotopy n
  map_zero_left := bandHomotopy_zero n
  map_one_left := bandHomotopy_one n

/-- The equatorial band `Sⁿ⁺¹ \ {north, south}` is homotopy equivalent to `Sⁿ`. -/
def sphereBandHomotopyEquiv : ContinuousMap.HomotopyEquiv (sphereBand n) (Sphere n) where
  toFun := bandToSphere n
  invFun := sphereToBand n
  left_inv := ⟨bandHomotopy n⟩
  right_inv := bandToSphere_comp_sphereToBand n ▸ ContinuousMap.Homotopic.refl _

/-! ## Assembly of the Mayer–Vietoris step -/

/-- The categorical space `Sⁿ⁺¹` realized as a `TopCat` from the project model. -/
abbrev sphereSpace : TopCat.{0} := TopCat.of (Sphere (n + 1))

/-- The upper punctured sphere as an open set of `Sⁿ⁺¹`. -/
def upperOpens : TopologicalSpace.Opens (sphereSpace n) :=
  ⟨upperPunctured n, isOpen_upperPunctured n⟩

/-- The lower punctured sphere as an open set of `Sⁿ⁺¹`. -/
def lowerOpens : TopologicalSpace.Opens (sphereSpace n) :=
  ⟨lowerPunctured n, isOpen_lowerPunctured n⟩

instance contractible_upperOpens :
    ContractibleSpace (upperOpens n : Set (sphereSpace n)) := contractible_upperPunctured n

instance contractible_lowerOpens :
    ContractibleSpace (lowerOpens n : Set (sphereSpace n)) := contractible_lowerPunctured n

theorem upperOpens_sup_lowerOpens : upperOpens n ⊔ lowerOpens n = ⊤ := by
  apply TopologicalSpace.Opens.ext
  simpa [upperOpens, lowerOpens] using upper_union_lower n

/-- The integral homology of the band is isomorphic to `Hₙ(Sⁿ; ℤ)`, via the
subspace bridge and homotopy invariance. -/
def bandHomologyIso :
    (subChainComplex ℤ (sphereSpace n)
      ((upperOpens n : Set (sphereSpace n)) ∩ (lowerOpens n : Set (sphereSpace n)))).homology n ≅
      sphereTopHomologyℤ n :=
  subspaceHomologyIsoℤ (sphereSpace n)
      ((upperOpens n : Set (sphereSpace n)) ∩ (lowerOpens n : Set (sphereSpace n))) n
    ≪≫ singularHomologyℤ_isoOfHomotopyEquivSpace n (sphereBandHomotopyEquiv n)
    ≪≫ (sphereModelHomologyIso n n).symm

/-- **The Mayer–Vietoris recursive step.** For `n ≥ 1`,
`Hₙ₊₁(Sⁿ⁺¹; ℤ) ≅ Hₙ(Sⁿ; ℤ)`. -/
def sphereTopHomology_step_MV (hn : 1 ≤ n) :
    sphereTopHomologyℤ (n + 1) ≅ sphereTopHomologyℤ n :=
  sphereModelHomologyIso (n + 1) (n + 1)
    ≪≫ mvHomologyIso_succ ℤ (upperOpens n) (lowerOpens n) (upperOpens_sup_lowerOpens n) n
        (isZero_subChainComplex_homology_of_contractible _ _ (n + 1) (by omega))
        (isZero_subChainComplex_homology_of_contractible _ _ (n + 1) (by omega))
        (isZero_subChainComplex_homology_of_contractible _ _ n hn)
        (isZero_subChainComplex_homology_of_contractible _ _ n hn)
    ≪≫ bandHomologyIso n

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
