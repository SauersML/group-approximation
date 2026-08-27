import GroupApproximation.PropertyTT.LocalizedComplexPlane
import GroupApproximation.PropertyTT.RankFourColumnGeometry
import GroupApproximation.PropertyTT.UniformOrbitProjection
import GroupApproximation.PropertyTT.UnitaryDisplacement

/-!
# Relative `(TT)/T` for a rank-four root

This is the quantitative rank-four key trick.  The two embedded rank-three
planes control the moving part of a quasi-cocycle value on `X₀₃`; the
Steinberg commutator controls the missing root direction; and the bounded
orbit projection theorem closes the estimate.
-/

namespace GroupApproximation
namespace RankFourRelativeTT

open scoped InnerProductSpace commutatorElement
open FreeElementaryPropertyT
open FreeRootCharacterValuation
open RankFourRootGeometry
open RankFourColumnGeometry

noncomputable section

universe v

variable (X : Type*) [Fintype X]

abbrev R := FreeAlgebra (ZMod 2) X
abbrev G3 := elementaryGroup (Fin 3) (R X)
abbrev G4 := elementaryGroup (Fin 4) (R X)

/-- One finite number dominating the quasi-cocycle values on both embedded
copies of the rank-three control set. -/
noncomputable def embeddedControlNormSum
    {E : Type v} [NormedAddCommGroup E] (b : G4 X → E) : ℝ :=
  ∑ s ∈ controlSet X,
    (‖b (embed123 X s)‖ + ‖b (embedRow012 X s)‖)

theorem embeddedControlNormSum_nonneg
    {E : Type v} [NormedAddCommGroup E] (b : G4 X → E) :
    0 ≤ embeddedControlNormSum X b := by
  classical
  exact Finset.sum_nonneg fun s _ ↦
    add_nonneg (norm_nonneg _) (norm_nonneg _)

theorem norm_embed123_controlElement_le
    {E : Type v} [NormedAddCommGroup E] (b : G4 X → E)
    (p : A2Root × Option (Fin (Fintype.card X))) :
    ‖b (embed123 X (controlElement X p))‖ ≤ embeddedControlNormSum X b := by
  classical
  calc
    ‖b (embed123 X (controlElement X p))‖ ≤
        ‖b (embed123 X (controlElement X p))‖ +
          ‖b (embedRow012 X (controlElement X p))‖ :=
      le_add_of_nonneg_right (norm_nonneg _)
    _ ≤ embeddedControlNormSum X b := by
      exact Finset.single_le_sum
        (fun (s : G3 X) _ ↦ add_nonneg
          (norm_nonneg (b (embed123 X s)))
          (norm_nonneg (b (embedRow012 X s))))
        (controlElement_mem X p)

theorem norm_embedRow012_controlElement_le
    {E : Type v} [NormedAddCommGroup E] (b : G4 X → E)
    (p : A2Root × Option (Fin (Fintype.card X))) :
    ‖b (embedRow012 X (controlElement X p))‖ ≤
      embeddedControlNormSum X b := by
  classical
  calc
    ‖b (embedRow012 X (controlElement X p))‖ ≤
        ‖b (embed123 X (controlElement X p))‖ +
          ‖b (embedRow012 X (controlElement X p))‖ :=
      le_add_of_nonneg_left (norm_nonneg _)
    _ ≤ embeddedControlNormSum X b := by
      exact Finset.single_le_sum
        (fun (s : G3 X) _ ↦ add_nonneg
          (norm_nonneg (b (embed123 X s)))
          (norm_nonneg (b (embedRow012 X s))))
        (controlElement_mem X p)

/-- The moving part of a quasi-cocycle value on `X₀₃` is uniformly bounded.
The bound depends only on the finite embedded control values and the defect,
not on the root coefficient `a`. -/
theorem norm_root03_movingProjection_le
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (rho : G4 X →* (E ≃ₗᵢ[ℂ] E)) (b : G4 X → E) (D : ℝ)
    (hb : IsQuasiCocycle rho b D) (a : R X) :
    letI : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
    ‖KazhdanFixedSpace.subgroupMovingProjection (realifyHom rho)
        (columnGroup X)
        (b (elementaryRoot (0 : Fin 4) 3 (by decide) a))‖ ≤
      6 * (2 * (6 * Fintype.card X + 6 : ℝ) *
        (2 * embeddedControlNormSum X b + 2 * D)) := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  let rhoR : G4 X →* (E ≃ₗᵢ[ℝ] E) := realifyHom rho
  let N : Subgroup (G4 X) := columnGroup X
  let r : G4 X := elementaryRoot (0 : Fin 4) 3 (by decide) a
  let M : ℝ := embeddedControlNormSum X b
  let B : ℝ := 2 * M + 2 * D
  let K : ℝ := 2 * (6 * Fintype.card X + 6 : ℝ) * B
  let w : E := KazhdanFixedSpace.subgroupMovingProjection rhoR N (b r)
  have hM : 0 ≤ M := embeddedControlNormSum_nonneg X b
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact add_nonneg (mul_nonneg (by norm_num) hM)
      (mul_nonneg (by norm_num) hb.1)
  have hcontrol123 (i j : Fin 3) (hij : i ≠ j)
      (q : Option (Fin (Fintype.card X))) :
      ‖b (embed123 X
        (elementaryRoot i j hij (controlCoefficient X q)))‖ ≤ M := by
    let p : A2Root × Option (Fin (Fintype.card X)) :=
      (⟨(i, j), hij⟩, q)
    simpa only [p, controlElement] using
      norm_embed123_controlElement_le X b p
  have hcontrolRow (i j : Fin 3) (hij : i ≠ j)
      (q : Option (Fin (Fintype.card X))) :
      ‖b (embedRow012 X
        (elementaryRoot i j hij (controlCoefficient X q)))‖ ≤ M := by
    let p : A2Root × Option (Fin (Fintype.card X)) :=
      (⟨(i, j), hij⟩, q)
    simpa only [p, controlElement] using
      norm_embedRow012_controlElement_le X b p
  have hmove_le {s : G4 X} (hs : s ∈ Subgroup.normalizer N) :
      ‖rho s w - w‖ ≤ ‖rho s (b r) - b r‖ := by
    change ‖rhoR s w - w‖ ≤ ‖rhoR s (b r) - b r‖
    exact
      KazhdanFixedSpace.norm_subgroupMovingProjection_displacement_le_of_mem_normalizer
        rhoR N hs (b r)
  have hnear123 (i j : Fin 3) (hij : i ≠ j)
      (q : Option (Fin (Fintype.card X)))
      (hcomm : Commute
        (embed123 X (elementaryRoot i j hij (controlCoefficient X q))) r)
      (hnorm : embed123 X
        (elementaryRoot i j hij (controlCoefficient X q)) ∈
          Subgroup.normalizer N) :
      ‖rho (embed123 X
          (elementaryRoot i j hij (controlCoefficient X q))) w - w‖ ≤ B := by
    apply (hmove_le hnorm).trans
    calc
      ‖rho (embed123 X
          (elementaryRoot i j hij (controlCoefficient X q))) (b r) - b r‖ ≤
          2 * ‖b (embed123 X
            (elementaryRoot i j hij (controlCoefficient X q)))‖ + 2 * D :=
        hb.norm_action_sub_of_commute_le hcomm
      _ ≤ B := by
        dsimp only [B]
        gcongr
        exact hcontrol123 i j hij q
  have hnearRow (i j : Fin 3) (hij : i ≠ j)
      (q : Option (Fin (Fintype.card X)))
      (hcomm : Commute
        (embedRow012 X (elementaryRoot i j hij (controlCoefficient X q))) r)
      (hnorm : embedRow012 X
        (elementaryRoot i j hij (controlCoefficient X q)) ∈
          Subgroup.normalizer N) :
      ‖rho (embedRow012 X
          (elementaryRoot i j hij (controlCoefficient X q))) w - w‖ ≤ B := by
    apply (hmove_le hnorm).trans
    calc
      ‖rho (embedRow012 X
          (elementaryRoot i j hij (controlCoefficient X q))) (b r) - b r‖ ≤
          2 * ‖b (embedRow012 X
            (elementaryRoot i j hij (controlCoefficient X q)))‖ + 2 * D :=
        hb.norm_action_sub_of_commute_le hcomm
      _ ≤ B := by
        dsimp only [B]
        gcongr
        exact hcontrolRow i j hij q
  have hcolIK :
      ‖rho (embed123 X
        (elementaryRoot (0 : Fin 3) 2 (by decide) 1)) w - w‖ ≤ B := by
    apply hnear123 (0 : Fin 3) 2 (by decide) none
    · rw [embed123_elementaryRoot]
      exact N.le_normalizer (root13_mem_columnGroup X 1)
    · rw [embed123_elementaryRoot]
      exact elementaryRoot_commute_of_ne
        (1 : Fin 4) 3 0 3 (by decide) (by decide)
          (by decide) (by decide) 1 a
  have hcolJK :
      ‖rho (embed123 X
        (elementaryRoot (1 : Fin 3) 2 (by decide) 1)) w - w‖ ≤ B := by
    apply hnear123 (1 : Fin 3) 2 (by decide) none
    · rw [embed123_elementaryRoot]
      exact N.le_normalizer (root23_mem_columnGroup X 1)
    · rw [embed123_elementaryRoot]
      exact elementaryRoot_commute_of_ne
        (2 : Fin 4) 3 0 3 (by decide) (by decide)
          (by decide) (by decide) 1 a
  have hcolIJ (q : Option (Fin (Fintype.card X))) :
      ‖rho (embed123 X
        (elementaryRoot (0 : Fin 3) 1 (by decide)
          (controlCoefficient X q))) w - w‖ ≤ B := by
    apply hnear123 (0 : Fin 3) 1 (by decide) q
    · rw [embed123_elementaryRoot]
      exact root12_mem_normalizer_columnGroup X _
    · rw [embed123_elementaryRoot]
      exact elementaryRoot_commute_of_ne
        (1 : Fin 4) 2 0 3 (by decide) (by decide)
          (by decide) (by decide) _ a
  have hcolJI (q : Option (Fin (Fintype.card X))) :
      ‖rho (embed123 X
        (elementaryRoot (1 : Fin 3) 0 (by decide)
          (controlCoefficient X q))) w - w‖ ≤ B := by
    apply hnear123 (1 : Fin 3) 0 (by decide) q
    · rw [embed123_elementaryRoot]
      exact root21_mem_normalizer_columnGroup X _
    · rw [embed123_elementaryRoot]
      exact elementaryRoot_commute_of_ne
        (2 : Fin 4) 1 0 3 (by decide) (by decide)
          (by decide) (by decide) _ a
  have hrowIK :
      ‖rho (embedRow012 X
        (elementaryRoot (1 : Fin 3) 0 (by decide) 1)) w - w‖ ≤ B := by
    apply hnearRow (1 : Fin 3) 0 (by decide) none
    · rw [embedRow012_controlRoot]
      exact root01_mem_normalizer_columnGroup X 1
    · rw [embedRow012_controlRoot]
      exact elementaryRoot_commute_of_ne
        (0 : Fin 4) 1 0 3 (by decide) (by decide)
          (by decide) (by decide) 1 a
  have hrowJK :
      ‖rho (embedRow012 X
        (elementaryRoot (2 : Fin 3) 0 (by decide) 1)) w - w‖ ≤ B := by
    apply hnearRow (2 : Fin 3) 0 (by decide) none
    · rw [embedRow012_controlRoot]
      exact root02_mem_normalizer_columnGroup X 1
    · rw [embedRow012_controlRoot]
      exact elementaryRoot_commute_of_ne
        (0 : Fin 4) 2 0 3 (by decide) (by decide)
          (by decide) (by decide) 1 a
  have hrowIJ (q : Option (Fin (Fintype.card X))) :
      ‖rho (embedRow012 X
        (elementaryRoot (1 : Fin 3) 2 (by decide)
          (controlCoefficient X q))) w - w‖ ≤ B := by
    apply hnearRow (1 : Fin 3) 2 (by decide) q
    · rw [embedRow012_controlRoot]
      exact root21_mem_normalizer_columnGroup X _
    · rw [embedRow012_controlRoot]
      exact elementaryRoot_commute_of_ne
        (2 : Fin 4) 1 0 3 (by decide) (by decide)
          (by decide) (by decide) _ a
  have hrowJI (q : Option (Fin (Fintype.card X))) :
      ‖rho (embedRow012 X
        (elementaryRoot (2 : Fin 3) 1 (by decide)
          (controlCoefficient X q))) w - w‖ ≤ B := by
    apply hnearRow (2 : Fin 3) 1 (by decide) q
    · rw [embedRow012_controlRoot]
      exact root12_mem_normalizer_columnGroup X _
    · rw [embedRow012_controlRoot]
      exact elementaryRoot_commute_of_ne
        (1 : Fin 4) 2 0 3 (by decide) (by decide)
          (by decide) (by decide) _ a
  have hcolPlane (g : G3 X)
      (hg : g ∈ elementaryRootSubgroup (0 : Fin 3) 2 (by decide) ⊔
        elementaryRootSubgroup (1 : Fin 3) 2 (by decide)) :
      ‖rho (embed123 X g) w - w‖ ≤ K := by
    have h := norm_comp_columnPlane_sub_le_of_root_bounds X
      (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
      (embed123 X) rho w hB hcolIK hcolJK
      (hcolIJ none) (hcolJI none)
      (fun q ↦ hcolIJ (some q)) (fun q ↦ hcolJI (some q)) g hg
    simpa only [K] using h
  have hrowPlane (g : G3 X)
      (hg : g ∈ elementaryRootSubgroup (1 : Fin 3) 0 (by decide) ⊔
        elementaryRootSubgroup (2 : Fin 3) 0 (by decide)) :
      ‖rho (embedRow012 X g) w - w‖ ≤ K := by
    have h := norm_comp_columnPlane_sub_le_of_root_bounds X
      (1 : Fin 3) 2 0 (by decide) (by decide) (by decide)
      (embedRow012 X) rho w hB hrowIK hrowJK
      (hrowIJ none) (hrowJI none)
      (fun q ↦ hrowIJ (some q)) (fun q ↦ hrowJI (some q)) g hg
    simpa only [K] using h
  have hcol13 (c : R X) :
      ‖rho (elementaryRoot (1 : Fin 4) 3 (by decide) c) w - w‖ ≤ K := by
    have h := hcolPlane
      (elementaryRoot (0 : Fin 3) 2 (by decide) c)
      ((show elementaryRootSubgroup (0 : Fin 3) 2 (by decide) ≤
          elementaryRootSubgroup (0 : Fin 3) 2 (by decide) ⊔
            elementaryRootSubgroup (1 : Fin 3) 2 (by decide) from le_sup_left)
        ⟨c, rfl⟩)
    simpa using h
  have hcol23 (c : R X) :
      ‖rho (elementaryRoot (2 : Fin 4) 3 (by decide) c) w - w‖ ≤ K := by
    have h := hcolPlane
      (elementaryRoot (1 : Fin 3) 2 (by decide) c)
      ((show elementaryRootSubgroup (1 : Fin 3) 2 (by decide) ≤
          elementaryRootSubgroup (0 : Fin 3) 2 (by decide) ⊔
            elementaryRootSubgroup (1 : Fin 3) 2 (by decide) from le_sup_right)
        ⟨c, rfl⟩)
    simpa using h
  have hrow01 (c : R X) :
      ‖rho (elementaryRoot (0 : Fin 4) 1 (by decide) c) w - w‖ ≤ K := by
    let c' : R X := -MulOpposite.unop
      (FreeAlgebra.reverseEquiv (ZMod 2) X c)
    have h := hrowPlane
      (elementaryRoot (1 : Fin 3) 0 (by decide) c')
      ((show elementaryRootSubgroup (1 : Fin 3) 0 (by decide) ≤
          elementaryRootSubgroup (1 : Fin 3) 0 (by decide) ⊔
            elementaryRootSubgroup (2 : Fin 3) 0 (by decide) from le_sup_left)
        ⟨c', rfl⟩)
    dsimp only [c'] at h
    rw [embedRow012_preimage_elementaryRoot] at h
    exact h
    all_goals decide
  have htarget (c : R X) :
      ‖rho (elementaryRoot (0 : Fin 4) 3 (by decide) c) w - w‖ ≤ 4 * K := by
    rw [← root01_root13_commutator X c]
    calc
      ‖rho ⁅elementaryRoot (0 : Fin 4) 1 (by decide) c,
          elementaryRoot (1 : Fin 4) 3 (by decide) 1⁆ w - w‖ ≤
          2 * ‖rho (elementaryRoot (0 : Fin 4) 1 (by decide) c) w - w‖ +
            2 * ‖rho (elementaryRoot (1 : Fin 4) 3 (by decide) 1) w - w‖ :=
        norm_unitary_commutator_sub_le rho _ _ w
      _ ≤ 4 * K := by
        have h1 := hrow01 c
        have h2 := hcol13 1
        linarith
  have hplane (p : G4 X) (hp : p ∈ columnPlane X) :
      ‖rho p w - w‖ ≤ 2 * K := by
    obtain ⟨c, d, rfl⟩ :=
      exists_root13_mul_root23_of_mem_columnPlane X hp
    calc
      ‖rho (elementaryRoot (1 : Fin 4) 3 (by decide) c *
          elementaryRoot (2 : Fin 4) 3 (by decide) d) w - w‖ ≤
          ‖rho (elementaryRoot (1 : Fin 4) 3 (by decide) c) w - w‖ +
            ‖rho (elementaryRoot (2 : Fin 4) 3 (by decide) d) w - w‖ :=
        norm_unitary_mul_sub_le rho _ _ w
      _ ≤ 2 * K := by
        have h1 := hcol13 c
        have h2 := hcol23 d
        linarith
  have hcolumn (g : G4 X) (hg : g ∈ N) :
      ‖rho g w - w‖ ≤ 6 * K := by
    obtain ⟨c, p, hp, rfl⟩ :=
      exists_root03_mul_plane_of_mem_columnGroup X hg
    calc
      ‖rho (elementaryRoot (0 : Fin 4) 3 (by decide) c * p) w - w‖ ≤
          ‖rho (elementaryRoot (0 : Fin 4) 3 (by decide) c) w - w‖ +
            ‖rho p w - w‖ := norm_unitary_mul_sub_le rho _ _ w
      _ ≤ 6 * K := by
        have h1 := htarget c
        have h2 := hplane p hp
        linarith
  have hwraw :=
    KazhdanFixedSpace.norm_subgroupMovingProjection_le_of_uniform_displacement
      rhoR N w (A := 6 * K) (by
        intro g hg
        change ‖rho g w - w‖ ≤ 6 * K
        exact hcolumn g hg)
  have hwProjection :
      KazhdanFixedSpace.subgroupMovingProjection rhoR N w = w := by
    let U := KazhdanFixedSpace.fixedSubspace rhoR N
    letI : CompleteSpace U :=
      (KazhdanFixedSpace.isClosed_fixedSubspace rhoR N).completeSpace_coe
    change Uᗮ.starProjection w = w
    exact Uᗮ.starProjection_eq_self_iff.mpr
      (KazhdanFixedSpace.subgroupMovingProjection_mem rhoR N (b r))
  rw [hwProjection] at hwraw
  simpa only [rhoR, N, r, w, K, B, M, mul_assoc] using hwraw

omit [Fintype X] in
/-- The column-fixed part of a quasi-cocycle value on `X₀₃` is bounded by
the defect.  The proof uses only that the target root lies in the column
subgroup and has order two. -/
theorem norm_root03_fixedProjection_le
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (rho : G4 X →* (E ≃ₗᵢ[ℂ] E)) (b : G4 X → E) (D : ℝ)
    (hb : IsQuasiCocycle rho b D) (a : R X) :
    letI : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
    ‖(KazhdanFixedSpace.fixedProjection (realifyHom rho)
        (columnGroup X)
        (b (elementaryRoot (0 : Fin 4) 3 (by decide) a)) : E)‖ ≤ D := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  let rhoR : G4 X →* (E ≃ₗᵢ[ℝ] E) := realifyHom rho
  let N : Subgroup (G4 X) := columnGroup X
  let r : G4 X := elementaryRoot (0 : Fin 4) 3 (by decide) a
  let p : E := (KazhdanFixedSpace.fixedProjection rhoR N (b r) : E)
  let q : E := (KazhdanFixedSpace.fixedProjection rhoR N (b 1) : E)
  let e : E := b (r * r) - b r - rho r (b r)
  have hrN : r ∈ N := root03_mem_columnGroup X a
  have hrr : r * r = 1 := by
    simpa only [pow_two] using root03_sq X a
  have he : ‖e‖ ≤ D := hb.2 r r
  have hpFixed : rhoR r p = p := by
    change rhoR r
      (KazhdanFixedSpace.fixedProjection rhoR N (b r) : E) =
        (KazhdanFixedSpace.fixedProjection rhoR N (b r) : E)
    exact KazhdanFixedSpace.fixedProjection_mem rhoR N (b r) ⟨r, hrN⟩
  have hprojE :
      (KazhdanFixedSpace.fixedProjection rhoR N e : E) = q - p - p := by
    have hequiv :=
      KazhdanFixedSpace.fixedProjection_equivariant_of_mem_normalizer
        rhoR N (N.le_normalizer hrN) (b r)
    dsimp only [e, q, p]
    rw [hrr]
    change ((KazhdanFixedSpace.fixedProjection rhoR N)
        (b 1 - b r - rhoR r (b r)) : E) = _
    rw [map_sub, map_sub]
    change (KazhdanFixedSpace.fixedProjection rhoR N (b 1) : E) -
        (KazhdanFixedSpace.fixedProjection rhoR N (b r) : E) -
          (KazhdanFixedSpace.fixedProjection rhoR N (rhoR r (b r)) : E) = _
    rw [hequiv, hpFixed]
  have hprojContract (x : E) :
      ‖(KazhdanFixedSpace.fixedProjection rhoR N x : E)‖ ≤ ‖x‖ := by
    let U := KazhdanFixedSpace.fixedSubspace rhoR N
    letI : CompleteSpace U :=
      (KazhdanFixedSpace.isClosed_fixedSubspace rhoR N).completeSpace_coe
    change ‖U.starProjection x‖ ≤ ‖x‖
    exact U.norm_starProjection_apply_le x
  have hPe : ‖q - p - p‖ ≤ D := by
    rw [← hprojE]
    exact (hprojContract e).trans he
  have hq : ‖q‖ ≤ D := by
    exact (hprojContract (b 1)).trans hb.norm_one_le
  have htwo : ‖p + p‖ ≤ 2 * D := by
    have hid : p + p = q - (q - p - p) := by abel
    rw [hid]
    calc
      ‖q - (q - p - p)‖ ≤ ‖q‖ + ‖q - p - p‖ := norm_sub_le _ _
      _ ≤ 2 * D := by linarith
  have hnormTwo : ‖p + p‖ = 2 * ‖p‖ := by
    rw [← two_smul ℝ p, norm_smul, Real.norm_ofNat]
  rw [hnormTwo] at htwo
  have hp0 : 0 ≤ ‖p‖ := norm_nonneg p
  change ‖p‖ ≤ D
  linarith

/-- **Rank-four relative `(TT)/T` key trick.**  Every quasi-cocycle is
uniformly bounded on `X₀₃`.  No invariant-vector hypothesis is used, so this
is stronger than the relative statement required for `(TT)/T`. -/
theorem hasRelativeTT_X03 :
    HasRelativeTT.{_, v} (G4 X) (X03 X) := by
  intro E _ _ _ rho b D hb
  let M : ℝ := embeddedControlNormSum X b
  let C : ℝ := D +
    6 * (2 * (6 * Fintype.card X + 6 : ℝ) * (2 * M + 2 * D))
  have hM : 0 ≤ M := embeddedControlNormSum_nonneg X b
  have hinner : 0 ≤ 2 * M + 2 * D := by
    have hD := hb.1
    positivity
  have hfactor : 0 ≤ (6 * Fintype.card X + 6 : ℝ) := by positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg hb.1 <|
      mul_nonneg (by norm_num) <|
        mul_nonneg (mul_nonneg (by norm_num) hfactor) hinner
  refine ⟨C, hC, ?_⟩
  intro g hg
  obtain ⟨a, rfl⟩ := hg
  letI : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  let rhoR : G4 X →* (E ≃ₗᵢ[ℝ] E) := realifyHom rho
  let N : Subgroup (G4 X) := columnGroup X
  let r : G4 X := elementaryRoot (0 : Fin 4) 3 (by decide) a
  let p : E := (KazhdanFixedSpace.fixedProjection rhoR N (b r) : E)
  let w : E := KazhdanFixedSpace.subgroupMovingProjection rhoR N (b r)
  have hfixed : ‖p‖ ≤ D := by
    simpa only [p, rhoR, N, r] using
      norm_root03_fixedProjection_le X rho b D hb a
  have hmoving :
      ‖w‖ ≤ 6 * (2 * (6 * Fintype.card X + 6 : ℝ) *
        (2 * M + 2 * D)) := by
    simpa only [w, rhoR, N, r, M] using
      norm_root03_movingProjection_le X rho b D hb a
  have hsplit : b r = p + w := by
    dsimp only [p, w]
    rw [KazhdanFixedSpace.subgroupMovingProjection_eq_sub_fixedProjection]
    abel
  change ‖b r‖ ≤ C
  rw [hsplit]
  exact (norm_add_le p w).trans <| by
    dsimp only [C]
    linarith

/-- The relative `(TT)/T` statement used in globalization is the immediate
weakening of the stronger root theorem. -/
theorem hasRelativeTTmodT_X03 :
    HasRelativeTTmodT.{_, v} (G4 X) (X03 X) :=
  (hasRelativeTT_X03 X).toRelativeTTmodT

end
end RankFourRelativeTT
end GroupApproximation
