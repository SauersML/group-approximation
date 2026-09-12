import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SphereHomologyMVStep
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.KroneckerNaturality
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.InducedOnRPCohomology
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SubChainSubspaceBridge
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.MayerVietoris
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SingularH0General
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SphereHomologyS1BaseMV
import GroupApproximation.Meta.AxiomGuard
import Mathlib

/-!
# Intermediate mod-two homology and cohomology of spheres vanish

This file proves the classical intermediate-degree vanishing of the mod-two
singular homology (and, via the universal coefficient isomorphism over `F₂`, the
mod-two singular cohomology) of the sphere:

```text
H_k(Sⁿ; F₂) = 0     and     Hᵏ(Sⁿ; F₂) = 0      for 0 < k < n.
```

This is the one topological input feeding the injectivity of the Smith/Gysin
connecting map `rpGysinConnecting n k` in degrees `1 ≤ k < n`, which in turn
drives the unconditional α-power nonvanishing for `RPⁿ`.

The proof is the standard Mayer–Vietoris suspension computation, carried out over
the field `F₂` using the project's general-coefficient MV machinery
(`mvHomologyIso_succ`), the coefficient-`Mod` chain homotopy
(`singularChainHomotopyOfHomotopyModule`), and the equatorial-band homotopy
equivalence `sphereBandHomotopyEquiv`.
-/

noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

open AffineBarycentricSubdivision

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-! ## General-coefficient homology homotopy invariance -/

/-
Homotopic `TopCat` maps induce equal maps on the `k`-th homology of the
singular chain complex with coefficients in an arbitrary module `Mod`.
-/
theorem homologyMap_eq_of_homotopic_module (R : Type) [CommRing R] (Mod : ModuleCat.{0} R)
    {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : ContinuousMap.Homotopy f.hom g.hom) (k : ℕ) :
    HomologicalComplex.homologyMap
        (((singularChainComplexFunctor (ModuleCat.{0} R)).obj Mod).map f) k
      = HomologicalComplex.homologyMap
        (((singularChainComplexFunctor (ModuleCat.{0} R)).obj Mod).map g) k :=
  ((show TopCat.Homotopy f g from H).singularChainComplexFunctorObjMap Mod).homologyMap_eq k

/-
Homology iso from a homotopy equivalence of spaces, over general coefficients
`Mod`.
-/
def homologyIsoOfHomotopyEquivModule (R : Type) [CommRing R] (Mod : ModuleCat.{0} R) (k : ℕ)
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj Mod).obj (TopCat.of X)).homology k ≅
      (((singularChainComplexFunctor (ModuleCat.{0} R)).obj Mod).obj (TopCat.of Y)).homology k where
  hom := HomologicalComplex.homologyMap
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj Mod).map (TopCat.ofHom e.toFun)) k
  inv := HomologicalComplex.homologyMap
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj Mod).map (TopCat.ofHom e.invFun)) k
  hom_inv_id := by
    rw [← HomologicalComplex.homologyMap_comp, ← Functor.map_comp,
      show TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun
        = TopCat.ofHom (e.invFun.comp e.toFun) from rfl,
      homologyMap_eq_of_homotopic_module R Mod
        (f := TopCat.ofHom (e.invFun.comp e.toFun)) (g := 𝟙 (TopCat.of X))
        (e.left_inv.some) k]
    simp
  inv_hom_id := by
    rw [← HomologicalComplex.homologyMap_comp, ← Functor.map_comp,
      show TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun
        = TopCat.ofHom (e.toFun.comp e.invFun) from rfl,
      homologyMap_eq_of_homotopic_module R Mod
        (f := TopCat.ofHom (e.toFun.comp e.invFun)) (g := 𝟙 (TopCat.of Y))
        (e.right_inv.some) k]
    simp

/-! ## Contractible spaces have vanishing positive mod-two subchain homology -/

/-
**Vanishing of positive mod-two homology for contractible subspaces.** If
`S ⊆ X` is contractible and `m ≥ 1`, then `H_m(S; F₂) = 0` in subchain form.
-/
theorem isZero_subChainComplex_homologyZMod2_of_contractible
    (X : TopCat.{0}) (S : Set X) [ContractibleSpace S] (m : ℕ) (hm : 1 ≤ m) :
    IsZero ((subChainComplex (ZMod 2) X S).homology m) := by
  obtain ⟨ e ⟩ := ‹ContractibleSpace S›;
  obtain ⟨ e ⟩ := e;
  have hUnit :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat (ZMod 2)) m (ModuleCat.of (ZMod 2) (ZMod 2)) (TopCat.of Unit) (by omega)
  change IsZero (homologyZMod2 (TopCat.of Unit) m) at hUnit
  exact IsZero.of_iso hUnit
    (subspaceHomologyIso S m ≪≫ homologyIsoOfHomotopyEquivModule
      (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)) m e)

/-! ## The mod-two suspension isomorphism -/

/-- **Mod-two suspension isomorphism (positive degrees).** For `j ≥ 1`,
`H_{j+1}(Sⁿ⁺¹; F₂) ≅ H_j(Sⁿ; F₂)`. -/
def sphereModTwoSuspension (n j : ℕ) (hj : 1 ≤ j) :
    homologyZMod2 (TopCat.of (Sphere (n + 1))) (j + 1)
      ≅ homologyZMod2 (TopCat.of (Sphere n)) j :=
  (mvHomologyIso_succ (ZMod 2) (upperOpens n) (lowerOpens n) (upperOpens_sup_lowerOpens n) j
      (isZero_subChainComplex_homologyZMod2_of_contractible _ _ (j + 1) (by omega))
      (isZero_subChainComplex_homologyZMod2_of_contractible _ _ (j + 1) (by omega))
      (isZero_subChainComplex_homologyZMod2_of_contractible _ _ j hj)
      (isZero_subChainComplex_homologyZMod2_of_contractible _ _ j hj))
    ≪≫ subspaceHomologyIso _ j
    ≪≫ homologyIsoOfHomotopyEquivModule (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)) j
        (sphereBandHomotopyEquiv n)

/-! ## The intermediate vanishing -/

/-- The Mayer–Vietoris left map on `H₀` of the sphere cover, over `F₂`:
`H₀(U ∩ V) → H₀(U) ⊕ H₀(V)`. -/
abbrev mvF0 (m : ℕ) :
    (subChainComplex (ZMod 2) (sphereSpace m)
        ((upperOpens m : Set (sphereSpace m))
          ∩ (lowerOpens m : Set (sphereSpace m)))).homology 0 ⟶
      ((mvShortComplex (ZMod 2) (upperOpens m) (lowerOpens m)
          (upperOpens_sup_lowerOpens m)).X₂).homology 0 :=
  HomologicalComplex.homologyMap
    (mvShortComplex (ZMod 2) (upperOpens m) (lowerOpens m) (upperOpens_sup_lowerOpens m)).f 0

/-
The equatorial band is nonempty.
-/
theorem sphereBand_nonempty (m : ℕ) :
    Nonempty ↥((upperOpens m : Set (sphereSpace m))
      ∩ (lowerOpens m : Set (sphereSpace m))) := by
  -- The equatorial band is nonempty because it contains the equator.
  have h_eq : Nonempty (Sphere m) := by
    exact ⟨ EuclideanSpace.single 0 1, by simp +decide ⟩
  change Nonempty ↥(sphereBand m)
  exact h_eq.map (fun x : Sphere m => (sphereBandHomotopyEquiv m).invFun x)

/-
The equatorial band of `Sⁿ⁺¹` is path-connected for `n ≥ 1` (it is homotopy
equivalent to `Sⁿ`, which is path-connected).
-/
theorem sphereBand_pathConnected (m : ℕ) (hm : 1 ≤ m) :
    PathConnectedSpace ↥((upperOpens m : Set (sphereSpace m))
      ∩ (lowerOpens m : Set (sphereSpace m))) := by
  obtain ⟨ e ⟩ := sphereBandHomotopyEquiv m;
  rename_i f hf₁ hf₂;
  have h_path_connected : ∀ x y : ↥(sphereBand m), ∃ p : Path x y, True := by
    intro x y
    obtain ⟨p, hp⟩ : ∃ p : Path (e x) (e y), True := by
      have h_path_connected : PathConnectedSpace (Sphere m) := by
        have h_path_connected : IsPathConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) := by
          apply_rules [ isPathConnected_sphere ];
          · rw [ ← Module.finrank_eq_rank ];
            norm_num;
            exact hm;
          · norm_num;
        convert h_path_connected;
        rw [ isPathConnected_iff_pathConnectedSpace ];
      exact ⟨ PathConnectedSpace.somePath ( e x ) ( e y ), trivial ⟩;
    obtain ⟨H, hH⟩ : ∃ H : ContinuousMap.Homotopy (f.comp e) (ContinuousMap.id (↥(sphereBand m))), True := by
      exact ⟨ hf₁.some, trivial ⟩;
    -- Compose the paths from x to f(e(x)), f(e(x)) to f(e(y)), and f(e(y)) to y.
    use Path.trans (Path.trans (H.evalAt x).symm (Path.map p (f.continuous)) ) (H.evalAt y);
  constructor;
  · convert sphereBand_nonempty m;
  · exact fun x y => by obtain ⟨ p, hp ⟩ := h_path_connected x y; exact ⟨ p ⟩ ;

/-
**Injectivity of the Mayer–Vietoris `H₀` map** for `n ≥ 1`: since the band
`U ∩ V` and the hemispheres `U`, `V` are all path-connected, `H₀(U∩V) → H₀(U)⊕H₀(V)`
is injective.
-/
theorem mvF0_injective (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (mvF0 m).hom := by
  let projU := HomologicalComplex.homologyMap
    (biprod.fst :
      (subChainComplex (ZMod 2) (sphereSpace m) (upperOpens m) ⊞
        subChainComplex (ZMod 2) (sphereSpace m) (lowerOpens m)) ⟶ _) 0
  let inclU := HomologicalComplex.homologyMap
    (mvInclUV_U (ZMod 2) (upperOpens m) (lowerOpens m)) 0
  have h_mvF0 : mvF0 m ≫ projU = inclU := by
    have hchain :
        (mvShortComplex (ZMod 2) (upperOpens m) (lowerOpens m)
            (upperOpens_sup_lowerOpens m)).f ≫
            (biprod.fst :
              (subChainComplex (ZMod 2) (sphereSpace m) (upperOpens m) ⊞
                subChainComplex (ZMod 2) (sphereSpace m) (lowerOpens m)) ⟶ _)
          = mvInclUV_U (ZMod 2) (upperOpens m) (lowerOpens m) :=
      biprod.lift_fst _ _
    have := congrArg (fun f => HomologicalComplex.homologyMap f 0) hchain
    simpa only [mvF0, projU, inclU, HomologicalComplex.homologyMap_comp] using this
  have h_mvInclUV_U : inclU ≫
      H0Gen.subH0aug (ZMod 2) (sphereSpace m) (upperOpens m : Set (sphereSpace m)) =
      H0Gen.subH0aug (ZMod 2) (sphereSpace m)
        ((upperOpens m : Set (sphereSpace m)) ∩ (lowerOpens m : Set (sphereSpace m))) := by
    simpa only [inclU, mvInclUV_U] using
      H0Gen.subH0aug_natural_inclusion (R := ZMod 2) (sphereSpace m)
        ((upperOpens m : Set (sphereSpace m)) ∩ (lowerOpens m : Set (sphereSpace m)))
        (upperOpens m : Set (sphereSpace m)) Set.inter_subset_left
  haveI : PathConnectedSpace
      ↥((upperOpens m : Set (sphereSpace m)) ∩ (lowerOpens m : Set (sphereSpace m))) :=
    sphereBand_pathConnected m hm
  have h_aug_inj : Function.Injective
      (H0Gen.subH0aug (ZMod 2) (sphereSpace m)
        ((upperOpens m : Set (sphereSpace m)) ∩ (lowerOpens m : Set (sphereSpace m)))).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  intro x y hxy
  apply h_aug_inj
  have hproj : projU.hom ((mvF0 m).hom x) = projU.hom ((mvF0 m).hom y) :=
    congrArg projU.hom hxy
  have hincl : inclU.hom x = inclU.hom y := by
    have hx := congrArg (fun f => f.hom x) h_mvF0
    have hy := congrArg (fun f => f.hom y) h_mvF0
    simp only [CategoryTheory.comp_apply] at hx hy
    exact hx.symm.trans (hproj.trans hy)
  have hupper := congrArg
    (H0Gen.subH0aug (ZMod 2) (sphereSpace m)
      (upperOpens m : Set (sphereSpace m))).hom hincl
  have hx := congrArg (fun f => f.hom x) h_mvInclUV_U
  have hy := congrArg (fun f => f.hom y) h_mvInclUV_U
  simp only [CategoryTheory.comp_apply] at hx hy
  exact hx.symm.trans (hupper.trans hy)

/-
The small-chains `H₁` of the sphere cover vanishes for `n ≥ 1`: the connecting
map `δ : H₁(X₃) → H₀(X₁)` is injective (as `H₁(X₂) = 0`) and has trivial range
(its range is `ker(mvF0)`, and `mvF0` is injective), hence its source is zero.
-/
theorem mvX3_H1_isZero (m : ℕ) (hm : 1 ≤ m) :
    IsZero ((mvShortComplex (ZMod 2) (upperOpens m) (lowerOpens m)
        (upperOpens_sup_lowerOpens m)).X₃.homology 1) := by
  let S := mvShortComplex (ZMod 2) (upperOpens m) (lowerOpens m)
    (upperOpens_sup_lowerOpens m)
  let hS := mvShortExact (ZMod 2) (upperOpens m) (lowerOpens m)
    (upperOpens_sup_lowerOpens m)
  let δ := hS.δ 1 0 rfl
  have hX2 : IsZero (S.X₂.homology 1) :=
    isZero_mvX₂_homology (ZMod 2) (upperOpens m) (lowerOpens m)
      (upperOpens_sup_lowerOpens m) 1
      (isZero_subChainComplex_homologyZMod2_of_contractible (sphereSpace m)
        (upperOpens m : Set (sphereSpace m)) 1 (by norm_num))
      (isZero_subChainComplex_homologyZMod2_of_contractible (sphereSpace m)
        (lowerOpens m : Set (sphereSpace m)) 1 (by norm_num))
  haveI : Mono δ := hS.homology_exact₃ 1 0 rfl |>.mono_g (hX2.eq_of_src _ _)
  have hδ_inj : Function.Injective δ.hom := (ModuleCat.mono_iff_injective _).mp inferInstance
  have hzero : ∀ x : S.X₃.homology 1, x = 0 := by
    intro x
    apply hδ_inj
    rw [map_zero]
    apply mvF0_injective m hm
    have hmem : δ.hom x ∈ LinearMap.ker (mvF0 m).hom := by
      rw [← hS.homology_exact₁ 1 0 rfl |>.moduleCat_range_eq_ker]
      exact LinearMap.mem_range_self δ.hom x
    exact (LinearMap.mem_ker.mp hmem).trans (map_zero (mvF0 m).hom).symm
  rw [ModuleCat.isZero_iff_subsingleton]
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

/-- **Mod-two `H₁` of high-dimensional spheres vanishes.** For `n ≥ 2`,
`H₁(Sⁿ; F₂) = 0`. -/
theorem sphereModTwoH1_isZero (n : ℕ) (hn : 2 ≤ n) :
    IsZero (homologyZMod2 (TopCat.of (Sphere n)) 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  refine IsZero.of_iso (mvX3_H1_isZero m hm) ?_
  exact (smallChains_homologyIso (ZMod 2) (TopCat.of (Sphere (m + 1)))
    (twoSetCover (upperOpens m) (lowerOpens m) (upperOpens_sup_lowerOpens m)) 1).symm

/-- **Intermediate mod-two sphere homology vanishes.** For `0 < k < n`,
`H_k(Sⁿ; F₂) = 0`. -/
theorem sphereModTwoHomology_isZero_of_lt (n k : ℕ) (h0 : 0 < k) (hkn : k < n) :
    IsZero (homologyZMod2 (TopCat.of (Sphere n)) k) := by
  induction n generalizing k with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have hk1 : k = 1 := by omega
      subst hk1
      exact sphereModTwoH1_isZero (m + 1) (by omega)
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      exact IsZero.of_iso (ih j (by omega) (by omega)) (sphereModTwoSuspension m j (by omega))

/-! ## Intermediate mod-two sphere cohomology vanishes -/

/-
**Intermediate mod-two sphere cohomology vanishes.** For `0 < k < n`,
`Hᵏ(Sⁿ; F₂) = 0`. This is obtained from the homology vanishing above via the
universal coefficient isomorphism over `F₂` (`kroneckerEquiv`): the cohomology is
isomorphic to the `F₂`-linear dual of the homology, which is zero when the
homology is zero.
-/
theorem sphereCohomology_isZero_of_lt (n k : ℕ) (h0 : 0 < k) (hkn : k < n) :
    IsZero (sphereCohomology n k) := by
  have h_dual : IsZero (homologyDualZMod2 (TopCat.of (Sphere n)) k) := by
    have h_dual : IsZero (homologyZMod2 (TopCat.of (Sphere n)) k) := by
      convert sphereModTwoHomology_isZero_of_lt n k h0 hkn using 1;
    rw [ ModuleCat.isZero_iff_subsingleton ] at *;
    exact Subsingleton.intro fun x y => by ext; simp +decide [ show x = 0 from LinearMap.ext fun _ => by simp +decide [ show ( ‹_› : homologyZMod2 _ _ ) = 0 from Subsingleton.elim _ _ ], show y = 0 from LinearMap.ext fun _ => by simp +decide [ show ( ‹_› : homologyZMod2 _ _ ) = 0 from Subsingleton.elim _ _ ] ] ;
  exact IsZero.of_iso h_dual ( kroneckerEquiv ( TopCat.of ( Sphere n ) ) k )

/-- Closed audit endpoint for intermediate mod-two sphere (co)homology vanishing. -/
theorem sphereModTwo_intermediate_vanishing_closed :
    (∀ n k : ℕ, 0 < k → k < n →
      IsZero (homologyZMod2 (TopCat.of (Sphere n)) k)) ∧
    (∀ n k : ℕ, 0 < k → k < n → IsZero (sphereCohomology n k)) :=
  ⟨sphereModTwoHomology_isZero_of_lt, sphereCohomology_isZero_of_lt⟩

#audit_closed_axioms sphereModTwo_intermediate_vanishing_closed

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
