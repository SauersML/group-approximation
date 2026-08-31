import Mathlib
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CoefficientReduction
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SphereOrientationPosFromMV

/-!
# Bockstein nonvanishing of the reduced integral top generator

This file proves the single remaining topological input for Prompt 05: the reduced
integral top generator of the sphere is nonzero
(`reducedTopGenerator_ne_zero`).

The proof is the standard Bockstein argument: the coefficient short exact sequence
`0 → ℤ --(·2)--> ℤ --(mod 2)--> ZMod 2 → 0` induces (degreewise, by exactness of
coproducts in `ModuleCat ℤ`) a short exact sequence of singular chain complexes,
whose homology long exact sequence is exact at `Hₙ(Sⁿ; ℤ)`.  Hence the kernel of
the coefficient reduction on `Hₙ` is the image of multiplication by `2`.  If the
reduced generator vanished, the integral generator would be `2 • v`, contradicting
that it maps to `1` under the orientation isomorphism.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ## The coefficient short exact sequence `0 → ℤ → ℤ → ZMod 2 → 0` -/

/-- Multiplication by `2` on `ℤ`, as a morphism of `ℤ`-modules. -/
def bk_f : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ := ModuleCat.ofHom (2 • LinearMap.id : ℤ →ₗ[ℤ] ℤ)

theorem bk_f_apply (x : ℤ) : bk_f.hom x = 2 * x := by
  show (2 • LinearMap.id) x = 2 * x; simp [two_smul]; ring

theorem bk_f_eq_two_smul : bk_f = (2 : ℤ) • 𝟙 (ModuleCat.of ℤ ℤ) := by
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun x => ?_
  rw [bk_f_apply]
  show (2 : ℤ) * x = ((2 : ℤ) • 𝟙 (ModuleCat.of ℤ ℤ)).hom x
  simp

theorem redCoeff_apply (x : ℤ) : redCoeffHom.hom x = (x : ZMod 2) := rfl

/-- The coefficient short complex `ℤ --(·2)--> ℤ --(mod 2)--> ZMod 2`. -/
def bocksteinSES : ShortComplex (ModuleCat.{0} ℤ) :=
  ShortComplex.mk bk_f redCoeffHom (by
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun x => ?_
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [redCoeff_apply, bk_f_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact ⟨x, by ring⟩)

theorem bocksteinSES_shortExact : bocksteinSES.ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    show LinearMap.range (bk_f.hom) = LinearMap.ker (redCoeffHom.hom)
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      simp only [LinearMap.mem_ker]
      rw [bk_f_apply, redCoeff_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact ⟨y, by ring⟩
    · intro x hx
      simp only [LinearMap.mem_ker] at hx
      rw [redCoeff_apply, ZMod.intCast_zmod_eq_zero_iff_dvd] at hx
      obtain ⟨k, rfl⟩ := hx
      exact ⟨(k : ℤ), by rw [bk_f_apply]; push_cast; ring⟩
  · refine (ModuleCat.mono_iff_injective bocksteinSES.f).mpr ?_
    show Function.Injective bk_f.hom
    have hfun : ⇑bk_f.hom = fun x : ℤ => 2 * x := by ext x; exact bk_f_apply x
    rw [hfun]; intro a b h; exact mul_left_cancel₀ (by norm_num) h
  · refine (ModuleCat.epi_iff_surjective bocksteinSES.g).mpr ?_
    show Function.Surjective redCoeffHom.hom
    intro y; obtain ⟨x, hx⟩ := ZMod.intCast_surjective (n := 2) y; exact ⟨x, hx⟩

/-! ## The induced short exact sequence of chain complexes -/

/-- The singular chain complex functor of a fixed space, as a functor of the
coefficient module. -/
def Fc (S : TopCat.{0}) : ModuleCat.{0} ℤ ⥤ ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (singularChainComplexFunctor (ModuleCat.{0} ℤ)).flip.obj S

instance constDiscrete_additive (J : Type) :
    (Functor.const (Discrete J) : ModuleCat.{0} ℤ ⥤ _).Additive := by
  constructor
  intro X Y f g
  ext j
  simp

instance Fc_additive (S : TopCat.{0}) : (Fc S).Additive := by
  constructor
  intro X Y f g
  apply HomologicalComplex.hom_ext
  intro k
  have key : ∀ φ : X ⟶ Y, ((Fc S).map φ).f k
      = (Fc S ⋙ HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) k).map φ :=
    fun _ => rfl
  rw [HomologicalComplex.add_f_apply, key, key, key]
  exact (inferInstanceAs ((Functor.const (Discrete _) ⋙ colim).Additive)).map_add

/-- Degreewise, `Fc S` preserves finite limits. -/
instance Fc_eval_preservesFiniteLimits (S : TopCat.{0}) (k : ℕ) :
    PreservesFiniteLimits (Fc S ⋙ HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) k) :=
  inferInstanceAs (PreservesFiniteLimits (Functor.const (Discrete _) ⋙ colim))

/-- Degreewise, `Fc S` preserves finite colimits. -/
instance Fc_eval_preservesFiniteColimits (S : TopCat.{0}) (k : ℕ) :
    PreservesFiniteColimits (Fc S ⋙ HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) k) :=
  inferInstanceAs (PreservesFiniteColimits (Functor.const (Discrete _) ⋙ colim))

/-- The short exact sequence of singular chain complexes obtained from the
coefficient sequence. -/
theorem chainSES_shortExact (S : TopCat.{0}) : (bocksteinSES.map (Fc S)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro k
  have hmap : (bocksteinSES.map (Fc S)).map (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) k)
      = bocksteinSES.map (Fc S ⋙ HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) k) := by
    rfl
  rw [hmap]
  exact bocksteinSES_shortExact.map_of_exact _

/-- Multiplication by `2` on a chain complex induces multiplication by `2` on
homology. -/
theorem homologyMap_two_smul_id (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) :
    HomologicalComplex.homologyMap ((2 : ℤ) • 𝟙 K) n
      = (2 : ℤ) • 𝟙 ((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ)
          (ComplexShape.down ℕ) n).obj K) := by
  rw [show HomologicalComplex.homologyMap ((2 : ℤ) • 𝟙 K) n
        = (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).map
            ((2 : ℤ) • 𝟙 K) from rfl,
    CategoryTheory.Functor.map_zsmul,
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).map_id]

/-! ## Nonvanishing of the reduced generator -/

theorem reducedTopGenerator_ne_zero (n : ℕ) (hn : 1 ≤ n) :
    reducedTopGenerator (sphereTopHomologyIso_unconditional n hn) ≠ 0 := by
  intro hzero
  set e := sphereTopHomologyIso_unconditional n hn with he
  set S : TopCat.{0} := TopCat.sphere.{0} n with hS
  set Sc := bocksteinSES.map (Fc S) with hSc
  have hSE : Sc.ShortExact := chainSES_shortExact S
  -- exactness of the homology sequence at degree n
  have hex := hSE.homology_exact₂ n
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hex
  set gZ := integralTopGenerator e with hgZ
  -- the reduction map equals `sphereTopHomologyReduction n` on homology
  have hg_ker : (HomologicalComplex.homologyMap Sc.g n).hom gZ = 0 := by
    show (HomologicalComplex.homologyMap Sc.g n).hom gZ = 0
    have : (HomologicalComplex.homologyMap Sc.g n) = (sphereTopHomologyReduction n) := by
      rw [sphereTopHomologyReduction, redHomology_eq_homologyMap]
      rfl
    rw [this]
    exact hzero
  -- gZ is in the range of the multiplication-by-2 map on homology
  have hmem : gZ ∈ LinearMap.range (HomologicalComplex.homologyMap Sc.f n).hom := by
    rw [hex]; exact hg_ker
  obtain ⟨v, hv⟩ := hmem
  -- the multiplication-by-2 chain map induces multiplication by 2 on homology
  have hfeq : Sc.f = (2 : ℤ) • 𝟙 Sc.X₂ := by
    have h : (Fc S).map bk_f = (2 : ℤ) • 𝟙 ((Fc S).obj (ModuleCat.of ℤ ℤ)) := by
      rw [bk_f_eq_two_smul, CategoryTheory.Functor.map_zsmul, CategoryTheory.Functor.map_id]
    exact h
  have hf2 : HomologicalComplex.homologyMap Sc.f n
      = (2 : ℤ) • 𝟙 ((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).obj Sc.X₂) := by
    rw [hfeq]; exact homologyMap_two_smul_id Sc.X₂ n
  -- apply the orientation isomorphism
  have h1 : e.hom.hom gZ = 1 := by
    rw [hgZ, integralTopGenerator, ← ModuleCat.comp_apply, e.inv_hom_id, ModuleCat.id_apply]
  have step : e.hom.hom gZ = e.hom.hom ((2 : ℤ) • v) := by
    rw [← hv, hf2]; rfl
  rw [h1, map_zsmul, smul_eq_mul] at step
  have hdvd : (2 : ℤ) ∣ 1 := ⟨e.hom.hom v, step⟩
  norm_num at hdvd

