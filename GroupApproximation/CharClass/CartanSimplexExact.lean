import GroupApproximation.CharClass.CartanSimplexContractible
import GroupApproximation.CharClass.CartanTargetBoundary
import GroupApproximation.CharClass.AcyclicModelsHomology
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CoveringTransferBoundary

/-!
# The `Finsupp` model of the mod-2 singular complex, and its exactness on models

Two descriptions of the same chain group are in play.  The repo's singular chain
complex, inherited from Mathlib, has degree-`k` carrier the **coproduct** of one
copy of `F₂` per singular simplex; the Cartan lane's differential `bdU` acts on
the **finitely supported functions** on singular simplices.  They are isomorphic,
degreewise and compatibly with the differentials, and this file says so.

The point of saying so is that the vanishing homology of a contractible space,
which lives on the coproduct side, becomes an elementary statement on the
`Finsupp` side: a positive-degree cycle for `bdU` over a standard simplex is a
boundary.  That is the exact form the acyclicity of the pair complex is built
from.

Both maps are elementary.  `toChainHom` extends `σ ↦ ι σ (1)` linearly;
`fromChainHom` is the coproduct's universal map with components `Finsupp.lsingle`.
The differentials agree because the alternating signs of the singular boundary
collapse in characteristic two, which the repo's `singular_d_ι` already records.

## Main results

* `toChainHom`, `fromChainHom` — the two directions, mutually inverse.
* `toChainHom_bdU` — the isomorphism is a chain map.
* `bdU_exists_preimage` — vanishing homology makes `bdU`-cycles into boundaries.
* `bdU_exists_preimage_stdSimplexTop` — **the acyclicity input**, on the models.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

variable (X : TopCat.{0})

/-! ## 1. The two directions -/

/-- The basis chain of a singular simplex, inside the coproduct carrier. -/
noncomputable def genChain (k : ℕ) (σ : singularSimplices X k) : (singularChainCx X).X k :=
  (Limits.Sigma.ι (fun (_ : singularSimplices X k) => transferCoeff) σ).hom (1 : ZMod 2)

/-- From finitely supported functions to the coproduct. -/
noncomputable def toChainHom (k : ℕ) :
    ModuleCat.of (ZMod 2) (singularSimplices X k →₀ ZMod 2) ⟶ (singularChainCx X).X k :=
  ModuleCat.ofHom (Finsupp.linearCombination (ZMod 2) (genChain X k))

/-- From the coproduct to finitely supported functions. -/
noncomputable def fromChainHom (k : ℕ) :
    (singularChainCx X).X k ⟶ ModuleCat.of (ZMod 2) (singularSimplices X k →₀ ZMod 2) :=
  Limits.Sigma.desc (fun σ => ModuleCat.ofHom (Finsupp.lsingle σ))

theorem ι_comp_fromChainHom (k : ℕ) (σ : singularSimplices X k) :
    Limits.Sigma.ι (fun (_ : singularSimplices X k) => transferCoeff) σ ≫ fromChainHom X k
      = ModuleCat.ofHom (Finsupp.lsingle σ) :=
  Limits.Sigma.ι_desc _ σ

theorem toChainHom_single (k : ℕ) (σ : singularSimplices X k) (c : ZMod 2) :
    (toChainHom X k).hom (Finsupp.single σ c) = c • genChain X k σ := by
  show Finsupp.linearCombination (ZMod 2) (genChain X k) (Finsupp.single σ c) = _
  rw [Finsupp.linearCombination_single]

theorem toChainHom_single_one (k : ℕ) (σ : singularSimplices X k) :
    (toChainHom X k).hom (Finsupp.single σ 1) = genChain X k σ := by
  rw [toChainHom_single, one_smul]

theorem fromChainHom_genChain (k : ℕ) (σ : singularSimplices X k) :
    (fromChainHom X k).hom (genChain X k σ) = Finsupp.single σ 1 := by
  exact congrArg (fun (m : transferCoeff ⟶
      ModuleCat.of (ZMod 2) (singularSimplices X k →₀ ZMod 2)) => m.hom (1 : ZMod 2))
    (ι_comp_fromChainHom X k σ)

/-! ## 2. The two directions are mutually inverse -/

theorem fromChainHom_toChainHom (k : ℕ) (y : singularSimplices X k →₀ ZMod 2) :
    (fromChainHom X k).hom ((toChainHom X k).hom y) = y := by
  induction y using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, hu, hv]
  | single σ c =>
      rw [toChainHom_single, map_smul, fromChainHom_genChain, Finsupp.smul_single,
        smul_eq_mul, mul_one]

theorem toChainHom_injective (k : ℕ) : Function.Injective (toChainHom X k).hom := by
  intro a b h
  have := congrArg (fromChainHom X k).hom h
  rwa [fromChainHom_toChainHom, fromChainHom_toChainHom] at this

theorem fromChainHom_comp_toChainHom (k : ℕ) :
    fromChainHom X k ≫ toChainHom X k = 𝟙 ((singularChainCx X).X k) := by
  apply Limits.Sigma.hom_ext
  intro σ
  have key : (Limits.Sigma.ι (fun (_ : singularSimplices X k) => transferCoeff) σ
        ≫ fromChainHom X k) ≫ toChainHom X k
      = Limits.Sigma.ι (fun (_ : singularSimplices X k) => transferCoeff) σ := by
    rw [ι_comp_fromChainHom]
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    show (toChainHom X k).hom (Finsupp.single σ (1 : ZMod 2)) = genChain X k σ
    rw [toChainHom_single_one]
  exact (Category.assoc _ _ _).symm.trans (key.trans (Category.comp_id _).symm)

theorem toChainHom_fromChainHom (k : ℕ) (z : (singularChainCx X).X k) :
    (toChainHom X k).hom ((fromChainHom X k).hom z) = z :=
  congrArg (fun (m : (singularChainCx X).X k ⟶ (singularChainCx X).X k) => m.hom z)
    (fromChainHom_comp_toChainHom X k)

/-! ## 3. The isomorphism is a chain map -/

theorem d_genChain (k : ℕ) (σ : singularSimplices X (k + 1)) :
    ((singularChainCx X).d (k + 1) k).hom (genChain X (k + 1) σ)
      = ∑ i : Fin (k + 2), genChain X k (faceSimplex X k i σ) := by
  have hL : ((singularChainCx X).d (k + 1) k).hom (genChain X (k + 1) σ)
      = (Limits.Sigma.ι (fun (_ : singularSimplices X (k + 1)) => transferCoeff) σ
          ≫ (singularChainCx X).d (k + 1) k).hom (1 : ZMod 2) := rfl
  have hR : (∑ i : Fin (k + 2),
        Limits.Sigma.ι (fun (_ : singularSimplices X k) => transferCoeff)
          (faceSimplex X k i σ)).hom (1 : ZMod 2)
      = ∑ i : Fin (k + 2), genChain X k (faceSimplex X k i σ) := by
    rw [ModuleCat.hom_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => rfl
  rw [hL, singular_d_ι]
  exact hR

theorem toChainHom_bdU (k : ℕ) (y : singularSimplices X (k + 1) →₀ ZMod 2) :
    (toChainHom X k).hom (bdU (ZMod 2) X k y)
      = ((singularChainCx X).d (k + 1) k).hom ((toChainHom X (k + 1)).hom y) := by
  have hgen : ∀ σ : singularSimplices X (k + 1),
      (toChainHom X k).hom (bdU (ZMod 2) X k (Finsupp.single σ 1))
        = ((singularChainCx X).d (k + 1) k).hom
            ((toChainHom X (k + 1)).hom (Finsupp.single σ 1)) := by
    intro σ
    rw [bdU_single, toChainHom_single_one, d_genChain, map_sum]
    exact Finset.sum_congr rfl fun i _ => toChainHom_single_one X k _
  induction y using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add u v hu hv =>
      simp only [map_add]
      rw [hu, hv]
  | single σ c =>
      have hsc : (Finsupp.single σ c : singularSimplices X (k + 1) →₀ ZMod 2)
          = c • Finsupp.single σ (1 : ZMod 2) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hsc, map_smul, map_smul, map_smul, map_smul, hgen σ]

/-! ## 4. Cycles are boundaries -/

/-- Vanishing homology of the singular complex makes positive-degree `bdU`-cycles
into boundaries. -/
theorem bdU_exists_preimage (k : ℕ)
    (h : Limits.IsZero ((singularChainCx X).homology (k + 1)))
    (y : singularSimplices X (k + 1) →₀ ZMod 2)
    (hy : bdU (ZMod 2) X k y = 0) :
    ∃ z : singularSimplices X (k + 2) →₀ ZMod 2, bdU (ZMod 2) X (k + 1) z = y := by
  have hcy : ((singularChainCx X).d (k + 1) k).hom ((toChainHom X (k + 1)).hom y) = 0 := by
    rw [← toChainHom_bdU, hy, map_zero]
  obtain ⟨z', hz'⟩ :=
    exists_preimage_of_isZero_homology (singularChainCx X) k h _ hcy
  refine ⟨(fromChainHom X (k + 2)).hom z', ?_⟩
  apply toChainHom_injective X (k + 1)
  rw [toChainHom_bdU, toChainHom_fromChainHom, hz']

/-- **The acyclicity input.**  Over a standard simplex every positive-degree
`bdU`-cycle is a boundary. -/
theorem bdU_exists_preimage_stdSimplexTop (n k : ℕ)
    (y : singularSimplices (stdSimplexTop n) (k + 1) →₀ ZMod 2)
    (hy : bdU (ZMod 2) (stdSimplexTop n) k y = 0) :
    ∃ z : singularSimplices (stdSimplexTop n) (k + 2) →₀ ZMod 2,
      bdU (ZMod 2) (stdSimplexTop n) (k + 1) z = y := by
  have h : Limits.IsZero ((singularChainCx (stdSimplexTop n)).homology (k + 1)) :=
    homZMod2_isZero_stdSimplexTop n (k + 1) (Nat.succ_ne_zero k)
  exact bdU_exists_preimage (stdSimplexTop n) k h y hy

end

end GroupApproximation.CharClass
