import GroupApproximation.CharClass.CartanSingularFreeCx
import GroupApproximation.CharClass.CartanTargetFunctorial
import GroupApproximation.CharClass.AcyclicModels

/-!
# The target of the Cartan comparison, as a functor into complexes over `Λ`

Everything the acyclic-models theorem asks of the target is now available, so
this file assembles it: `X ↦ S(X) ⊗ S(X)`, with `cc-steenrod`'s differential,
the group ring acting through the factor swap, as a functor
`TopCat ⥤ ChainComplex (ModuleCat Λ) ℕ`, together with its acyclicity on the
standard simplices.

Nothing new is proved here.  The differential is `Λ`-linear by
`CartanTargetEquivariance.lean`, it squares to zero and is acyclic on the models
by `CartanSingularFreeCx.lean`, and the pushforward is a `Λ`-linear chain map by
`CartanTargetFunctorial.lean`.

## Main results

* `tgtCx` — the pair complex of one space, over the group ring.
* `tgt` — **the target functor.**
* `tgt_acyclicOnModels` — **the acyclicity hypothesis of the comparison.**
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

/-! ## 1. The differential over the group ring -/

/-- `cc-steenrod`'s pair differential, as a map of modules over the group ring. -/
noncomputable def dTgtLambda (X : TopCat.{0}) (k : ℕ) :
    (Steenrod.PairIdx X (k + 1) →₀ ZMod 2) →ₗ[GroupRingZ2]
      (Steenrod.PairIdx X k →₀ ZMod 2) where
  toFun := Steenrod.dTgt X (ZMod 2) k
  map_add' u v := map_add _ u v
  map_smul' c y := dTgt_smul_tgtModule X k c y

/-- The pair complex of one space, over the group ring. -/
noncomputable def tgtCx (X : TopCat.{0}) : ChainComplex (ModuleCat.{0} GroupRingZ2) ℕ :=
  ChainComplex.of (fun k => ModuleCat.of GroupRingZ2 (Steenrod.PairIdx X k →₀ ZMod 2))
    (fun k => ModuleCat.ofHom (dTgtLambda X k))
    (fun k => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      exact dTgt_dTgt X k y)

theorem tgtCx_d (X : TopCat.{0}) (k : ℕ) :
    (tgtCx X).d (k + 1) k = ModuleCat.ofHom (dTgtLambda X k) := by
  simp [tgtCx]

/-- The differential of `tgtCx`, applied to an element: `cc-steenrod`'s `dTgt`. -/
theorem tgtCx_d_apply (X : TopCat.{0}) (k : ℕ)
    (y : Steenrod.PairIdx X (k + 1) →₀ ZMod 2) :
    ((tgtCx X).d (k + 1) k).hom y = Steenrod.dTgt X (ZMod 2) k y := by
  rw [tgtCx_d]
  rfl

/-! ## 2. Functoriality -/

theorem pairMapF2_id (X : TopCat.{0}) (k : ℕ) (y : Steenrod.PairIdx X k →₀ ZMod 2) :
    pairMapF2 (𝟙 X) k y = y := by
  induction y using Finsupp.induction_linear with
  | zero => rw [map_zero]
  | add u v hu hv => rw [map_add, hu, hv]
  | single q c => rw [pairMapF2_single, pairIdxMap_id]

theorem pairMapF2_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (k : ℕ)
    (y : Steenrod.PairIdx X k →₀ ZMod 2) :
    pairMapF2 (f ≫ g) k y = pairMapF2 g k (pairMapF2 f k y) := by
  induction y using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
  | single q c =>
      rw [pairMapF2_single, pairMapF2_single, pairMapF2_single, pairIdxMap_comp]

/-- The pushforward, as a map of complexes. -/
noncomputable def tgtMap {X Y : TopCat.{0}} (f : X ⟶ Y) : tgtCx X ⟶ tgtCx Y where
  f k := ModuleCat.ofHom (pairMapLambda f k)
  comm' i j hij := by
    have hij' : j + 1 = i := hij
    subst hij'
    rw [tgtCx_d, tgtCx_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    exact dTgt_pairMap f j y

/-- **The target of the Cartan comparison**, as a functor into complexes over the
group ring. -/
noncomputable def tgt : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} GroupRingZ2) ℕ where
  obj X := tgtCx X
  map f := tgtMap f
  map_id X := by
    refine HomologicalComplex.hom_ext _ _ fun k => ?_
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    exact pairMapF2_id X k y
  map_comp f g := by
    refine HomologicalComplex.hom_ext _ _ fun k => ?_
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    exact pairMapF2_comp f g k y

@[simp] theorem tgt_obj (X : TopCat.{0}) : tgt.obj X = tgtCx X := rfl

@[simp] theorem tgt_map {X Y : TopCat.{0}} (f : X ⟶ Y) : tgt.map f = tgtMap f := rfl

/-! ## 3. Acyclicity on the models -/

/-- **The target is acyclic on the models.**  This is the hypothesis the
acyclic-models theorem consumes. -/
theorem tgt_acyclicOnModels : AcyclicOnModels stdSimplexTop GroupRingZ2 tgt where
  exists_preimage n k y hy := by
    have hy' : Steenrod.dTgt (stdSimplexTop n) (ZMod 2) k y = 0 :=
      (tgtCx_d_apply (stdSimplexTop n) k y).symm.trans hy
    obtain ⟨z, hz⟩ := dTgt_exists_preimage_stdSimplexTop n k y hy'
    exact ⟨z, (tgtCx_d_apply (stdSimplexTop n) (k + 1) z).trans hz⟩

end

end GroupApproximation.CharClass
