import GroupApproximation.CharClass.CartanFreeCxHom
import GroupApproximation.CharClass.CartanTargetComplex

/-!
# The fourfold object `S(X)^{⊗4}` of the internal Cartan comparison

The lead's internal route compares two natural equivariant chain maps out of
`W ⊗ S(X)` into `S(X)^{⊗4}` on **one** space.  This file builds that target: the
tensor square of the pair complex, with the block swap acting, as a functor into
complexes over the group ring, together with its acyclicity on the models.

Nothing is proved here that was not proved in general.  Presenting the fourfold
as the tensor of the pair with itself, rather than as a complex indexed by
four-tuples of degrees, is what makes that possible: the contraction, the swap
and the differential all come from the general theorems applied a second time.

It is also what makes the `(13)(24)` action automatic.  The block swap of
`A ⊗ A` exchanges blocks; with `A` the pair complex, that is exactly the
permutation exchanging the first two of the four factors with the last two.

## Main results

* `pairFreeCx`, `fourFreeCx` — the pair and fourfold complexes.
* `fourCx`, `four` — the fourfold as a complex and as a functor over `Λ`.
* `four_acyclicOnModels` — **the acyclicity hypothesis for the comparison.**
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

/-! ## 1. Chain maps, packaged -/

theorem FreeCxHom.ext {A B : FreeCx} {φ ψ : FreeCxHom A B} (h : φ.f = ψ.f) : φ = ψ := by
  cases φ
  cases ψ
  subst h
  rfl

/-- The tensor product of two chain maps, as a chain map. -/
noncomputable def tenFreeCxHom {A A' B B' : FreeCx} (φ : FreeCxHom A B)
    (ψ : FreeCxHom A' B') : FreeCxHom (tensorFreeCx A A') (tensorFreeCx B B') where
  f k := tenHom φ ψ k
  comm k u := tenHom_tensorD φ ψ k u

/-! ## 2. The pair and fourfold complexes -/

/-- The pair complex `S(X) ⊗ S(X)`. -/
noncomputable abbrev pairFreeCx (X : TopCat.{0}) : FreeCx :=
  tensorFreeCx (singFreeCx X) (singFreeCx X)

/-- The fourfold complex `S(X)^{⊗4}`, as the tensor square of the pair. -/
noncomputable abbrev fourFreeCx (X : TopCat.{0}) : FreeCx :=
  tensorFreeCx (pairFreeCx X) (pairFreeCx X)

/-- An augmented contraction of the pair complex of a model. -/
noncomputable def pairAug (n : ℕ) : AugContraction (pairFreeCx (stdSimplexTop n)) :=
  tensorAug (singAug n) (singAug n)

/-- An augmented contraction of the fourfold complex of a model. -/
noncomputable def fourAug (n : ℕ) : AugContraction (fourFreeCx (stdSimplexTop n)) :=
  tensorAug (pairAug n) (pairAug n)

/-! ## 3. The pushforward -/

/-- The pushforward of singular chains, as a chain map. -/
noncomputable def singHom {X Y : TopCat.{0}} (f : X ⟶ Y) :
    FreeCxHom (singFreeCx X) (singFreeCx Y) where
  f k := Finsupp.lmapDomain (ZMod 2) (ZMod 2) (pushSimplex f k)
  comm k u := (bdU_natural (ZMod 2) f k u).symm

theorem singHom_id (X : TopCat.{0}) : singHom (𝟙 X) = FreeCxHom.id (singFreeCx X) := by
  refine FreeCxHom.ext (funext fun k => ?_)
  apply LinearMap.ext
  intro u
  show Finsupp.mapDomain (pushSimplex (𝟙 X) k) u = u
  rw [show (pushSimplex (𝟙 X) k) = id from funext fun σ => pushSimplex_id X k σ,
    Finsupp.mapDomain_id]

theorem singHom_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    singHom (f ≫ g) = (singHom g).comp (singHom f) := by
  refine FreeCxHom.ext (funext fun k => ?_)
  apply LinearMap.ext
  intro u
  show Finsupp.mapDomain (pushSimplex (f ≫ g) k) u
    = Finsupp.mapDomain (pushSimplex g k) (Finsupp.mapDomain (pushSimplex f k) u)
  rw [← Finsupp.mapDomain_comp]
  exact congrArg (fun h => Finsupp.mapDomain h u)
    (funext fun σ => pushSimplex_comp f g k σ)

/-- The pushforward on the pair complex. -/
noncomputable def pairHom {X Y : TopCat.{0}} (f : X ⟶ Y) :
    FreeCxHom (pairFreeCx X) (pairFreeCx Y) :=
  tenFreeCxHom (singHom f) (singHom f)

/-- The pushforward on the fourfold complex. -/
noncomputable def fourHom {X Y : TopCat.{0}} (f : X ⟶ Y) :
    FreeCxHom (fourFreeCx X) (fourFreeCx Y) :=
  tenFreeCxHom (pairHom f) (pairHom f)

/-! ## 4. The group ring acts by the block swap -/

/-- **The block swap makes the fourfold a module over the group ring.**  On the
four underlying factors this is the permutation `(13)(24)`. -/
noncomputable instance fourModule (X : TopCat.{0}) (k : ℕ) :
    Module GroupRingZ2 (TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) :=
  moduleOfInvolution (tenSwap (pairFreeCx X) k) (tenSwap_mul_self (pairFreeCx X) k)

theorem fourD_smul (X : TopCat.{0}) (k : ℕ) (c : GroupRingZ2)
    (y : TensorIdx (pairFreeCx X) (pairFreeCx X) (k + 1) →₀ ZMod 2) :
    tensorD (pairFreeCx X) (pairFreeCx X) k (c • y)
      = c • tensorD (pairFreeCx X) (pairFreeCx X) k y :=
  galAlgHom_comm (tenSwap (pairFreeCx X) (k + 1)) (tenSwap_mul_self (pairFreeCx X) (k + 1))
    (tenSwap (pairFreeCx X) k) (tenSwap_mul_self (pairFreeCx X) k)
    (tensorD (pairFreeCx X) (pairFreeCx X) k) (tensorD_tenSwap (pairFreeCx X) k) c y

theorem fourHom_smul {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ) (c : GroupRingZ2)
    (y : TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) :
    (fourHom f).f k (c • y) = c • (fourHom f).f k y :=
  galAlgHom_comm (tenSwap (pairFreeCx X) k) (tenSwap_mul_self (pairFreeCx X) k)
    (tenSwap (pairFreeCx Y) k) (tenSwap_mul_self (pairFreeCx Y) k)
    (tenHom (pairHom f) (pairHom f) k) (tenHom_tenSwap (pairHom f) k) c y

/-! ## 5. The fourfold as a functor over the group ring -/

/-- The fourfold differential, as a map of modules over the group ring. -/
noncomputable def fourDLambda (X : TopCat.{0}) (k : ℕ) :
    (TensorIdx (pairFreeCx X) (pairFreeCx X) (k + 1) →₀ ZMod 2) →ₗ[GroupRingZ2]
      (TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) where
  toFun := tensorD (pairFreeCx X) (pairFreeCx X) k
  map_add' u v := map_add _ u v
  map_smul' c y := fourD_smul X k c y

/-- The fourfold complex of one space, over the group ring. -/
noncomputable def fourCx (X : TopCat.{0}) : ChainComplex (ModuleCat.{0} GroupRingZ2) ℕ :=
  ChainComplex.of
    (fun k => ModuleCat.of GroupRingZ2 (TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2))
    (fun k => ModuleCat.ofHom (fourDLambda X k))
    (fun k => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      exact tensorD_tensorD (pairFreeCx X) (pairFreeCx X) k y)

theorem fourCx_d (X : TopCat.{0}) (k : ℕ) :
    (fourCx X).d (k + 1) k = ModuleCat.ofHom (fourDLambda X k) := by
  simp [fourCx]

theorem fourCx_d_apply (X : TopCat.{0}) (k : ℕ)
    (y : TensorIdx (pairFreeCx X) (pairFreeCx X) (k + 1) →₀ ZMod 2) :
    ((fourCx X).d (k + 1) k).hom y = tensorD (pairFreeCx X) (pairFreeCx X) k y := by
  rw [fourCx_d]
  rfl

/-- The pushforward, as a map of complexes over the group ring. -/
noncomputable def fourMap {X Y : TopCat.{0}} (f : X ⟶ Y) : fourCx X ⟶ fourCx Y where
  f k := ModuleCat.ofHom
    { toFun := (fourHom f).f k
      map_add' := fun u v => map_add _ u v
      map_smul' := fun c y => fourHom_smul f k c y :
      (TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) →ₗ[GroupRingZ2]
        (TensorIdx (pairFreeCx Y) (pairFreeCx Y) k →₀ ZMod 2) }
  comm' i j hij := by
    have hij' : j + 1 = i := hij
    subst hij'
    rw [fourCx_d, fourCx_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    exact ((fourHom f).comm j y).symm

/-- **The fourfold object of the comparison**, as a functor. -/
noncomputable def four : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} GroupRingZ2) ℕ where
  obj X := fourCx X
  map f := fourMap f
  map_id X := by
    refine HomologicalComplex.hom_ext _ _ fun k => ?_
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    show (fourHom (𝟙 X)).f k y = y
    show tenHom (pairHom (𝟙 X)) (pairHom (𝟙 X)) k y = y
    rw [show pairHom (𝟙 X) = FreeCxHom.id (pairFreeCx X) from by
      rw [pairHom, singHom_id]
      refine FreeCxHom.ext (funext fun m => ?_)
      apply LinearMap.ext
      intro u
      exact tenHom_id (singFreeCx X) (singFreeCx X) m u]
    exact tenHom_id (pairFreeCx X) (pairFreeCx X) k y
  map_comp f g := by
    refine HomologicalComplex.hom_ext _ _ fun k => ?_
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    show tenHom (pairHom (f ≫ g)) (pairHom (f ≫ g)) k y
      = tenHom (pairHom g) (pairHom g) k (tenHom (pairHom f) (pairHom f) k y)
    rw [show pairHom (f ≫ g) = (pairHom g).comp (pairHom f) from by
      rw [pairHom, pairHom, pairHom, singHom_comp]
      refine FreeCxHom.ext (funext fun m => ?_)
      apply LinearMap.ext
      intro u
      exact tenHom_comp (singHom f) (singHom f) (singHom g) (singHom g) m u]
    exact tenHom_comp (pairHom f) (pairHom f) (pairHom g) (pairHom g) k y

@[simp] theorem four_obj (X : TopCat.{0}) : four.obj X = fourCx X := rfl

/-! ## 6. Acyclicity on the models -/

/-- **The fourfold object is acyclic on the models.** -/
theorem four_acyclicOnModels : AcyclicOnModels stdSimplexTop GroupRingZ2 four where
  exists_preimage n k y hy := by
    have hy' : tensorD (pairFreeCx (stdSimplexTop n)) (pairFreeCx (stdSimplexTop n)) k y = 0 :=
      (fourCx_d_apply (stdSimplexTop n) k y).symm.trans hy
    obtain ⟨z, hz⟩ := tensorD_exists_preimage (pairAug n) (pairAug n) k y hy'
    exact ⟨z, (fourCx_d_apply (stdSimplexTop n) (k + 1) z).trans hz⟩

end

end GroupApproximation.CharClass
