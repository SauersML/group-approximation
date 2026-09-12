import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.AlexanderWhitneyFaceMaps

/-!
# Alexander–Whitney cochain chain-map (Leibniz) identity

This file proves the **build-clean** Alexander–Whitney chain-map / Leibniz
identity for the cochain-level singular cup product, over `ZMod 2` coefficients
(where the Koszul signs are trivial):

```text
δ(φ ⌣ ψ) = δφ ⌣ ψ + φ ⌣ δψ.
```

This is the central algebraic identity that descends the cochain cup product
`cochainCup` of `CupProduct.lean` to a cohomology-level product. There are **no**
placeholder definitions, **no** axioms, and **no** fake declarations: every
statement is fully proved.

## Strategy

The singular cochain coboundary `δ = d^p : C^p → C^{p+1}` is, by construction,
precomposition with the singular chain boundary `∂ = Σ_i (-1)^i d_i`
(`cochainCoboundary_eval`). Telescoping `δ(φ ⌣ ψ)` over the boundary faces and
splitting by the position of the deleted vertex relative to the cup split point
`p` uses the four face-composition identities of `AlexanderWhitneyFaceMaps.lean`
(`frontFace_comp_δ_of_le/_gt`, `backFace_comp_δ_of_le/_gt`) and the two endpoint
identities (`aw_endpoint_front`, `aw_endpoint_back`). The two endpoint faces
produce the *same* restriction pair and cancel; over `ZMod 2` they coincide and
cancel mod 2.

## Degree bookkeeping

The three terms naturally live in degrees `(p+q)+1`, `(p+1)+q` and `p+(q+1)`.
Now `p+(q+1)` is **definitionally** `(p+q)+1`, but `(p+1)+q` is only
propositionally equal to it, so the `δφ ⌣ ψ` term is transported along the
degree equality via the cochain degree cast `cochainCast`.

## Main results

* `cochainCoboundary` / `cochainCoboundary_eval` — the cochain coboundary and its
  alternating-face evaluation formula.
* `aw_cochain_leibniz_zmod2` — the Leibniz / chain-map identity over `ZMod 2`.
-/

open CategoryTheory MonoidalCategory AlgebraicTopology Simplicial SimplexCategory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-! ## 0. The underlying simplicial module of the singular chain complex -/

/-- The free `R`-module simplicial object whose alternating face map complex is
the singular chain complex `C_•(Z; R)`. Its value in degree `n` is the coproduct
`∐_{σ : n-simplex} R`. -/
noncomputable def singularChainSimplicialModule (R : Type) [CommRing R] (Z : TopCat.{0}) :
    SimplicialObject (ModuleCat.{0} R) :=
  ((Limits.sigmaConst ⋙ SimplicialObject.whiskering (Type 0) (ModuleCat.{0} R)).obj
    (ModuleCat.of R R)).obj (TopCat.toSSet.obj Z)

/-- A morphism in `SimplexCategoryᵒᵖ` acts on the singular chain simplicial module
by sending a basis generator to the basis generator at the restricted simplex. -/
theorem singularChainSimplicialModule_map_generator (R : Type) [CommRing R] (X : TopCat.{0})
    (m m' : ℕ) (g : (Opposite.op (⦋m'⦌ : SimplexCategory)) ⟶ Opposite.op ⦋m⦌)
    (σ : singularSimplices X m') :
    ((singularChainSimplicialModule R X).map g).hom
      ((Limits.Sigma.ι (fun (_ : singularSimplices X m') => ModuleCat.of R R) σ).hom (1 : R))
    = (Limits.Sigma.ι (fun (_ : singularSimplices X m) => ModuleCat.of R R)
        ((TopCat.toSSet.obj X).map g σ)).hom (1 : R) := by
  have key : (Limits.Sigma.ι (fun (_ : singularSimplices X m') => ModuleCat.of R R) σ)
      ≫ (singularChainSimplicialModule R X).map g
      = Limits.Sigma.ι (fun (_ : singularSimplices X m) => ModuleCat.of R R)
        ((TopCat.toSSet.obj X).map g σ) := by
    dsimp [singularChainSimplicialModule, SimplicialObject.whiskering, Limits.sigmaConst]
    simp
  have := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom key) (1 : R)
  convert this using 1 <;> rfl

/-- The simplicial face map `δ i` of the singular chain simplicial module sends
the basis generator at a simplex `σ` to the basis generator at its `i`-th
boundary face `d_i σ = faceSimplex Z n i σ`. -/
theorem singularChainSimplicialModule_δ_generator (R : Type) [CommRing R] (Z : TopCat.{0})
    (n : ℕ) (i : Fin (n + 2)) (σ : singularSimplices Z (n + 1)) :
    ((singularChainSimplicialModule R Z).δ i).hom
      ((Limits.Sigma.ι (fun (_ : singularSimplices Z (n + 1)) => ModuleCat.of R R) σ).hom (1 : R))
    = (Limits.Sigma.ι (fun (_ : singularSimplices Z n) => ModuleCat.of R R)
        (faceSimplex Z n i σ)).hom (1 : R) :=
  singularChainSimplicialModule_map_generator R Z n (n + 1) (SimplexCategory.δ i).op σ

/-! ## 1. The cochain coboundary and its evaluation formula -/

/-- The **cochain coboundary** `δ = d^p : C^p(Z; R) → C^{p+1}(Z; R)`, the
differential of the singular cochain complex. By construction it is
precomposition with the singular chain boundary. -/
noncomputable def cochainCoboundary (R : Type) [CommRing R] (Z : TopCat.{0}) (p : ℕ)
    (φ : singularCochainGroup R Z p) : singularCochainGroup R Z (p + 1) :=
  (((singularCochainComplexFunctor R (ModuleCat.of R R)).obj (Opposite.op Z)).d p (p + 1)).hom φ

/-- **Coboundary evaluation formula.** The coboundary `δφ` of a `p`-cochain `φ`,
evaluated on a `(p+1)`-simplex `σ`, is the alternating sum of `φ` over the
boundary faces: `(δφ)(σ) = Σ_i (-1)^i φ(d_i σ)`. -/
theorem cochainCoboundary_eval (R : Type) [CommRing R] (Z : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup R Z n) (σ : singularSimplices Z (n + 1)) :
    cochainEval (n + 1) (cochainCoboundary R Z n φ) σ
      = ∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) * cochainEval n φ (faceSimplex Z n i σ) := by
  unfold cochainEval cochainCoboundary
  have hd : (((singularCochainComplexFunctor R (ModuleCat.of R R)).obj (Opposite.op Z)).d n (n + 1)).hom φ
      = (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj Z).d (n + 1) n ≫ φ :=
    rfl
  rw [hd, ModuleCat.hom_comp, LinearMap.comp_apply,
    show (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj Z).d (n + 1) n
        = (AlternatingFaceMapComplex.obj (singularChainSimplicialModule R Z)).d (n + 1) n from rfl,
    AlternatingFaceMapComplex.obj_d_eq, ModuleCat.hom_sum, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [ModuleCat.hom_zsmul, LinearMap.smul_apply, map_zsmul, zsmul_eq_mul]
  push_cast
  exact congrArg (fun t => (-1 : R) ^ (i : ℕ) * (ModuleCat.Hom.hom φ) t)
    (singularChainSimplicialModule_δ_generator R Z n i σ)

/-! ## 2. The degree cast on cochains and the cast singular simplex -/

/-- The **cochain degree cast** transporting a cochain along an equality of
degrees `m = m'`. Needed because `(p+1)+q` and `(p+q)+1` are only
propositionally equal. -/
noncomputable def cochainCast {R : Type} [CommRing R] {Z : TopCat.{0}} {m m' : ℕ}
    (h : m = m') (φ : singularCochainGroup R Z m) : singularCochainGroup R Z m' :=
  (eqToHom (by rw [h]) :
      (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj Z).X m'
        ⟶ (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj Z).X m)
    ≫ φ

/-- The singular `(p+q+1)`-simplex `σ` relabelled as a `(p+1+q)`-simplex via the
degree cast `awCastLeft`. This is the cast simplex on which the `δφ ⌣ ψ` term is
evaluated. -/
noncomputable def awCastSimplex (X : TopCat.{0}) (p q : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋p + q + 1⦌ : SimplexCategory))) :
    (TopCat.toSSet.obj X).obj (Opposite.op (⦋p + 1 + q⦌ : SimplexCategory)) :=
  (TopCat.toSSet.obj X).map (awCastLeft p q).op σ

/-- **Evaluation of the degree-cast cochain.** Evaluating `cochainCast` of the
`δφ ⌣ ψ` term on `σ` equals evaluating the original cochain on the cast simplex
`awCastSimplex X p q σ`. -/
theorem cochainCast_eval_awCastSimplex (R : Type) [CommRing R] (X : TopCat.{0}) (p q : ℕ)
    (χ : singularCochainGroup R X (p + 1 + q)) (σ : singularSimplices X (p + q + 1)) :
    cochainEval (p + q + 1) (cochainCast (aw_degree_left_succ p q) χ) σ
      = cochainEval (p + 1 + q) χ (awCastSimplex X p q σ) := by
  unfold cochainEval cochainCast awCastSimplex
  rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  congr 1
  have e1 : (eqToHom (by rw [aw_degree_left_succ p q]) :
      (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj X).X (p + q + 1)
       ⟶ (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj X).X (p + 1 + q))
      = (singularChainSimplicialModule R X).map ((awCastLeft p q).op) := by
    rw [show ((awCastLeft p q).op) = eqToHom (by rw [aw_degree_left_succ p q]) from ?_]
    · rw [eqToHom_map]
    · rw [awCastLeft, eqToHom_op]
  rw [e1]
  exact singularChainSimplicialModule_map_generator R X (p + 1 + q) (p + q + 1)
    ((awCastLeft p q).op) σ

/-- **Evaluation of the right (definitional) degree cast.** Since `p+(q+1)` is
definitionally `(p+q)+1`, the `φ ⌣ δψ` cast is the identity. -/
theorem cochainCast_eval_right (R : Type) [CommRing R] (X : TopCat.{0}) (p q : ℕ)
    (χ : singularCochainGroup R X (p + (q + 1))) (σ : singularSimplices X (p + q + 1)) :
    cochainEval (p + q + 1) (cochainCast (aw_degree_right_succ p q) χ) σ
      = cochainEval (p + (q + 1)) χ σ :=
  rfl

/-! ## 3. Simplex-level face identities (cast versions)

The two `k > p` cases are already cast-free in `AlexanderWhitneyFaceMaps.lean`
(`frontSimplex_faceSimplex_of_gt`, `backSimplex_faceSimplex_of_gt`). Here we add
the `k ≤ p` cases and the two endpoint identities, both of which involve the
degree cast simplex `awCastSimplex`. -/

/-- **Simplex-level internal front face, `k ≤ p`.** -/
theorem frontSimplex_faceSimplex_of_le (X : TopCat.{0}) (p q : ℕ) (k : Fin (p + q + 2))
    (hk : k.val ≤ p)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋p + q + 1⦌ : SimplexCategory))) :
    frontSimplex X p q (faceSimplex X (p + q) k σ)
      = faceSimplex X p ⟨k.val, by omega⟩ (frontSimplex X (p + 1) q (awCastSimplex X p q σ)) := by
  unfold frontSimplex faceSimplex awCastSimplex
  rw [← Functor.map_comp_apply, ← op_comp, frontFace_comp_δ_of_le p q k hk]
  rw [op_comp, Functor.map_comp_apply, op_comp, Functor.map_comp_apply]

/-- **Simplex-level internal back face, `k ≤ p`.** Independent of `k`. -/
theorem backSimplex_faceSimplex_of_le (X : TopCat.{0}) (p q : ℕ) (k : Fin (p + q + 2))
    (hk : k.val ≤ p)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋p + q + 1⦌ : SimplexCategory))) :
    backSimplex X p q (faceSimplex X (p + q) k σ)
      = backSimplex X (p + 1) q (awCastSimplex X p q σ) := by
  unfold backSimplex faceSimplex awCastSimplex
  rw [← Functor.map_comp_apply, ← op_comp, backFace_comp_δ_of_le p q k hk]
  rw [op_comp, Functor.map_comp_apply]

/-- **Front endpoint identity (simplex level).** The top boundary face of the
front `(p+1)`-face of the cast simplex recovers the front `p`-face of `σ`. -/
theorem frontSimplex_faceSimplex_endpoint (X : TopCat.{0}) (p q : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋p + q + 1⦌ : SimplexCategory))) :
    faceSimplex X p (Fin.last (p + 1)) (frontSimplex X (p + 1) q (awCastSimplex X p q σ))
      = frontSimplex X p (q + 1) σ := by
  unfold frontSimplex faceSimplex awCastSimplex
  rw [← Functor.map_comp_apply, ← op_comp, ← Functor.map_comp_apply, ← op_comp,
    Category.assoc, aw_endpoint_front p q]
  rfl

/-- **Back endpoint identity (simplex level).** The bottom boundary face of the
back `(q+1)`-face of `σ` recovers the back `q`-face of the cast simplex. -/
theorem backSimplex_faceSimplex_endpoint (X : TopCat.{0}) (p q : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋p + q + 1⦌ : SimplexCategory))) :
    faceSimplex X q 0 (backSimplex X p (q + 1) σ)
      = backSimplex X (p + 1) q (awCastSimplex X p q σ) := by
  unfold backSimplex faceSimplex awCastSimplex
  rw [← Functor.map_comp_apply, ← op_comp, ← Functor.map_comp_apply, ← op_comp,
    aw_endpoint_back p q]
  rfl

/-! ## 4. An abstract char-2 sum-splitting lemma -/

/-- **Abstract characteristic-two sum split.** If a function `L` on
`Fin (p+q+2)` matches `A` on the front block `k ≤ p`, matches `B` on the back
block `k > p`, and the two endpoints `A (last)` and `B 0` coincide, then in a
2-torsion abelian group `∑ L = ∑ A + ∑ B` (the endpoints cancel mod 2). -/
theorem sum_split_char2 {M : Type} [AddCommGroup M] (htwo : ∀ x : M, x + x = 0)
    (p q : ℕ) (L : Fin (p + q + 2) → M) (A : Fin (p + 2) → M) (B : Fin (q + 2) → M)
    (hle : ∀ k : Fin (p + q + 2), (hk : k.val ≤ p) → L k = A ⟨k.val, by omega⟩)
    (hgt : ∀ k : Fin (p + q + 2), (hk : p < k.val) → L k = B ⟨k.val - p, by have := k.isLt; omega⟩)
    (hend : A (Fin.last (p + 1)) = B 0) :
    ∑ k, L k = (∑ i, A i) + ∑ j, B j := by
  rw [Fin.sum_univ_castSucc (n := p + 1) A, Fin.sum_univ_succ (n := q + 1) B]
  set e : Fin (p + 1) ⊕ Fin (q + 1) ≃ Fin (p + q + 2) :=
    finSumFinEquiv.trans (finCongr (by omega)) with he
  have hsum : ∑ k, L k = ∑ s, L (e s) := (Equiv.sum_comp e L).symm
  rw [hsum, Fintype.sum_sum_type]
  have hL : ∑ a₁ : Fin (p + 1), L (e (Sum.inl a₁)) = ∑ i : Fin (p + 1), A i.castSucc := by
    apply Finset.sum_congr rfl; intro i _
    have hval : (e (Sum.inl i)).val = i.val := by
      simp [he, finSumFinEquiv_apply_left, Fin.castAdd, Fin.castLE]
    rw [hle (e (Sum.inl i)) (by rw [hval]; omega)]
    apply congrArg A; apply Fin.ext; simp [hval, Fin.castSucc, Fin.castAdd, Fin.castLE]
  have hR : ∑ a₂ : Fin (q + 1), L (e (Sum.inr a₂)) = ∑ j : Fin (q + 1), B j.succ := by
    apply Finset.sum_congr rfl; intro j _
    have hval : (e (Sum.inr j)).val = p + 1 + j.val := by
      simp [he, finSumFinEquiv_apply_right, Fin.natAdd]
    rw [hgt (e (Sum.inr j)) (by rw [hval]; omega)]
    apply congrArg B; apply Fin.ext; simp only [hval, Fin.val_succ]; omega
  rw [hL, hR, hend]
  have hrw : (∑ i : Fin (p + 1), A i.castSucc + B 0) + (B 0 + ∑ j : Fin (q + 1), B j.succ)
      = (∑ i : Fin (p + 1), A i.castSucc + ∑ j : Fin (q + 1), B j.succ) + (B 0 + B 0) := by abel
  rw [hrw, htwo, add_zero]

/-! ## 5. The Leibniz identity over `ZMod 2` -/

/-- Over `ZMod 2`, the coefficient sign `(-1)^k` is `1`. -/
theorem neg_one_pow_zmod2 (k : ℕ) : (-1 : ZMod 2) ^ k = 1 := by
  have : (-1 : ZMod 2) = 1 := by decide
  rw [this, one_pow]

/-- **Alexander–Whitney cochain Leibniz identity over `ZMod 2`.**

The cochain coboundary is a derivation for the cup product (over `ZMod 2`, where
all Koszul signs are trivial):

```text
δ(φ ⌣ ψ) = δφ ⌣ ψ + φ ⌣ δψ.
```

This is the chain-map identity that lets the cup product descend to cohomology
(prompt 06). The `δφ ⌣ ψ` term, naturally of degree `(p+1)+q`, and the
`φ ⌣ δψ` term, of degree `p+(q+1)`, are transported to degree `(p+q)+1` via the
cochain degree cast. -/
theorem aw_cochain_leibniz_zmod2 {X : TopCat.{0}} (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) X q) :
    cochainCoboundary (ZMod 2) X (p + q) (cochainCup p q φ ψ)
      = cochainCast (aw_degree_left_succ p q)
          (cochainCup (p + 1) q (cochainCoboundary (ZMod 2) X p φ) ψ)
        + cochainCast (aw_degree_right_succ p q)
            (cochainCup p (q + 1) φ (cochainCoboundary (ZMod 2) X q ψ)) := by
  apply cochain_ext
  intro σ
  rw [cochainEval_add]
  rw [show cochainEval (p + q + 1)
        (cochainCoboundary (ZMod 2) X (p + q) (cochainCup p q φ ψ)) σ
      = ∑ k : Fin (p + q + 2),
          cochainEval p φ (frontSimplex X p q (faceSimplex X (p + q) k σ))
            * cochainEval q ψ (backSimplex X p q (faceSimplex X (p + q) k σ)) from ?_]
  · rw [show cochainEval (p + q + 1) (cochainCast (aw_degree_left_succ p q)
            (cochainCup (p + 1) q (cochainCoboundary (ZMod 2) X p φ) ψ)) σ
        = ∑ i : Fin (p + 2),
            cochainEval p φ (faceSimplex X p i (frontSimplex X (p + 1) q (awCastSimplex X p q σ)))
              * cochainEval q ψ (backSimplex X (p + 1) q (awCastSimplex X p q σ)) from ?_]
    · rw [show cochainEval (p + q + 1) (cochainCast (aw_degree_right_succ p q)
              (cochainCup p (q + 1) φ (cochainCoboundary (ZMod 2) X q ψ))) σ
          = ∑ j : Fin (q + 2),
              cochainEval p φ (frontSimplex X p (q + 1) σ)
                * cochainEval q ψ (faceSimplex X q j (backSimplex X p (q + 1) σ)) from ?_]
      · apply sum_split_char2 (by decide)
        · intro k hk
          rw [frontSimplex_faceSimplex_of_le X p q k hk, backSimplex_faceSimplex_of_le X p q k hk]
        · intro k hk
          rw [frontSimplex_faceSimplex_of_gt X p q k hk, backSimplex_faceSimplex_of_gt X p q k hk]
        · rw [frontSimplex_faceSimplex_endpoint X p q, backSimplex_faceSimplex_endpoint X p q]
      · rw [cochainCast_eval_right, cochainCup_eval, cochainCoboundary_eval, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; rw [neg_one_pow_zmod2, one_mul]
    · rw [cochainCast_eval_awCastSimplex, cochainCup_eval, cochainCoboundary_eval, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro i _; rw [neg_one_pow_zmod2, one_mul]
  · rw [cochainCoboundary_eval]
    apply Finset.sum_congr rfl; intro k _; rw [neg_one_pow_zmod2, one_mul, cochainCup_eval]

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
