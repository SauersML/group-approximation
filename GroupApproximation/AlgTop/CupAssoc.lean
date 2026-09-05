import GroupApproximation.AlgTop.CupProduct

/-!
# Strict associativity and left unitality of the cup product

The Alexander–Whitney cup product is associative **already on cochains**: both
`(φ ⌣ ψ) ⌣ χ` and `φ ⌣ (ψ ⌣ χ)` evaluate on a singular `(p+q+r)`-simplex `σ` to

```text
φ(σ|[0..p]) · ψ(σ|[p..p+q]) · χ(σ|[p+q..p+q+r]),
```

so no chain homotopy is needed. What *is* needed is degree bookkeeping: `(p+q)+r`
and `p+(q+r)` are only propositionally equal in `ℕ`, so the two sides live in
different (though definitionally isomorphic) dependent types and must be compared
through the degree cast `cochainCast`.

Left unitality `1 ⌣ ψ = ψ` has the same shape: `0 + q` is not definitionally `q`
(unlike `q + 0`, which is, and which is why right unitality `cochainCup_one` is
cast-free in the vendored development).

## Main results

* `cochainCup_assoc` — strict associativity of the cochain cup product.
* `cup_assoc`, `cup_assoc'` — associativity of the cohomology cup product,
  transported by `cohCast`.
* `cochainCup_one_left`, `one_cup` — left unitality.

## Method

Each identity reduces to an equality of composites of the front/back face
inclusions in `SimplexCategory`, proved by computing vertex values:

* `frontFace p q ≫ frontFace (p+q) r = frontFace p (q+r) ≫ awCastAssoc p q r`
  (both send `i ↦ i`);
* `backFace p q ≫ frontFace (p+q) r
    = frontFace q r ≫ backFace p (q+r) ≫ awCastAssoc p q r` (both send `i ↦ i+p`);
* `backFace (p+q) r = backFace q r ≫ backFace p (q+r) ≫ awCastAssoc p q r`
  (both send `i ↦ i+p+q`);
* `backFace 0 q = awCastZeroAdd q` (both send `i ↦ i`).
-/

open CategoryTheory Limits AlgebraicTopology Simplicial SimplexCategory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation.AlgTop

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

/-! ## 1. The associativity and zero-add degree casts in `SimplexCategory` -/

/-- The object-level degree equality `⦋p+(q+r)⦌ = ⦋p+q+r⦌`. -/
theorem awDegAssoc (p q r : ℕ) : (⦋p + (q + r)⦌ : SimplexCategory) = ⦋p + q + r⦌ := by
  rw [Nat.add_assoc]

/-- The degree-cast morphism `⦋p+(q+r)⦌ ⟶ ⦋p+q+r⦌`. -/
def awCastAssoc (p q r : ℕ) : (⦋p + (q + r)⦌ : SimplexCategory) ⟶ ⦋p + q + r⦌ :=
  eqToHom (awDegAssoc p q r)

/-- The associativity degree cast is a relabelling: it preserves vertex values. -/
@[simp] lemma awCastAssoc_val (p q r : ℕ) (x : Fin (p + (q + r) + 1)) :
    (((awCastAssoc p q r).toOrderHom x : Fin (p + q + r + 1)) : ℕ) = x.val := by
  rw [awCastAssoc, SimplexCategory.eqToHom_toOrderHom (awDegAssoc p q r)]; rfl

/-- The object-level degree equality `⦋q⦌ = ⦋0+q⦌`. -/
theorem awDegZeroAdd (q : ℕ) : (⦋q⦌ : SimplexCategory) = ⦋0 + q⦌ := by
  rw [Nat.zero_add]

/-- The degree-cast morphism `⦋q⦌ ⟶ ⦋0+q⦌`. -/
def awCastZeroAdd (q : ℕ) : (⦋q⦌ : SimplexCategory) ⟶ ⦋0 + q⦌ :=
  eqToHom (awDegZeroAdd q)

@[simp] lemma awCastZeroAdd_val (q : ℕ) (x : Fin (q + 1)) :
    (((awCastZeroAdd q).toOrderHom x : Fin (0 + q + 1)) : ℕ) = x.val := by
  rw [awCastZeroAdd, SimplexCategory.eqToHom_toOrderHom (awDegZeroAdd q)]; rfl

/-! ## 2. Face composition identities -/

/-- The front `p`-face of the front `(p+q)`-face is the front `p`-face. -/
theorem frontFace_comp_frontFace (p q r : ℕ) :
    frontFace p q ≫ frontFace (p + q) r = frontFace p (q + r) ≫ awCastAssoc p q r := by
  ext x : 3
  apply Fin.ext
  have hL : (((frontFace p q ≫ frontFace (p + q) r).toOrderHom x
      : Fin (p + q + r + 1)) : ℕ) = x.val := by
    show (((frontFace (p + q) r).toOrderHom ((frontFace p q).toOrderHom x)) : ℕ) = x.val
    rw [frontFace_apply, frontFace_apply]
  have hR : (((frontFace p (q + r) ≫ awCastAssoc p q r).toOrderHom x
      : Fin (p + q + r + 1)) : ℕ) = x.val := by
    show (((awCastAssoc p q r).toOrderHom ((frontFace p (q + r)).toOrderHom x)) : ℕ) = x.val
    rw [awCastAssoc_val, frontFace_apply]
  omega

/-- The back `q`-face of the front `(p+q)`-face is the middle block. -/
theorem backFace_comp_frontFace (p q r : ℕ) :
    backFace p q ≫ frontFace (p + q) r
      = frontFace q r ≫ backFace p (q + r) ≫ awCastAssoc p q r := by
  ext x : 3
  apply Fin.ext
  have hL : (((backFace p q ≫ frontFace (p + q) r).toOrderHom x
      : Fin (p + q + r + 1)) : ℕ) = x.val + p := by
    show (((frontFace (p + q) r).toOrderHom ((backFace p q).toOrderHom x)) : ℕ) = x.val + p
    rw [frontFace_apply, backFace_apply]
  have hR : (((frontFace q r ≫ backFace p (q + r) ≫ awCastAssoc p q r).toOrderHom x
      : Fin (p + q + r + 1)) : ℕ) = x.val + p := by
    show (((awCastAssoc p q r).toOrderHom ((backFace p (q + r)).toOrderHom
        ((frontFace q r).toOrderHom x))) : ℕ) = x.val + p
    rw [awCastAssoc_val, backFace_apply, frontFace_apply]
  omega

/-- The back `r`-face of a `(p+q+r)`-simplex is the back `r`-face of its back
`(q+r)`-face. -/
theorem backFace_comp_backFace (p q r : ℕ) :
    backFace (p + q) r = backFace q r ≫ backFace p (q + r) ≫ awCastAssoc p q r := by
  ext x : 3
  apply Fin.ext
  have hL : (((backFace (p + q) r).toOrderHom x : Fin (p + q + r + 1)) : ℕ)
      = x.val + (p + q) := by
    rw [backFace_apply]
  have hR : (((backFace q r ≫ backFace p (q + r) ≫ awCastAssoc p q r).toOrderHom x
      : Fin (p + q + r + 1)) : ℕ) = x.val + q + p := by
    show (((awCastAssoc p q r).toOrderHom ((backFace p (q + r)).toOrderHom
        ((backFace q r).toOrderHom x))) : ℕ) = x.val + q + p
    rw [awCastAssoc_val, backFace_apply, backFace_apply]
  omega

/-- With an empty front block the back face is the degree relabelling. -/
theorem backFace_zero_eq (q : ℕ) : backFace 0 q = awCastZeroAdd q := by
  ext x : 3
  apply Fin.ext
  have hL : (((backFace 0 q).toOrderHom x : Fin (0 + q + 1)) : ℕ) = x.val := by
    rw [backFace_apply]
  have hR : (((awCastZeroAdd q).toOrderHom x : Fin (0 + q + 1)) : ℕ) = x.val :=
    awCastZeroAdd_val q x
  omega

/-! ## 3. Simplex-level restriction identities -/

/-- The singular `(p+q+r)`-simplex `σ` relabelled as a `p+(q+r)`-simplex. -/
def awCastAssocSimplex (X : TopCat.{0}) (p q r : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋p + q + r⦌ : SimplexCategory))) :
    (TopCat.toSSet.obj X).obj (Opposite.op (⦋p + (q + r)⦌ : SimplexCategory)) :=
  (TopCat.toSSet.obj X).map (awCastAssoc p q r).op σ

theorem frontSimplex_frontSimplex (X : TopCat.{0}) (p q r : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋p + q + r⦌ : SimplexCategory))) :
    frontSimplex X p q (frontSimplex X (p + q) r σ)
      = frontSimplex X p (q + r) (awCastAssocSimplex X p q r σ) := by
  unfold frontSimplex awCastAssocSimplex
  rw [← Functor.map_comp_apply, ← op_comp, ← Functor.map_comp_apply, ← op_comp,
    frontFace_comp_frontFace p q r]

theorem backSimplex_frontSimplex (X : TopCat.{0}) (p q r : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋p + q + r⦌ : SimplexCategory))) :
    backSimplex X p q (frontSimplex X (p + q) r σ)
      = frontSimplex X q r (backSimplex X p (q + r) (awCastAssocSimplex X p q r σ)) := by
  unfold frontSimplex backSimplex awCastAssocSimplex
  rw [← Functor.map_comp_apply, ← op_comp, ← Functor.map_comp_apply, ← op_comp,
    ← Functor.map_comp_apply, ← op_comp, Category.assoc, backFace_comp_frontFace p q r]

theorem backSimplex_backSimplex (X : TopCat.{0}) (p q r : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋p + q + r⦌ : SimplexCategory))) :
    backSimplex X (p + q) r σ
      = backSimplex X q r (backSimplex X p (q + r) (awCastAssocSimplex X p q r σ)) := by
  unfold backSimplex awCastAssocSimplex
  rw [← Functor.map_comp_apply, ← op_comp, ← Functor.map_comp_apply, ← op_comp,
    Category.assoc, ← backFace_comp_backFace p q r]

/-- The singular `q`-simplex `σ` of degree `0+q` relabelled as a `q`-simplex. -/
def awCastZeroAddSimplex (X : TopCat.{0}) (q : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋0 + q⦌ : SimplexCategory))) :
    (TopCat.toSSet.obj X).obj (Opposite.op (⦋q⦌ : SimplexCategory)) :=
  (TopCat.toSSet.obj X).map (awCastZeroAdd q).op σ

theorem backSimplex_zero (X : TopCat.{0}) (q : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋0 + q⦌ : SimplexCategory))) :
    backSimplex X 0 q σ = awCastZeroAddSimplex X q σ := by
  unfold backSimplex awCastZeroAddSimplex
  rw [backFace_zero_eq q]

/-! ## 4. Evaluating the degree casts -/

theorem cochainCast_eval_awCastAssoc (R : Type) [CommRing R] (X : TopCat.{0}) (p q r : ℕ)
    (χ : singularCochainGroup R X (p + (q + r))) (σ : singularSimplices X (p + q + r)) :
    cochainEval (p + q + r) (cochainCast (add_assoc p q r).symm χ) σ
      = cochainEval (p + (q + r)) χ (awCastAssocSimplex X p q r σ) := by
  unfold cochainEval cochainCast awCastAssocSimplex
  rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  congr 1
  have e1 : (eqToHom (by rw [(add_assoc p q r).symm]) :
      (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj X).X
          (p + q + r)
       ⟶ (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj X).X
          (p + (q + r)))
      = (singularChainSimplicialModule R X).map ((awCastAssoc p q r).op) := by
    rw [show ((awCastAssoc p q r).op) = eqToHom (by rw [(add_assoc p q r).symm]) from ?_]
    · rw [eqToHom_map]
    · rw [awCastAssoc, eqToHom_op]
  rw [e1]
  exact singularChainSimplicialModule_map_generator R X (p + (q + r)) (p + q + r)
    ((awCastAssoc p q r).op) σ

theorem cochainCast_eval_awCastZeroAdd (R : Type) [CommRing R] (X : TopCat.{0}) (q : ℕ)
    (χ : singularCochainGroup R X q) (σ : singularSimplices X (0 + q)) :
    cochainEval (0 + q) (cochainCast (Nat.zero_add q).symm χ) σ
      = cochainEval q χ (awCastZeroAddSimplex X q σ) := by
  unfold cochainEval cochainCast awCastZeroAddSimplex
  rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  congr 1
  have e1 : (eqToHom (by rw [(Nat.zero_add q).symm]) :
      (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj X).X (0 + q)
       ⟶ (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj X).X q)
      = (singularChainSimplicialModule R X).map ((awCastZeroAdd q).op) := by
    rw [show ((awCastZeroAdd q).op) = eqToHom (by rw [(Nat.zero_add q).symm]) from ?_]
    · rw [eqToHom_map]
    · rw [awCastZeroAdd, eqToHom_op]
  rw [e1]
  exact singularChainSimplicialModule_map_generator R X q (0 + q) ((awCastZeroAdd q).op) σ

/-! ## 5. Strict associativity and left unitality on cochains -/

/-- **Strict associativity of the Alexander–Whitney cochain cup product.** Both
sides evaluate on `σ` to `φ(σ|[0..p]) · ψ(σ|[p..p+q]) · χ(σ|[p+q..p+q+r])`. -/
theorem cochainCup_assoc (R : Type) [CommRing R] {X : TopCat.{0}} (p q r : ℕ)
    (φ : singularCochainGroup R X p) (ψ : singularCochainGroup R X q)
    (χ : singularCochainGroup R X r) :
    cochainCup (p + q) r (cochainCup p q φ ψ) χ
      = cochainCast (add_assoc p q r).symm
          (cochainCup p (q + r) φ (cochainCup q r ψ χ)) := by
  apply cochain_ext
  intro σ
  rw [cochainCup_eval, cochainCup_eval, cochainCast_eval_awCastAssoc, cochainCup_eval,
    cochainCup_eval, frontSimplex_frontSimplex X p q r σ, backSimplex_frontSimplex X p q r σ,
    backSimplex_backSimplex X p q r σ]
  ring

/-- **Left unitality of the cochain cup product.** -/
theorem cochainCup_one_left (R : Type) [CommRing R] {X : TopCat.{0}} (q : ℕ)
    (ψ : singularCochainGroup R X q) :
    cochainCup 0 q (cochainOne (R := R) (Z := X)) ψ
      = cochainCast (Nat.zero_add q).symm ψ := by
  apply cochain_ext
  intro σ
  rw [cochainCup_eval, cochainOne_eval, one_mul, cochainCast_eval_awCastZeroAdd,
    backSimplex_zero X q σ]

/-! ## 6. The cohomology statements -/

variable {R : Type} [CommRing R]

/-- **Associativity of the cup product on cohomology**, in the form that avoids
composing two degree transports. -/
theorem cup_assoc' {X : TopCat.{0}} {p q r : ℕ} (a : cohomology R X p) (b : cohomology R X q)
    (c : cohomology R X r) :
    (a ⌣ b) ⌣ c
      = (cohCast R X (add_assoc p q r).symm).hom (a ⌣ (b ⌣ c)) := by
  obtain ⟨φ, hφ, rfl⟩ := cocycleClass_surjective R X p a
  obtain ⟨ψ, hψ, rfl⟩ := cocycleClass_surjective R X q b
  obtain ⟨χ, hχ, rfl⟩ := cocycleClass_surjective R X r c
  rw [cup_mk, cup_mk, cup_mk, cup_mk,
    ← cocycleClass_cast R X (add_assoc p q r).symm _
      (cochainCup_cocycle hφ (cochainCup_cocycle hψ hχ))
      (by rw [← cochainCup_assoc R p q r φ ψ χ]
          exact cochainCup_cocycle (cochainCup_cocycle hφ hψ) hχ)]
  exact cocycleClass_congr R X (p + q + r) (cochainCup_assoc R p q r φ ψ χ) _ _

/-- **Associativity of the cup product on cohomology.** -/
theorem cup_assoc {X : TopCat.{0}} {p q r : ℕ} (a : cohomology R X p) (b : cohomology R X q)
    (c : cohomology R X r) :
    (cohCast R X (add_assoc p q r)).hom ((a ⌣ b) ⌣ c) = a ⌣ (b ⌣ c) := by
  rw [cup_assoc' a b c, cohCast_comp]
  exact cohCast_self_apply R X _ _

/-- **Left unitality of the cup product on cohomology.** -/
theorem one_cup {X : TopCat.{0}} {q : ℕ} (b : cohomology R X q) :
    one R X ⌣ b = (cohCast R X (Nat.zero_add q).symm).hom b := by
  obtain ⟨ψ, hψ, rfl⟩ := cocycleClass_surjective R X q b
  rw [one, cup_mk,
    ← cocycleClass_cast R X (Nat.zero_add q).symm ψ hψ
      (by rw [← cochainCup_one_left R q ψ]
          exact cochainCup_cocycle (cochainCoboundary_cochainOne X) hψ)]
  exact cocycleClass_congr R X (0 + q) (cochainCup_one_left R q ψ) _ _

/-- **Left unitality**, transported so that the unit acts as the identity. -/
theorem one_cup' {X : TopCat.{0}} {q : ℕ} (b : cohomology R X q) :
    (cohCast R X (Nat.zero_add q)).hom (one R X ⌣ b) = b := by
  rw [one_cup b, cohCast_comp]
  exact cohCast_self_apply R X _ _

end

end GroupApproximation.AlgTop
