import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CoveringTransferChains
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.AlexanderWhitneyChainMap

/-!
# The mod-2 transfer of `Sⁿ → RPⁿ` is a chain map

This file upgrades the degreewise mod-2 transfer `projTransferChainDegree` of
`CoveringTransferChains.lean` into a genuine **chain map**
```text
projTransferChainMap n :
  C_•(RPⁿ; F₂) ⟶ C_•(Sⁿ; F₂)
```
of singular chain complexes, by proving compatibility with the singular boundary:
for every `k`,
```text
projTransferChainDegree n (k+1) ≫ d = d ≫ projTransferChainDegree n k.
```

## Strategy

The proof rests on simplex-lift *uniqueness*, not on any invented computation.

* **Boundary formula (`singular_d_ι`).** Over `ZMod 2` the alternating-face
  differential of the singular chain complex acts on a basis simplex `ρ` by the
  *unsigned* sum of its boundary faces:
  `Sigma.ι ρ ≫ d = ∑ i, Sigma.ι (faceSimplex … i ρ)` (the signs `(-1)^i`
  collapse, since the chain groups are `2`-torsion). This is read off Mathlib's
  `AlternatingFaceMapComplex.obj_d_eq` together with the project's
  `singularChainSimplicialModule_δ_generator`.

* **Choice-independence of the transfer (`projTransferOnSimplex_eq_of_lift`).**
  For *any* continuous lift `τ` of a singular simplex `ρ` of `RPⁿ`, the transfer
  of `ρ` is the sum of the basis simplices of `τ` and of its antipode
  `antipodal ∘ τ`. (The fiber over the chosen vertex is the two-element set
  `{e, -e}`; the lift over `-e` is the antipode of the lift over `e`, so summing
  both sheets is independent of which fiber point was selected.) This is the
  genuine well-definedness statement, proved with `projLiftSimplex_unique` /
  `eq_projLiftSimplex`.

* **Face of a lift (`projTransferOnSimplex_face`).** The `i`-th face of a lift of
  `σ` is a lift of the `i`-th face of `σ` (naturality of the simplicial map
  induced by `proj n`), and its antipode is the corresponding face of the
  antipodal lift. Combined with choice-independence, this gives the term-by-term
  identity that makes the boundary square commute.

The key naturality inputs are two squares of Mathlib's singular simplicial set:
post-composition naturality of `TopCat.toSSetObjEquiv` along `proj n` /
`antipodal n` (both **definitional**), and the face naturality of the simplicial
map `TopCat.toSSet.map (TopCat.ofHom (proj n))` (its `NatTrans.naturality`).

## Main declarations

* `singular_d_ι` — the unsigned mod-2 boundary formula on a basis simplex.
* `projTransferOnSimplex_eq_of_lift` — choice-independence of the transfer.
* `projTransferOnSimplex_face` — the per-face term identity.
* `projTransfer_boundary` — the degreewise boundary-compatibility identity.
* `projTransferChainMap` — the assembled chain map `C_•(RPⁿ) ⟶ C_•(Sⁿ)`.
-/

noncomputable section

open CategoryTheory AlgebraicTopology Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The singular mod-2 chain complex of a space, as a `ChainComplex`. By
construction `(singularChainCx X).X k = singularChainZMod2 X k`. -/
abbrev singularChainCx (X : TopCat.{0}) : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{0} (ZMod 2))).obj transferCoeff).obj X

/-! ## 1. The mod-2 boundary on a basis simplex -/

/-- Morphism-level action of the simplicial face map `δ i` on a basis simplex:
the coproduct injection of `ρ` post-composed with `δ i` is the coproduct
injection of the `i`-th face `faceSimplex X k i ρ`. -/
theorem singularChainSimplicialModule_δ_ι (X : TopCat.{0}) (k : ℕ) (i : Fin (k + 2))
    (ρ : singularSimplices X (k + 1)) :
    Sigma.ι (fun (_ : singularSimplices X (k + 1)) => transferCoeff) ρ
        ≫ (singularChainSimplicialModule (ZMod 2) X).δ i
      = Sigma.ι (fun (_ : singularSimplices X k) => transferCoeff) (faceSimplex X k i ρ) := by
  simp [singularChainSimplicialModule, SimplicialObject.whiskering, Limits.sigmaConst,
    faceSimplex, SimplicialObject.δ]

/-- In a `2`-torsion abelian group the sign `(-1)^m` acts trivially. -/
theorem neg_one_zsmul_eq_self {A : Type*} [AddCommGroup A] (h2 : ∀ a : A, a + a = 0)
    (m : ℕ) (g : A) : (-1 : ℤ) ^ m • g = g := by
  have hneg : -g = g := neg_eq_of_add_eq_zero_right (h2 g)
  rcases Nat.even_or_odd m with he | ho
  · rw [he.neg_one_pow, one_zsmul]
  · rw [ho.neg_one_pow, neg_zsmul, one_zsmul, hneg]

/-- The hom-groups of the singular mod-2 chain complex are `2`-torsion. -/
theorem singularChain_add_self (X : TopCat.{0}) (k : ℕ)
    (g : transferCoeff ⟶ (singularChainCx X).X k) : g + g = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  calc g + g = (2 : ZMod 2) • g := by rw [two_smul]
    _ = 0 := by rw [h2, zero_smul]

/-- **Unsigned mod-2 boundary formula.** The singular differential `d` applied to
a basis simplex `ρ` is the unsigned sum of the coproduct injections of the
boundary faces of `ρ` (the signs `(-1)^i` collapse over `ZMod 2`). -/
theorem singular_d_ι (X : TopCat.{0}) (k : ℕ) (ρ : singularSimplices X (k + 1)) :
    Sigma.ι (fun (_ : singularSimplices X (k + 1)) => transferCoeff) ρ
        ≫ (singularChainCx X).d (k + 1) k
      = ∑ i : Fin (k + 2),
          Sigma.ι (fun (_ : singularSimplices X k) => transferCoeff) (faceSimplex X k i ρ) := by
  rw [show (singularChainCx X).d (k + 1) k
        = (AlternatingFaceMapComplex.obj (singularChainSimplicialModule (ZMod 2) X)).d (k + 1) k
      from rfl, AlternatingFaceMapComplex.obj_d_eq, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Preadditive.comp_zsmul, singularChainSimplicialModule_δ_ι]
  exact neg_one_zsmul_eq_self (singularChain_add_self X k) _ _

/-! ## 2. The simplicial maps induced by `proj n` and `antipodal n` -/

/-- The simplicial map on singular simplices induced by the covering `proj n`. -/
abbrev projSimplexMap (n k : ℕ) :
    singularSimplices (TopCat.of (Sphere n)) k → singularSimplices (TopCat.of (RP n)) k :=
  (TopCat.toSSet.map (TopCat.ofHom (proj n))).app (Opposite.op (SimplexCategory.mk k))

/-- The simplicial map on singular simplices induced by `antipodal n`. -/
abbrev antipodalSimplexMap (n k : ℕ) :
    singularSimplices (TopCat.of (Sphere n)) k → singularSimplices (TopCat.of (Sphere n)) k :=
  (TopCat.toSSet.map (TopCat.ofHom (antipodal n))).app (Opposite.op (SimplexCategory.mk k))

/-- **Post-composition naturality (proj).** Under the simplex/continuous-map
equivalence, `projSimplexMap` is post-composition by `proj n`. Definitional. -/
theorem toSSetObjEquiv_projSimplexMap (n k : ℕ) (u : singularSimplices (TopCat.of (Sphere n)) k) :
    TopCat.toSSetObjEquiv (TopCat.of (RP n)) (Opposite.op (SimplexCategory.mk k))
        (projSimplexMap n k u)
      = (proj n).comp
          (TopCat.toSSetObjEquiv (TopCat.of (Sphere n)) (Opposite.op (SimplexCategory.mk k)) u) :=
  rfl

/-- **Post-composition naturality (antipodal).** Definitional. -/
theorem toSSetObjEquiv_antipodalSimplexMap (n k : ℕ)
    (u : singularSimplices (TopCat.of (Sphere n)) k) :
    TopCat.toSSetObjEquiv (TopCat.of (Sphere n)) (Opposite.op (SimplexCategory.mk k))
        (antipodalSimplexMap n k u)
      = (antipodal n).comp
          (TopCat.toSSetObjEquiv (TopCat.of (Sphere n)) (Opposite.op (SimplexCategory.mk k)) u) :=
  rfl

/-- **Face naturality (proj).** The induced simplicial map commutes with faces. -/
theorem projSimplexMap_faceSimplex (n k : ℕ) (i : Fin (k + 2))
    (u : singularSimplices (TopCat.of (Sphere n)) (k + 1)) :
    projSimplexMap n k (faceSimplex (TopCat.of (Sphere n)) k i u)
      = faceSimplex (TopCat.of (RP n)) k i (projSimplexMap n (k + 1) u) := by
  simpa only [projSimplexMap, faceSimplex, SimplicialObject.δ,
    ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom
      ((TopCat.toSSet.map (TopCat.ofHom (proj n))).naturality (SimplexCategory.δ i).op) u

/-- **Face naturality (antipodal).** -/
theorem antipodalSimplexMap_faceSimplex (n k : ℕ) (i : Fin (k + 2))
    (u : singularSimplices (TopCat.of (Sphere n)) (k + 1)) :
    antipodalSimplexMap n k (faceSimplex (TopCat.of (Sphere n)) k i u)
      = faceSimplex (TopCat.of (Sphere n)) k i (antipodalSimplexMap n (k + 1) u) := by
  simpa only [antipodalSimplexMap, faceSimplex, SimplicialObject.δ,
    ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom
      ((TopCat.toSSet.map (TopCat.ofHom (antipodal n))).naturality (SimplexCategory.δ i).op) u

/-! ## 3. Choice-independence of the transfer -/

/-
**Choice-independence of the transfer.** For *any* continuous lift `τ` of a
singular simplex `ρ` of `RPⁿ` (`proj n ∘ τ = ρ`), the transfer of `ρ` is the sum
of the basis simplices of `τ` and of its antipode `antipodal n ∘ τ`.
-/
theorem projTransferOnSimplex_eq_of_lift (n k : ℕ)
    (ρ : singularSimplices (TopCat.of (RP n)) k) (τ : C(TopologicalSimplex k, Sphere n))
    (hτ : ⇑(proj n) ∘ ⇑τ
      = ⇑(TopCat.toSSetObjEquiv (TopCat.of (RP n)) (Opposite.op (SimplexCategory.mk k)) ρ)) :
    projTransferOnSimplex n k ρ
      = Sigma.ι (fun (_ : singularSimplices (TopCat.of (Sphere n)) k) => transferCoeff)
            ((TopCat.toSSetObjEquiv (TopCat.of (Sphere n)) (Opposite.op (SimplexCategory.mk k))).symm τ)
        + Sigma.ι (fun (_ : singularSimplices (TopCat.of (Sphere n)) k) => transferCoeff)
            ((TopCat.toSSetObjEquiv (TopCat.of (Sphere n))
                (Opposite.op (SimplexCategory.mk k))).symm ((antipodal n).comp τ)) := by
  let σc : C(TopologicalSimplex k, RP n) :=
    TopCat.toSSetObjEquiv (TopCat.of (RP n)) (Opposite.op (SimplexCategory.mk k)) ρ
  let v₀ : TopologicalSimplex k := Classical.arbitrary _
  let e : Sphere n := (proj_surjective n (σc v₀)).choose
  have he : proj n e = σc v₀ := (proj_surjective n (σc v₀)).choose_spec
  let τ₁ : C(TopologicalSimplex k, Sphere n) := projLiftSimplex σc v₀ e he
  let τ₂ : C(TopologicalSimplex k, Sphere n) :=
    projLiftSimplex σc v₀ (-e) ((proj_neg e).trans he)
  have hp : proj n (τ v₀) = proj n e := by
    rw [he]
    exact congrFun hτ v₀
  rcases proj_eq_iff.mp hp with hpos | hneg
  · have hτ_eq : τ = τ₁ := eq_projLiftSimplex σc v₀ e he hτ hpos
    rw [hτ_eq]
    have hanti : τ₂ = (antipodal n).comp τ₁ :=
      projLiftSimplex_antipodal σc v₀ e he
    change
      Sigma.ι (fun (_ : singularSimplices (TopCat.of (Sphere n)) k) => transferCoeff)
          ((TopCat.toSSetObjEquiv _ _).symm τ₁) +
        Sigma.ι (fun (_ : singularSimplices (TopCat.of (Sphere n)) k) => transferCoeff)
          ((TopCat.toSSetObjEquiv _ _).symm τ₂) = _
    rw [hanti]
  · have hτ_eq : τ = τ₂ :=
      eq_projLiftSimplex σc v₀ (-e) ((proj_neg e).trans he) hτ hneg
    rw [hτ_eq]
    have hanti : τ₂ = (antipodal n).comp τ₁ :=
      projLiftSimplex_antipodal σc v₀ e he
    have hdouble : (antipodal n).comp τ₂ = τ₁ := by
      rw [hanti, ← ContinuousMap.comp_assoc, antipodal_comp_antipodal,
        ContinuousMap.id_comp]
    change
      Sigma.ι (fun (_ : singularSimplices (TopCat.of (Sphere n)) k) => transferCoeff)
          ((TopCat.toSSetObjEquiv _ _).symm τ₁) +
        Sigma.ι (fun (_ : singularSimplices (TopCat.of (Sphere n)) k) => transferCoeff)
          ((TopCat.toSSetObjEquiv _ _).symm τ₂) = _
    rw [hdouble]
    exact add_comm _ _

/-! ## 4. The face of a lift -/

/-
**Per-face term identity.** If `τ` is a continuous lift of a singular
`(k+1)`-simplex `σ` of `RPⁿ`, then the transfer of the `i`-th face of `σ` is the
sum of the basis simplices of the `i`-th faces of `τ` and of `antipodal n ∘ τ`.
-/
theorem projTransferOnSimplex_face (n k : ℕ)
    (σ : singularSimplices (TopCat.of (RP n)) (k + 1)) (τ : C(TopologicalSimplex (k + 1), Sphere n))
    (hτ : ⇑(proj n) ∘ ⇑τ
      = ⇑(TopCat.toSSetObjEquiv (TopCat.of (RP n)) (Opposite.op (SimplexCategory.mk (k + 1))) σ))
    (i : Fin (k + 2)) :
    projTransferOnSimplex n k (faceSimplex (TopCat.of (RP n)) k i σ)
      = Sigma.ι (fun (_ : singularSimplices (TopCat.of (Sphere n)) k) => transferCoeff)
            (faceSimplex (TopCat.of (Sphere n)) k i
              ((TopCat.toSSetObjEquiv (TopCat.of (Sphere n))
                  (Opposite.op (SimplexCategory.mk (k + 1)))).symm τ))
        + Sigma.ι (fun (_ : singularSimplices (TopCat.of (Sphere n)) k) => transferCoeff)
            (faceSimplex (TopCat.of (Sphere n)) k i
              ((TopCat.toSSetObjEquiv (TopCat.of (Sphere n))
                  (Opposite.op (SimplexCategory.mk (k + 1)))).symm ((antipodal n).comp τ))) := by
  rw [ ← eq_comm ] at hτ;
  convert projTransferOnSimplex_eq_of_lift n k ( faceSimplex ( TopCat.of ( RP n ) ) k i σ ) ( TopCat.toSSetObjEquiv ( TopCat.of ( Sphere n ) ) _ ( faceSimplex ( TopCat.of ( Sphere n ) ) k i ( ( TopCat.toSSetObjEquiv ( TopCat.of ( Sphere n ) ) ( Opposite.op ( SimplexCategory.mk ( k + 1 ) ) ) ).symm τ ) ) ) _ using 1;
  simp_all +decide [ funext_iff ]
  · let u := (TopCat.toSSetObjEquiv (TopCat.of (Sphere n))
        (Opposite.op (SimplexCategory.mk (k + 1)))).symm τ
    have hantiHi : antipodalSimplexMap n (k + 1) u =
        (TopCat.toSSetObjEquiv (TopCat.of (Sphere n))
          (Opposite.op (SimplexCategory.mk (k + 1)))).symm ((antipodal n).comp τ) := by
      apply (TopCat.toSSetObjEquiv (TopCat.of (Sphere n)) _).injective
      rw [toSSetObjEquiv_antipodalSimplexMap, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply]
    have hantiLo : antipodalSimplexMap n k
          (faceSimplex (TopCat.of (Sphere n)) k i u) =
        (TopCat.toSSetObjEquiv (TopCat.of (Sphere n))
          (Opposite.op (SimplexCategory.mk k))).symm
            ((antipodal n).comp
              (TopCat.toSSetObjEquiv (TopCat.of (Sphere n))
                (Opposite.op (SimplexCategory.mk k))
                (faceSimplex (TopCat.of (Sphere n)) k i u))) := by
      apply (TopCat.toSSetObjEquiv (TopCat.of (Sphere n)) _).injective
      rw [toSSetObjEquiv_antipodalSimplexMap, Equiv.apply_symm_apply]
    calc
      _ = Sigma.ι (fun (_ : singularSimplices (TopCat.of (Sphere n)) k) => transferCoeff)
          (faceSimplex (TopCat.of (Sphere n)) k i (antipodalSimplexMap n (k + 1) u)) :=
        congrArg _ (congrArg (faceSimplex (TopCat.of (Sphere n)) k i) hantiHi.symm)
      _ = Sigma.ι (fun (_ : singularSimplices (TopCat.of (Sphere n)) k) => transferCoeff)
          (antipodalSimplexMap n k (faceSimplex (TopCat.of (Sphere n)) k i u)) :=
        congrArg _ (antipodalSimplexMap_faceSimplex n k i u).symm
      _ = _ := congrArg _ hantiLo
  · let u := (TopCat.toSSetObjEquiv (TopCat.of (Sphere n))
        (Opposite.op (SimplexCategory.mk (k + 1)))).symm τ
    have hu : projSimplexMap n (k + 1) u = σ := by
      apply (TopCat.toSSetObjEquiv (TopCat.of (RP n)) _).injective
      rw [toSSetObjEquiv_projSimplexMap, Equiv.apply_symm_apply]
      apply ContinuousMap.ext
      intro x
      exact (congrFun hτ x).symm
    have hface : projSimplexMap n k
          (faceSimplex (TopCat.of (Sphere n)) k i u) =
        faceSimplex (TopCat.of (RP n)) k i σ := by
      rw [projSimplexMap_faceSimplex, hu]
    have hc := congrArg
      (TopCat.toSSetObjEquiv (TopCat.of (RP n))
        (Opposite.op (SimplexCategory.mk k))) hface
    rw [toSSetObjEquiv_projSimplexMap] at hc
    exact congrArg DFunLike.coe hc

/-! ## 5. Boundary compatibility and the chain map -/

/-- **Boundary compatibility (degreewise).** The mod-2 transfer commutes with the
singular boundary in each degree. -/
theorem projTransfer_boundary (n k : ℕ) :
    projTransferChainDegree n (k + 1) ≫ (singularChainCx (TopCat.of (Sphere n))).d (k + 1) k
      = (singularChainCx (TopCat.of (RP n))).d (k + 1) k ≫ projTransferChainDegree n k := by
  -- By definition of `projTransferChainDegree`, we know that the composition of the transfer chain degree and the differential is equal to the differential followed by the transfer chain degree.
  apply Eq.symm; exact (by
    have := @singular_d_ι;
    have := @projTransferOnSimplex_face;
    apply CategoryTheory.Limits.Sigma.hom_ext;
    intro σ;
    rename_i h; specialize h ( TopCat.of ( RP n ) ) k σ; simp_all +decide [ ← CategoryTheory.Category.assoc ] ;
    rw [ projTransferOnSimplex_eq_of_lift ];
    rotate_left;
    exact projLiftSimplex ( TopCat.toSSetObjEquiv ( TopCat.of ( RP n ) ) ( Opposite.op ( SimplexCategory.mk ( k + 1 ) ) ) σ ) ( Classical.arbitrary _ ) ( ( proj_surjective n ( TopCat.toSSetObjEquiv ( TopCat.of ( RP n ) ) ( Opposite.op ( SimplexCategory.mk ( k + 1 ) ) ) σ ( Classical.arbitrary _ ) ) ).choose ) ( ( proj_surjective n ( TopCat.toSSetObjEquiv ( TopCat.of ( RP n ) ) ( Opposite.op ( SimplexCategory.mk ( k + 1 ) ) ) σ ( Classical.arbitrary _ ) ) ).choose_spec );
    · exact projLiftSimplex_lifts _ _ _ _;
    · simp +decide [ CategoryTheory.Preadditive.sum_comp, CategoryTheory.Preadditive.add_comp, singular_d_ι, projTransferChainDegree_ι ];
      rw [ ← Finset.sum_add_distrib ] ; congr ; ext i ; rw [ this _ _ _ _ ( projLiftSimplex_lifts _ _ _ _ ) i ] ;
  )

/-- **The mod-2 transfer chain map** of the double cover `Sⁿ → RPⁿ`. -/
def projTransferChainMap (n : ℕ) :
    singularChainCx (TopCat.of (RP n)) ⟶ singularChainCx (TopCat.of (Sphere n)) where
  f k := projTransferChainDegree n k
  comm' i j hij := by
    have hij' : j + 1 = i := hij
    subst hij'
    exact projTransfer_boundary n j

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
