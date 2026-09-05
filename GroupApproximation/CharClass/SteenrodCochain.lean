import GroupApproximation.CharClass.SteenrodCutCancel
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CochainCupLeibniz

/-!
# Steenrod's cup-`i` products on singular cochains

This file defines `⌣ᵢ` on the vendored singular cochains and records everything
about it that does not need the coboundary formula: bilinearity, naturality,
the behaviour of a face under deletion of a vertex, and the coboundary of a
single face evaluation.

## The two design decisions

* **`faceVal` is total.**  `faceVal a α σ A` evaluates the `a`-cochain `α` on
  the face of `σ` spanned by the vertex subset `A`, and returns `0` when `A`
  has the wrong size.  So a sum over cut sets never carries a cardinality
  hypothesis, and no face map ever appears with a proof argument that would
  block `rw`.
* **The output degree is free.**  `cochainCupI i a b n α β` is a cochain of
  degree `n` for *every* `n`.  Since `|cutU S| + |cutV S| = (n+1) + (i+1)`, the
  two cardinality tests inside `faceVal` can succeed simultaneously only when
  `a + b = n + i`; in every other degree the cochain is `0`
  (`cochainCupI_of_degree_ne`).  This is what removes all degree casts from the
  coboundary formula in `SteenrodCoboundary.lean`.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial SimplexCategory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass

noncomputable section

/-! ## 1. Restricting a singular simplex along a face map -/

/-- The face of a singular `n`-simplex cut out by a map of simplices. -/
def restrictSimplex {X : TopCat.{0}} {a n : ℕ}
    (f : (⦋a⦌ : SimplexCategory) ⟶ ⦋n⦌) (σ : singularSimplices X n) :
    singularSimplices X a :=
  (TopCat.toSSet.obj X).map f.op σ

theorem restrictSimplex_comp {X : TopCat.{0}} {c a n : ℕ}
    (g : (⦋c⦌ : SimplexCategory) ⟶ ⦋a⦌) (f : (⦋a⦌ : SimplexCategory) ⟶ ⦋n⦌)
    (σ : singularSimplices X n) :
    restrictSimplex g (restrictSimplex f σ) = restrictSimplex (g ≫ f) σ := by
  unfold restrictSimplex
  rw [← Functor.map_comp_apply, ← op_comp]

theorem faceSimplex_eq_restrictSimplex (X : TopCat.{0}) (n : ℕ) (k : Fin (n + 2))
    (σ : singularSimplices X (n + 1)) :
    faceSimplex X n k σ = restrictSimplex (SimplexCategory.δ k) σ :=
  rfl

theorem restrictSimplex_naturality {X Y : TopCat.{0}} (h : X ⟶ Y) {a n : ℕ}
    (f : (⦋a⦌ : SimplexCategory) ⟶ ⦋n⦌) (σ : singularSimplices X n) :
    (TopCat.toSSet.map h).app (Opposite.op (⦋a⦌ : SimplexCategory)) (restrictSimplex f σ)
      = restrictSimplex f
          ((TopCat.toSSet.map h).app (Opposite.op (⦋n⦌ : SimplexCategory)) σ) := by
  simpa only [restrictSimplex, ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom ((TopCat.toSSet.map h).naturality f.op) σ

/-! ## 2. A cochain from a function on simplices -/

/-- The cochain taking the prescribed value on each singular simplex. -/
def cochainOfFun {R : Type} [CommRing R] {X : TopCat.{0}} (n : ℕ)
    (F : singularSimplices X n → R) : singularCochainGroup R X n :=
  Sigma.desc (fun σ => ModuleCat.ofHom ((F σ) • (LinearMap.id : R →ₗ[R] R)))

@[simp]
theorem cochainEval_cochainOfFun {R : Type} [CommRing R] {X : TopCat.{0}} (n : ℕ)
    (F : singularSimplices X n → R) (τ : singularSimplices X n) :
    cochainEval n (cochainOfFun n F) τ = F τ := by
  show (cochainOfFun n F).hom _ = _
  unfold cochainOfFun
  have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (Sigma.ι_desc (fun σ : singularSimplices X n =>
      ModuleCat.ofHom ((F σ) • (LinearMap.id : R →ₗ[R] R))) τ)) (1 : R)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  convert h using 1
  all_goals simp
  all_goals rfl

/-! ## 3. Evaluating a cochain on a subset of the vertices -/

/-- **The total face evaluation.**  `faceVal a α σ A` is the value of the
`a`-cochain `α` on the face of `σ` spanned by `A`, and `0` if `A` does not have
`a + 1` vertices. -/
def faceVal {R : Type} [CommRing R] {X : TopCat.{0}} (a : ℕ) {n : ℕ}
    (α : singularCochainGroup R X a) (σ : singularSimplices X n)
    (A : Finset (Fin (n + 1))) : R :=
  if h : A.card = a + 1 then cochainEval a α (restrictSimplex (faceOfFinset A h) σ) else 0

theorem faceVal_of_card {R : Type} [CommRing R] {X : TopCat.{0}} (a : ℕ) {n : ℕ}
    (α : singularCochainGroup R X a) (σ : singularSimplices X n)
    {A : Finset (Fin (n + 1))} (h : A.card = a + 1) :
    faceVal a α σ A = cochainEval a α (restrictSimplex (faceOfFinset A h) σ) :=
  dif_pos h

theorem faceVal_of_card_ne {R : Type} [CommRing R] {X : TopCat.{0}} {a n : ℕ}
    (α : singularCochainGroup R X a) (σ : singularSimplices X n)
    {A : Finset (Fin (n + 1))} (h : ¬ A.card = a + 1) :
    faceVal a α σ A = 0 :=
  dif_neg h

theorem faceVal_add {R : Type} [CommRing R] {X : TopCat.{0}} (a : ℕ) {n : ℕ}
    (α α' : singularCochainGroup R X a) (σ : singularSimplices X n)
    (A : Finset (Fin (n + 1))) :
    faceVal a (α + α') σ A = faceVal a α σ A + faceVal a α' σ A := by
  unfold faceVal
  by_cases h : A.card = a + 1
  · rw [dif_pos h, dif_pos h, dif_pos h, cochainEval_add]
  · rw [dif_neg h, dif_neg h, dif_neg h, add_zero]

theorem faceVal_zero {R : Type} [CommRing R] {X : TopCat.{0}} (a : ℕ) {n : ℕ}
    (σ : singularSimplices X n) (A : Finset (Fin (n + 1))) :
    faceVal a (0 : singularCochainGroup R X a) σ A = 0 := by
  unfold faceVal
  by_cases h : A.card = a + 1
  · rw [dif_pos h, cochainEval_zero]
  · rw [dif_neg h]

theorem faceVal_smul {R : Type} [CommRing R] {X : TopCat.{0}} (a : ℕ) {n : ℕ} (s : R)
    (α : singularCochainGroup R X a) (σ : singularSimplices X n)
    (A : Finset (Fin (n + 1))) :
    faceVal a (s • α) σ A = s * faceVal a α σ A := by
  unfold faceVal
  by_cases h : A.card = a + 1
  · rw [dif_pos h, dif_pos h, cochainEval_smul]
  · rw [dif_neg h, dif_neg h, mul_zero]

theorem faceVal_pullback {R : Type} [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y) (a : ℕ) {n : ℕ}
    (α : singularCochainGroup R Y a) (σ : singularSimplices X n)
    (A : Finset (Fin (n + 1))) :
    faceVal a (cochainPullback f a α) σ A
      = faceVal a α ((TopCat.toSSet.map f).app (Opposite.op (⦋n⦌ : SimplexCategory)) σ) A := by
  unfold faceVal
  by_cases h : A.card = a + 1
  · rw [dif_pos h, dif_pos h, cochainPullback_eval, restrictSimplex_naturality]
  · rw [dif_neg h, dif_neg h]

/-- **Deleting a vertex of the ambient simplex.**  Evaluating on the face `A` of
a boundary face of `τ` is evaluating on the corresponding face of `τ`. -/
theorem faceVal_faceSimplex {R : Type} [CommRing R] {X : TopCat.{0}} (a n : ℕ)
    (α : singularCochainGroup R X a) (k : Fin (n + 2))
    (τ : singularSimplices X (n + 1)) (A : Finset (Fin (n + 1))) :
    faceVal a α (faceSimplex X n k τ) A
      = faceVal a α τ (A.map (Fin.succAboveOrderEmb k).toEmbedding) := by
  by_cases h : A.card = a + 1
  · have h' : (A.map (Fin.succAboveOrderEmb k).toEmbedding).card = a + 1 := by
      rw [Finset.card_map]; exact h
    rw [faceVal_of_card a α _ h, faceVal_of_card a α τ h']
    congr 1
    rw [faceSimplex_eq_restrictSimplex, restrictSimplex_comp, faceOfFinset_comp_delta]
  · have h' : ¬ (A.map (Fin.succAboveOrderEmb k).toEmbedding).card = a + 1 := by
      rw [Finset.card_map]; exact h
    rw [faceVal_of_card_ne α _ h, faceVal_of_card_ne α τ h']

/-- **The coboundary through a face.**  Over `ZMod 2` the value of `δα` on a
face is the sum of the values of `α` on the faces obtained by deleting one of
its vertices.  Both sides vanish when `A` has the wrong size. -/
theorem faceVal_coboundary {X : TopCat.{0}} (a n : ℕ)
    (α : singularCochainGroup (ZMod 2) X a) (τ : singularSimplices X (n + 1))
    (A : Finset (Fin (n + 2))) :
    faceVal (a + 1) (cochainCoboundary (ZMod 2) X a α) τ A
      = ∑ c ∈ A, faceVal a α τ (A.erase c) := by
  by_cases h : A.card = a + 1 + 1
  · rw [faceVal_of_card (a + 1) (cochainCoboundary (ZMod 2) X a α) τ h, cochainCoboundary_eval]
    have hterm : ∀ i : Fin (a + 2),
        (-1 : ZMod 2) ^ (i : ℕ)
            * cochainEval a α (faceSimplex X a i (restrictSimplex (faceOfFinset A h) τ))
          = faceVal a α τ (A.erase (A.orderEmbOfFin h i)) := by
      intro i
      rw [neg_one_pow_zmod2, one_mul]
      have hcard : (A.erase (A.orderEmbOfFin h i)).card = a + 1 := by
        have := Finset.card_erase_of_mem (A.orderEmbOfFin_mem h i)
        omega
      rw [faceVal_of_card a α τ hcard]
      congr 1
      rw [faceSimplex_eq_restrictSimplex, restrictSimplex_comp, delta_comp_faceOfFinset]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i)]
    refine Finset.sum_bij (fun (i : Fin (a + 2)) _ => A.orderEmbOfFin h i) ?_ ?_ ?_ ?_
    · intro i _
      exact A.orderEmbOfFin_mem h i
    · intro i₁ _ i₂ _ heq
      exact (A.orderEmbOfFin h).injective heq
    · intro c hc
      have hrange : c ∈ Set.range (A.orderEmbOfFin h) := by
        rw [Finset.range_orderEmbOfFin]
        exact Finset.mem_coe.2 hc
      obtain ⟨i, hi⟩ := hrange
      exact ⟨i, Finset.mem_univ i, hi⟩
    · intro i _
      rfl
  · rw [faceVal_of_card_ne (cochainCoboundary (ZMod 2) X a α) τ h]
    refine (Finset.sum_eq_zero ?_).symm
    intro c hc
    refine faceVal_of_card_ne α τ ?_
    have hce := Finset.card_erase_of_mem hc
    have hpos : 1 ≤ A.card := Finset.card_pos.2 ⟨c, hc⟩
    omega

/-! ## 4. The cup-`i` product -/

/-- **Steenrod's cup-`i` product.**  The sum, over all `(i+1)`-element sets of
cut points of the output simplex, of the value of `α` on the left alternating
family times the value of `β` on the right one.  Terms of the wrong bidegree
vanish because `faceVal` does. -/
def cochainCupI {R : Type} [CommRing R] {X : TopCat.{0}} (i a b n : ℕ)
    (α : singularCochainGroup R X a) (β : singularCochainGroup R X b) :
    singularCochainGroup R X n :=
  cochainOfFun n
    (fun σ => ∑ S ∈ cutIndex (i + 1) n, faceVal a α σ (cutU S) * faceVal b β σ (cutV S))

@[simp]
theorem cochainCupI_eval {R : Type} [CommRing R] {X : TopCat.{0}} (i a b n : ℕ)
    (α : singularCochainGroup R X a) (β : singularCochainGroup R X b)
    (σ : singularSimplices X n) :
    cochainEval n (cochainCupI i a b n α β) σ
      = ∑ S ∈ cutIndex (i + 1) n, faceVal a α σ (cutU S) * faceVal b β σ (cutV S) :=
  cochainEval_cochainOfFun n _ σ

/-- **Degree bookkeeping is automatic.**  Outside the bidegree `a + b = n + i`
the cup-`i` product is the zero cochain, because the two families of an `i`-cut
of an `n`-simplex have `n + i + 2` vertices between them. -/
theorem cochainCupI_of_degree_ne {R : Type} [CommRing R] {X : TopCat.{0}} (i a b n : ℕ)
    (hab : ¬ a + b = n + i)
    (α : singularCochainGroup R X a) (β : singularCochainGroup R X b) :
    cochainCupI i a b n α β = 0 := by
  apply cochain_ext
  intro σ
  rw [cochainCupI_eval, cochainEval_zero]
  refine Finset.sum_eq_zero fun S hS => ?_
  by_cases hU : (cutU S).card = a + 1
  · refine mul_eq_zero_of_right _ (faceVal_of_card_ne β σ ?_)
    have hcount := cutU_card_add_cutV_card S
    have hcard := card_of_mem_cutIndex hS
    omega
  · exact mul_eq_zero_of_left (faceVal_of_card_ne α σ hU) _

theorem cochainCupI_add_left {R : Type} [CommRing R] {X : TopCat.{0}} (i a b n : ℕ)
    (α α' : singularCochainGroup R X a) (β : singularCochainGroup R X b) :
    cochainCupI i a b n (α + α') β = cochainCupI i a b n α β + cochainCupI i a b n α' β := by
  apply cochain_ext
  intro σ
  rw [cochainEval_add, cochainCupI_eval, cochainCupI_eval, cochainCupI_eval,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [faceVal_add]
  ring

theorem cochainCupI_add_right {R : Type} [CommRing R] {X : TopCat.{0}} (i a b n : ℕ)
    (α : singularCochainGroup R X a) (β β' : singularCochainGroup R X b) :
    cochainCupI i a b n α (β + β') = cochainCupI i a b n α β + cochainCupI i a b n α β' := by
  apply cochain_ext
  intro σ
  rw [cochainEval_add, cochainCupI_eval, cochainCupI_eval, cochainCupI_eval,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [faceVal_add]
  ring

@[simp]
theorem cochainCupI_zero_left {R : Type} [CommRing R] {X : TopCat.{0}} (i a b n : ℕ)
    (β : singularCochainGroup R X b) :
    cochainCupI i a b n (0 : singularCochainGroup R X a) β = 0 := by
  apply cochain_ext
  intro σ
  rw [cochainCupI_eval, cochainEval_zero]
  refine Finset.sum_eq_zero fun S _ => ?_
  rw [faceVal_zero, zero_mul]

@[simp]
theorem cochainCupI_zero_right {R : Type} [CommRing R] {X : TopCat.{0}} (i a b n : ℕ)
    (α : singularCochainGroup R X a) :
    cochainCupI i a b n α (0 : singularCochainGroup R X b) = 0 := by
  apply cochain_ext
  intro σ
  rw [cochainCupI_eval, cochainEval_zero]
  refine Finset.sum_eq_zero fun S _ => ?_
  rw [faceVal_zero, mul_zero]

/-- **Naturality of the cup-`i` product.** -/
theorem cochainCupI_naturality {R : Type} [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y)
    (i a b n : ℕ) (α : singularCochainGroup R Y a) (β : singularCochainGroup R Y b) :
    cochainPullback f n (cochainCupI i a b n α β)
      = cochainCupI i a b n (cochainPullback f a α) (cochainPullback f b β) := by
  apply cochain_ext
  intro σ
  rw [cochainPullback_eval, cochainCupI_eval, cochainCupI_eval]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [faceVal_pullback, faceVal_pullback]

end

end CharClass
end GroupApproximation
