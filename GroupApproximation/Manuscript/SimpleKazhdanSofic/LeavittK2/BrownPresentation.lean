import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown's presentation `Π = ⟨J, T | T k T⁻¹ = η k, T h T = h T h⟩`

Khanh (arXiv:2609.08428v1), proof of Theorem 5.1 (`thm:raw-criterion`), display
`eq:borel-presentation`:

> Let `τ = (12)` and `h = (23)` be permutation matrices, so that `h ∈ J`, and put
> `η(k) = τ k τ⁻¹`. [...]
> `Π = ⟨J, T | T k T⁻¹ = η(k) for k ∈ K,  T h T = h T h⟩`.
> This notation includes every multiplication relation in `J`. [...]
> The relation `T² = 1` follows from the displayed presentation: since `h² = 1`, the braid
> relation implies `(hT) h (hT)⁻¹ = T`. [...]
> the projection `p : Π → G`, given by `p(j) = j` and `p(T) = τ` [...]

Everything here is abstract: `G` is any group, `K ≤ J` are subgroups, `η : K →* K` and `h ∈ J`.

* `brownRels`, `BrownPresentation`: the presented group on the generators `J ⊕ {T}`.
* `brownJ_mul`, `brownJ_one`, `brownT_conj`, `brownT_braid`: the defining relations in `Π`.
* `brownT_mul_self`: `T² = 1` whenever `h² = 1` (the derivation printed in the tex).
* `conjEta`: the automorphism `k ↦ τ k τ⁻¹` of `K` when `τ` normalizes `K`.
* `brownMap`: the projection `p : Π →* G` with `p(j) = j`, `p(T) = τ`, which exists as soon as
  `η` is conjugation by `τ` and `τ h τ = h τ h` in `G`.

Surjectivity of `p` (from connectivity of the complex and edge-transitivity) is in
`LeavittK2.BrownWords`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

variable {G : Type*} [Group G]

section Presentation

variable (J K : Subgroup G) (hKJ : K ≤ J) (η : K →* K) (h : J)

/-- The inclusion `K → J`. -/
def brownKIncl (k : K) : J := ⟨k, hKJ k.2⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.brownKIncl

/-- The relators of Brown's presentation on the generators `J ⊕ {T}`: the multiplication table
of `J`, the edge relations `T k T⁻¹ η(k)⁻¹` for `k ∈ K`, and the triangle relator
`T h T (h T h)⁻¹`. -/
def brownRels : Set (FreeGroup (↥J ⊕ Unit)) :=
  Set.range (fun ab : J × J => FreeGroup.of (Sum.inl ab.1) * FreeGroup.of (Sum.inl ab.2) *
      (FreeGroup.of (Sum.inl (ab.1 * ab.2)))⁻¹) ∪
    Set.range (fun k : K => FreeGroup.of (Sum.inr ()) * FreeGroup.of (Sum.inl (brownKIncl J K hKJ k)) *
      (FreeGroup.of (Sum.inr ()))⁻¹ * (FreeGroup.of (Sum.inl (brownKIncl J K hKJ (η k))))⁻¹) ∪
    {FreeGroup.of (Sum.inr ()) * FreeGroup.of (Sum.inl h) * FreeGroup.of (Sum.inr ()) *
      (FreeGroup.of (Sum.inl h) * FreeGroup.of (Sum.inr ()) * FreeGroup.of (Sum.inl h))⁻¹}

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.brownRels

/-- Brown's group `Π = ⟨J, T | T k T⁻¹ = η(k) (k ∈ K), T h T = h T h⟩`, including the
multiplication relations of `J`. -/
abbrev BrownPresentation : Type _ := PresentedGroup (brownRels J K hKJ η h)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownPresentation

/-- The generator of `Π` attached to `j ∈ J`. -/
def brownJ (j : J) : BrownPresentation J K hKJ η h := PresentedGroup.of (Sum.inl j)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.brownJ

/-- The extra generator `T` of `Π`. -/
def brownT : BrownPresentation J K hKJ η h := PresentedGroup.of (Sum.inr ())

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.brownT

/-- The multiplication relations of `J` hold in `Π`. -/
theorem brownJ_mul (a b : J) :
    brownJ J K hKJ η h a * brownJ J K hKJ η h b = brownJ J K hKJ η h (a * b) := by
  have hr : FreeGroup.of (Sum.inl a) * FreeGroup.of (Sum.inl b) *
      (FreeGroup.of (Sum.inl (a * b)))⁻¹ ∈ brownRels J K hKJ η h := by
    unfold brownRels
    exact Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_range_self (a, b)))
  have hmk := PresentedGroup.mk_eq_mk_of_mul_inv_mem hr
  simp only [map_mul] at hmk
  exact hmk

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.brownJ_mul

/-- `brownJ 1 = 1` in `Π`. -/
theorem brownJ_one : brownJ J K hKJ η h 1 = 1 := by
  have hmk := brownJ_mul J K hKJ η h 1 1
  rw [mul_one] at hmk
  exact mul_left_cancel (hmk.trans (mul_one _).symm)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.brownJ_one

/-- The edge relations `T k T⁻¹ = η(k)` for `k ∈ K`. -/
theorem brownT_conj (k : K) :
    brownT J K hKJ η h * brownJ J K hKJ η h (brownKIncl J K hKJ k) * (brownT J K hKJ η h)⁻¹ =
      brownJ J K hKJ η h (brownKIncl J K hKJ (η k)) := by
  have hr : FreeGroup.of (Sum.inr ()) * FreeGroup.of (Sum.inl (brownKIncl J K hKJ k)) *
      (FreeGroup.of (Sum.inr ()))⁻¹ * (FreeGroup.of (Sum.inl (brownKIncl J K hKJ (η k))))⁻¹ ∈
      brownRels J K hKJ η h := by
    unfold brownRels
    exact Set.mem_union_left _ (Set.mem_union_right _ (Set.mem_range_self k))
  have hmk := PresentedGroup.mk_eq_mk_of_mul_inv_mem hr
  simp only [map_mul, map_inv] at hmk
  exact hmk

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.brownT_conj

/-- The triangle relation `T h T = h T h`. -/
theorem brownT_braid :
    brownT J K hKJ η h * brownJ J K hKJ η h h * brownT J K hKJ η h =
      brownJ J K hKJ η h h * brownT J K hKJ η h * brownJ J K hKJ η h h := by
  have hr : FreeGroup.of (Sum.inr ()) * FreeGroup.of (Sum.inl h) * FreeGroup.of (Sum.inr ()) *
      (FreeGroup.of (Sum.inl h) * FreeGroup.of (Sum.inr ()) * FreeGroup.of (Sum.inl h))⁻¹ ∈
      brownRels J K hKJ η h := by
    unfold brownRels
    exact Set.mem_union_right _ (Set.mem_singleton _)
  have hmk := PresentedGroup.mk_eq_mk_of_mul_inv_mem hr
  simp only [map_mul] at hmk
  exact hmk

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.brownT_braid

end Presentation

/-- In any group, a braid relation `t y t = y t y` with `y² = 1` forces `t² = 1`, because
`(y t) y (y t)⁻¹ = t`. -/
theorem mul_self_eq_one_of_braid {P : Type*} [Group P] {t y : P} (hb : t * y * t = y * t * y)
    (hy : y * y = 1) : t * t = 1 := by
  have ht : t = y * t * y * t⁻¹ * y⁻¹ := by
    rw [← hb]
    group
  calc t * t = (y * t * y * t⁻¹ * y⁻¹) * (y * t * y * t⁻¹ * y⁻¹) := by rw [← ht]
    _ = y * t * (y * y) * t⁻¹ * y⁻¹ := by group
    _ = 1 := by rw [hy]; group

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.mul_self_eq_one_of_braid

/-- `T² = 1` in `Π` when `h² = 1` (tex: "The relation `T² = 1` follows from the displayed
presentation"). -/
theorem brownT_mul_self (J K : Subgroup G) (hKJ : K ≤ J) (η : K →* K) (h : J) (hh : h * h = 1) :
    brownT J K hKJ η h * brownT J K hKJ η h = 1 :=
  mul_self_eq_one_of_braid (brownT_braid J K hKJ η h)
    (by rw [brownJ_mul, hh, brownJ_one])

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.brownT_mul_self

/-- Conjugation by an element `τ` normalizing `K`, as an endomorphism of `K`
(`η(k) = τ k τ⁻¹`). -/
def conjEta (K : Subgroup G) (τ : G) (hτ : ∀ k ∈ K, τ * k * τ⁻¹ ∈ K) : K →* K where
  toFun k := ⟨τ * k * τ⁻¹, hτ k k.2⟩
  map_one' := by
    ext
    simp
  map_mul' a b := by
    ext
    simp [mul_assoc]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.conjEta

theorem conjEta_apply (K : Subgroup G) (τ : G) (hτ : ∀ k ∈ K, τ * k * τ⁻¹ ∈ K) (k : K) :
    ((conjEta K τ hτ k : K) : G) = τ * k * τ⁻¹ :=
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.conjEta_apply

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
