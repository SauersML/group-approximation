import GroupApproximation.Sofic.LEF
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Order.Filter.Ultrafilter.Defs
import Mathlib.Order.Filter.Finite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Group.Prod

/-!
# Algebraic ultraproducts of groups are LEF

`simple_kazhdan_sofic_group.tex` at origin/main 37551fd93, proof of `cor:lef` and `cor:host`, uses the algebraic
ultraproduct over a nonprincipal ultrafilter `ω` of finite symmetric groups (tex l.348–351) and closes the paragraph with

> Finitely many products and inequalities in the ultraproduct hold in some coordinate, so Δ is infinite, finitely
> generated and LEF.                                                                              (tex l.355–356)

This file builds the algebraic ultraproduct `∏_ω G i` of a family of groups as the quotient of the product group by the
normal subgroup of the sequences that are trivial `ω`-almost everywhere, and proves the LEF clause of that sentence along
the printed route. For a finite test set, the finitely many products and inequalities between chosen representatives hold
`ω`-almost everywhere, so in one coordinate, and that coordinate is a finite model (`isTextbookLEF_ultraproduct`). Every
subgroup of such an ultraproduct is then LEF (`isLEF_subgroup_ultraproduct`).

It also proves that LEF passes to products (`isTextbookLEF_prod`). The replacement of `Γ` by `Γ × ℤ` at tex l.333 uses it.
-/

namespace GroupApproximation

open Filter

namespace AlgebraicUltraproduct

universe u v

section Construction

variable {ι : Type u} (ω : Ultrafilter ι) (G : ι → Type v) [∀ i, Group (G i)]

/-- The sequences that are trivial `ω`-almost everywhere. -/
def nullSubgroup : Subgroup (∀ i, G i) where
  carrier := {g | ∀ᶠ i in (ω : Filter ι), g i = 1}
  mul_mem' := by
    intro a b ha hb
    show ∀ᶠ i in (ω : Filter ι), (a * b) i = 1
    have ha' : ∀ᶠ i in (ω : Filter ι), a i = 1 := ha
    have hb' : ∀ᶠ i in (ω : Filter ι), b i = 1 := hb
    exact (ha'.and hb').mono fun i h => by simp [h.1, h.2]
  one_mem' := by
    show ∀ᶠ i in (ω : Filter ι), (1 : ∀ i, G i) i = 1
    exact Filter.Eventually.of_forall fun _ => rfl
  inv_mem' := by
    intro a ha
    show ∀ᶠ i in (ω : Filter ι), a⁻¹ i = 1
    have ha' : ∀ᶠ i in (ω : Filter ι), a i = 1 := ha
    exact ha'.mono fun i h => by simp [h]

theorem mem_nullSubgroup {g : ∀ i, G i} :
    g ∈ nullSubgroup ω G ↔ ∀ᶠ i in (ω : Filter ι), g i = 1 :=
  Iff.rfl

instance nullSubgroup_normal : (nullSubgroup ω G).Normal where
  conj_mem n hn g := by
    rw [mem_nullSubgroup] at hn ⊢
    exact hn.mono fun i h => by simp [h]

/-- The algebraic ultraproduct `∏_ω G i`: the product group modulo the `ω`-almost everywhere trivial sequences. -/
abbrev Ultraproduct : Type (max u v) :=
  (∀ i, G i) ⧸ nullSubgroup ω G

/-- Two sequences have the same class if and only if they agree `ω`-almost everywhere. -/
theorem mk_eq_mk_iff {g h : ∀ i, G i} :
    (QuotientGroup.mk g : Ultraproduct ω G) = QuotientGroup.mk h ↔
      ∀ᶠ i in (ω : Filter ι), g i = h i := by
  rw [QuotientGroup.eq, mem_nullSubgroup]
  simp only [Pi.mul_apply, Pi.inv_apply, inv_mul_eq_one]

/-- A chosen representative of a class. -/
noncomputable def out (x : Ultraproduct ω G) : ∀ i, G i :=
  Function.surjInv
    (QuotientGroup.mk_surjective : Function.Surjective
      (QuotientGroup.mk : (∀ i, G i) → Ultraproduct ω G)) x

@[simp] theorem mk_out (x : Ultraproduct ω G) :
    (QuotientGroup.mk (out ω G x) : Ultraproduct ω G) = x :=
  Function.surjInv_eq _ x

end Construction

section Finite

variable {ι : Type u} (ω : Ultrafilter ι) (G : ι → Type) [∀ i, Group (G i)] [∀ i, Finite (G i)]

/-- **Finitely many products and inequalities in the ultraproduct hold in some coordinate** (tex l.355–356): an
algebraic ultraproduct of finite groups is LEF, in the printed sense of partial embeddings preserving the products that
stay in the test set. -/
theorem isTextbookLEF_ultraproduct : IsTextbookLEF (Ultraproduct ω G) := by
  classical
  intro s
  have hmul : ∀ x y : Ultraproduct ω G,
      ∀ᶠ i in (ω : Filter ι), out ω G (x * y) i = out ω G x i * out ω G y i := by
    intro x y
    refine (mk_eq_mk_iff ω G).1 ?_
    rw [mk_out]
    exact (congrArg₂ (· * ·) (mk_out ω G x) (mk_out ω G y)).symm
  have hne : ∀ x y : Ultraproduct ω G, x ≠ y →
      ∀ᶠ i in (ω : Filter ι), ¬ out ω G x i = out ω G y i := by
    intro x y hxy
    refine Ultrafilter.eventually_not.2 fun h => hxy ?_
    rw [← mk_out ω G x, ← mk_out ω G y]
    exact (mk_eq_mk_iff ω G).2 h
  have hall : ∀ᶠ i in (ω : Filter ι), ∀ x ∈ s, ∀ y ∈ s,
      out ω G (x * y) i = out ω G x i * out ω G y i ∧
        (x ≠ y → ¬ out ω G x i = out ω G y i) := by
    refine (Filter.eventually_all_finset s).2 fun x _ =>
      (Filter.eventually_all_finset s).2 fun y _ => ?_
    by_cases hxy : x = y
    · exact (hmul x y).mono fun i h => ⟨h, fun hn => absurd hxy hn⟩
    · exact ((hmul x y).and (hne x y hxy)).mono fun i h => ⟨h.1, fun _ => h.2⟩
  obtain ⟨i, hi⟩ := hall.exists
  letI : Fintype (G i) := Fintype.ofFinite (G i)
  refine ⟨⟨G i, inferInstance, inferInstance, inferInstance⟩, fun x => out ω G x i, ?_, ?_⟩
  · intro x hx y hy hxy
    by_contra hn
    exact (hi x hx y hy).2 hn hxy
  · intro x hx y hy _
    exact (hi x hx y hy).1

/-- The algebraic ultraproduct of finite groups is LEF, in the project's `Perm (Fin n)` convention. -/
theorem isLEF_ultraproduct : IsLEF (Ultraproduct ω G) :=
  (isLEF_iff_textbook _).2 (isTextbookLEF_ultraproduct ω G)

/-- Every subgroup of an algebraic ultraproduct of finite groups is LEF. -/
theorem isLEF_subgroup_ultraproduct (H : Subgroup (Ultraproduct ω G)) : IsLEF H :=
  isLEF_of_injective H.subtype Subtype.val_injective (isLEF_ultraproduct ω G)

end Finite

end AlgebraicUltraproduct

/-- **LEF passes to products**: models of the factors on the two projections of a test set form a model of the
product on that test set. -/
theorem isTextbookLEF_prod {A B : Type*} [Group A] [Group B] (hA : IsTextbookLEF A)
    (hB : IsTextbookLEF B) : IsTextbookLEF (A × B) := by
  classical
  intro s
  obtain ⟨H₁, f₁, hf₁, hm₁⟩ := hA (s.image Prod.fst)
  obtain ⟨H₂, f₂, hf₂, hm₂⟩ := hB (s.image Prod.snd)
  refine ⟨⟨H₁ × H₂, inferInstance, inferInstance, inferInstance⟩,
    fun x => (f₁ x.1, f₂ x.2), ?_, ?_⟩
  · intro x hx y hy hxy
    have h₁ : f₁ x.1 = f₁ y.1 := congrArg Prod.fst hxy
    have h₂ : f₂ x.2 = f₂ y.2 := congrArg Prod.snd hxy
    exact Prod.ext
      (hf₁ (Finset.mem_image_of_mem Prod.fst hx) (Finset.mem_image_of_mem Prod.fst hy) h₁)
      (hf₂ (Finset.mem_image_of_mem Prod.snd hx) (Finset.mem_image_of_mem Prod.snd hy) h₂)
  · intro x hx y hy hxy
    exact Prod.ext
      (hm₁ x.1 (Finset.mem_image_of_mem Prod.fst hx) y.1 (Finset.mem_image_of_mem Prod.fst hy)
        (Finset.mem_image_of_mem Prod.fst hxy))
      (hm₂ x.2 (Finset.mem_image_of_mem Prod.snd hx) y.2 (Finset.mem_image_of_mem Prod.snd hy)
        (Finset.mem_image_of_mem Prod.snd hxy))

end GroupApproximation
