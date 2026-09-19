import GroupApproximation.Sofic.LEF
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Order.Filter.Ultrafilter.Defs
import Mathlib.Order.Filter.Finite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Group.Prod

/-!
# `lem:nn`: algebraic ultraproducts of finite groups are LEF, and LEF passes to `Γ × ℤ`

`simple_kazhdan_sofic_group.tex`, proof of `lem:nn` (l.489–525):

> Let Γ = {γ_1, γ_2, …} be a countable LEF group; replacing Γ by Γ × ℤ, we may assume that Γ is infinite. […]
> In the algebraic ultraproduct over ω of the symmetric groups of these sets […]
> Finitely many equations and inequalities that hold in the ultraproduct hold in some coordinate, so Δ is LEF […]

This file builds the algebraic ultraproduct `∏_ω G i` as the quotient of the product group by the sequences that are
trivial `ω`-almost everywhere (`Ultraproduct`), and proves the LEF clause along the printed route: for a finite test set,
the finitely many products and inequalities between chosen representatives hold `ω`-almost everywhere, hence in some
coordinate, which is then a finite model (`isTextbookLEF_ultraproduct`). Every subgroup of it, such as `Δ`, is LEF
(`isLEF_subgroup_ultraproduct`). The replacement of `Γ` by `Γ × ℤ` uses `isTextbookLEF_prod`.
-/

namespace GroupApproximation.Full.SK09

open Filter

section Construction

variable {ι : Type} (ω : Ultrafilter ι) (G : ι → Type) [∀ i, Group (G i)]

/-- The sequences that are trivial `ω`-almost everywhere. -/
def nullSubgroup : Subgroup (∀ i, G i) where
  carrier := {g | ∀ᶠ i in (ω : Filter ι), g i = 1}
  mul_mem' := by
    intro a b ha hb
    have ha' : ∀ᶠ i in (ω : Filter ι), a i = 1 := ha
    have hb' : ∀ᶠ i in (ω : Filter ι), b i = 1 := hb
    show ∀ᶠ i in (ω : Filter ι), (a * b) i = 1
    exact (ha'.and hb').mono fun i h => by
      show (a * b) i = 1
      rw [Pi.mul_apply, h.1, h.2, one_mul]
  one_mem' := by
    show ∀ᶠ i in (ω : Filter ι), (1 : ∀ i, G i) i = 1
    exact Filter.Eventually.of_forall fun _ => rfl
  inv_mem' := by
    intro a ha
    have ha' : ∀ᶠ i in (ω : Filter ι), a i = 1 := ha
    show ∀ᶠ i in (ω : Filter ι), a⁻¹ i = 1
    exact ha'.mono fun i h => by
      show a⁻¹ i = 1
      rw [Pi.inv_apply, h, inv_one]

theorem mem_nullSubgroup {g : ∀ i, G i} :
    g ∈ nullSubgroup ω G ↔ ∀ᶠ i in (ω : Filter ι), g i = 1 :=
  Iff.rfl

instance nullSubgroup_normal : (nullSubgroup ω G).Normal where
  conj_mem n hn g := by
    have hn' : ∀ᶠ i in (ω : Filter ι), n i = 1 := (mem_nullSubgroup ω G).1 hn
    refine (mem_nullSubgroup ω G).2 ?_
    exact hn'.mono fun i h => by
      show (g * n * g⁻¹) i = 1
      rw [Pi.mul_apply, Pi.mul_apply, Pi.inv_apply, h, mul_one, mul_inv_cancel]

/-- **The algebraic ultraproduct** `∏_ω G i` (`lem:nn`, simple_kazhdan_sofic_group.tex l.517–518): the product group
modulo the `ω`-almost everywhere trivial sequences. -/
abbrev Ultraproduct : Type :=
  (∀ i, G i) ⧸ nullSubgroup ω G

/-- Two sequences have the same class if and only if they agree `ω`-almost everywhere. -/
theorem mk_eq_mk_iff {g h : ∀ i, G i} :
    (QuotientGroup.mk g : Ultraproduct ω G) = QuotientGroup.mk h ↔
      ∀ᶠ i in (ω : Filter ι), g i = h i := by
  rw [QuotientGroup.eq, mem_nullSubgroup]
  refine Filter.eventually_congr (Filter.Eventually.of_forall fun i => ?_)
  show (g i)⁻¹ * h i = 1 ↔ g i = h i
  exact inv_mul_eq_one

/-- A chosen representative of a class. -/
noncomputable def out (x : Ultraproduct ω G) : ∀ i, G i :=
  Function.surjInv
    (QuotientGroup.mk_surjective : Function.Surjective
      (QuotientGroup.mk : (∀ i, G i) → Ultraproduct ω G)) x

theorem mk_out (x : Ultraproduct ω G) :
    (QuotientGroup.mk (out ω G x) : Ultraproduct ω G) = x :=
  Function.surjInv_eq _ x

end Construction

section Finite

variable {ι : Type} (ω : Ultrafilter ι) (G : ι → Type) [∀ i, Group (G i)] [∀ i, Finite (G i)]

/-- **Finitely many equations and inequalities that hold in the ultraproduct hold in some coordinate, so it is LEF**
(`lem:nn`, simple_kazhdan_sofic_group.tex l.523–524), in the printed sense of partial embeddings into finite groups that
preserve the products staying in the test set. -/
theorem isTextbookLEF_ultraproduct : IsTextbookLEF (Ultraproduct ω G) := by
  classical
  intro s
  have hmul : ∀ x y : Ultraproduct ω G,
      ∀ᶠ i in (ω : Filter ι), out ω G (x * y) i = (out ω G x * out ω G y) i := by
    intro x y
    refine (mk_eq_mk_iff ω G (g := out ω G (x * y)) (h := out ω G x * out ω G y)).1 ?_
    rw [mk_out, QuotientGroup.mk_mul, mk_out, mk_out]
  have hne : ∀ x y : Ultraproduct ω G, x ≠ y →
      ∀ᶠ i in (ω : Filter ι), ¬ out ω G x i = out ω G y i := by
    intro x y hxy
    refine Ultrafilter.eventually_not.2 fun h => hxy ?_
    exact ((mk_out ω G x).symm.trans ((mk_eq_mk_iff ω G (g := out ω G x) (h := out ω G y)).2 h)).trans (mk_out ω G y)
  have hall : ∀ᶠ i in (ω : Filter ι), ∀ x ∈ s, ∀ y ∈ s,
      out ω G (x * y) i = (out ω G x * out ω G y) i ∧
        (x ≠ y → ¬ out ω G x i = out ω G y i) := by
    refine (Filter.eventually_all_finset s).2 fun x _ =>
      (Filter.eventually_all_finset s).2 fun y _ => ?_
    by_cases hxy : x = y
    · exact (hmul x y).mono fun i h => ⟨h, fun hn => absurd hxy hn⟩
    · exact ((hmul x y).and (hne x y hxy)).mono fun i h => ⟨h.1, fun _ => h.2⟩
  obtain ⟨i, hi⟩ := hall.exists
  refine ⟨⟨G i, inferInstance, Fintype.ofFinite (G i), Classical.decEq (G i)⟩, fun x => out ω G x i, ?_, ?_⟩
  · intro x hx y hy hxy
    exact Classical.byContradiction fun hn => (hi x hx y hy).2 hn hxy
  · intro x hx y hy _
    exact (hi x hx y hy).1

/-- The algebraic ultraproduct of finite groups is LEF, in the project's `Perm (Fin n)` convention. -/
theorem isLEF_ultraproduct : IsLEF (Ultraproduct ω G) :=
  (isLEF_iff_textbook _).2 (isTextbookLEF_ultraproduct ω G)

/-- **Every subgroup of an algebraic ultraproduct of finite groups is LEF** (`lem:nn`, simple_kazhdan_sofic_group.tex
l.523–524, applied to `Δ`). -/
theorem isLEF_subgroup_ultraproduct (H : Subgroup (Ultraproduct ω G)) : IsLEF H :=
  isLEF_of_injective H.subtype H.subtype_injective (isLEF_ultraproduct ω G)

end Finite

/-- **LEF passes to products** (`lem:nn`, simple_kazhdan_sofic_group.tex l.495–497, the replacement of `Γ` by `Γ × ℤ`):
models of the factors on the two projections of a test set form a model of the product on that test set. -/
theorem isTextbookLEF_prod {A B : Type} [Group A] [Group B] (hA : IsTextbookLEF A)
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

end GroupApproximation.Full.SK09
