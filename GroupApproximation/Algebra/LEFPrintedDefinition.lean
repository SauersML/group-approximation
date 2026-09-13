import GroupApproximation.Pestov91.LEF
import GroupApproximation.Meta.AxiomGuard

/-!
# The printed definitions of LEF rings and LEF groups

`non_mf_groups_exist.tex`, `\label{sec:chain-core}`, tex 1354–1358:

> A ring is \emph{LEF} if every finite subset admits an injective map into a finite ring preserving
> the additions and multiplications that stay in that subset, and preserving $0$ and $1$ when
> present.  A group is LEF with the analogous multiplicative definition.

The working definitions of the repository ask for more.  `Pestov91.IsLEFRing` uses a map on all of
the ring that preserves `0`, `1` and every sum and product of two elements of the subset.
`IsLEF` uses a map into a symmetric group that preserves `1` and every product of two elements of
the subset.  This file states the printed definitions verbatim and proves that they agree with the
working ones.

* `IsPrintedLEFRing` and `isPrintedLEFRing_iff : IsPrintedLEFRing A ↔ Pestov91.IsLEFRing A`;
* `IsPrintedLEFGroup` and `isPrintedLEFGroup_iff : IsPrintedLEFGroup J ↔ IsLEF J`, through
  `IsTextbookLEF`;
* closed endpoints `printedLEFRingDefinition` and `printedLEFGroupDefinition`.

From a printed model one gets a working model by applying the printed property to the subset
enlarged by `0`, `1` and the sums and products of pairs, then extending the map by a constant.
-/

namespace GroupApproximation

section Ring

/-- **LEF ring, as printed** (tex 1354–1357): every finite subset `t` admits an injective map
`φ : t → F` into a finite ring preserving the additions and multiplications that stay in `t`, and
preserving `0` and `1` when present. -/
def IsPrintedLEFRing (A : Type*) [Ring A] : Prop :=
  ∀ t : Finset A, ∃ (F : Type) (_ : Ring F) (_ : Finite F) (φ : t → F), Function.Injective φ ∧
    (∀ (a b : t) (h : (a : A) + b ∈ t), φ ⟨(a : A) + b, h⟩ = φ a + φ b) ∧
    (∀ (a b : t) (h : (a : A) * b ∈ t), φ ⟨(a : A) * b, h⟩ = φ a * φ b) ∧
    (∀ h : (0 : A) ∈ t, φ ⟨0, h⟩ = 0) ∧ (∀ h : (1 : A) ∈ t, φ ⟨1, h⟩ = 1)

variable {A : Type*} [Ring A]

/-- A printed LEF ring is LEF in the sense of `Pestov91.IsLEFRing`. -/
theorem IsPrintedLEFRing.isLEFRing (h : IsPrintedLEFRing A) : Pestov91.IsLEFRing A := by
  classical
  intro t
  obtain ⟨t', ht, hadd, hmul, h0, h1⟩ : ∃ t' : Finset A, (∀ a ∈ t, a ∈ t') ∧
      (∀ a ∈ t, ∀ b ∈ t, a + b ∈ t') ∧ (∀ a ∈ t, ∀ b ∈ t, a * b ∈ t') ∧ (0 : A) ∈ t' ∧
      (1 : A) ∈ t' :=
    ⟨insert 0 (insert 1 (t ∪ (t ×ˢ t).image (fun p : A × A => p.1 + p.2) ∪
        (t ×ˢ t).image (fun p : A × A => p.1 * p.2))),
      fun a ha => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_union_left _ (Finset.mem_union_left _ ha))),
      fun a ha b hb => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_image_of_mem (fun p : A × A => p.1 + p.2)
            (Finset.mem_product.2 ⟨ha, hb⟩ : (a, b) ∈ t ×ˢ t))))),
      fun a ha b hb => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_union_right _ (Finset.mem_image_of_mem (fun p : A × A => p.1 * p.2)
          (Finset.mem_product.2 ⟨ha, hb⟩ : (a, b) ∈ t ×ˢ t)))),
      Finset.mem_insert_self _ _,
      Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
  obtain ⟨F, _, _, φ, hφ, hφadd, hφmul, hφ0, hφ1⟩ := h t'
  obtain ⟨ψ, hψ⟩ : ∃ ψ : A → F, ∀ (a : A) (ha : a ∈ t'), ψ a = φ ⟨a, ha⟩ :=
    ⟨fun a => if ha : a ∈ t' then φ ⟨a, ha⟩ else 0, fun _ ha => dif_pos ha⟩
  refine ⟨F, inferInstance, inferInstance, ψ, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    rw [hψ a (ht a (Finset.mem_coe.1 ha)), hψ b (ht b (Finset.mem_coe.1 hb))] at hab
    exact congrArg Subtype.val (hφ hab)
  · rw [hψ 0 h0]
    exact hφ0 h0
  · rw [hψ 1 h1]
    exact hφ1 h1
  · intro a ha b hb
    refine ⟨?_, ?_⟩
    · rw [hψ _ (hadd a ha b hb), hψ a (ht a ha), hψ b (ht b hb)]
      exact hφadd ⟨a, ht a ha⟩ ⟨b, ht b hb⟩ (hadd a ha b hb)
    · rw [hψ _ (hmul a ha b hb), hψ a (ht a ha), hψ b (ht b hb)]
      exact hφmul ⟨a, ht a ha⟩ ⟨b, ht b hb⟩ (hmul a ha b hb)

/-- A ring that is LEF in the sense of `Pestov91.IsLEFRing` is a printed LEF ring. -/
theorem isPrintedLEFRing_of_isLEFRing (h : Pestov91.IsLEFRing A) : IsPrintedLEFRing A := by
  intro t
  obtain ⟨F, _, _, φ, hφ, h0, h1, hops⟩ := h t
  refine ⟨F, inferInstance, inferInstance, fun a => φ a, ?_, fun a b _ => (hops a a.2 b b.2).1,
    fun a b _ => (hops a a.2 b b.2).2, fun _ => h0, fun _ => h1⟩
  intro a b hab
  exact Subtype.ext (hφ (Finset.mem_coe.2 a.2) (Finset.mem_coe.2 b.2) hab)

theorem isPrintedLEFRing_iff (A : Type*) [Ring A] : IsPrintedLEFRing A ↔ Pestov91.IsLEFRing A :=
  ⟨IsPrintedLEFRing.isLEFRing, isPrintedLEFRing_of_isLEFRing⟩

end Ring

section Group

/-- **LEF group, as printed** (tex 1357–1358, "the analogous multiplicative definition"): every
finite subset `t` admits an injective map `φ : t → H` into a finite group preserving the
multiplications that stay in `t`, and preserving `1` when present. -/
def IsPrintedLEFGroup (J : Type*) [Group J] : Prop :=
  ∀ t : Finset J, ∃ (H : Type) (_ : Group H) (_ : Finite H) (φ : t → H), Function.Injective φ ∧
    (∀ (a b : t) (h : (a : J) * b ∈ t), φ ⟨(a : J) * b, h⟩ = φ a * φ b) ∧
    (∀ h : (1 : J) ∈ t, φ ⟨1, h⟩ = 1)

variable {J : Type*} [Group J]

/-- A printed LEF group is textbook LEF. -/
theorem IsPrintedLEFGroup.isTextbookLEF (h : IsPrintedLEFGroup J) : IsTextbookLEF J := by
  classical
  intro s
  obtain ⟨H, _, _, φ, hφ, hφmul, -⟩ := h s
  obtain ⟨ψ, hψ⟩ : ∃ ψ : J → H, ∀ (x : J) (hx : x ∈ s), ψ x = φ ⟨x, hx⟩ :=
    ⟨fun x => if hx : x ∈ s then φ ⟨x, hx⟩ else 1, fun _ hx => dif_pos hx⟩
  let M : FiniteGroupModel :=
    { groupCarrier := H
      group := inferInstance
      fintype := Fintype.ofFinite H
      decidableEq := Classical.decEq H }
  refine ⟨M, ψ, ?_, ?_⟩
  · intro x hx y hy hxy
    rw [hψ x (Finset.mem_coe.1 hx), hψ y (Finset.mem_coe.1 hy)] at hxy
    exact congrArg Subtype.val (hφ hxy)
  · intro x hx y hy hxy
    rw [hψ _ hxy, hψ x hx, hψ y hy]
    exact hφmul ⟨x, hx⟩ ⟨y, hy⟩ hxy

/-- A textbook LEF group is a printed LEF group; preserving `1` is automatic in a group. -/
theorem isPrintedLEFGroup_of_isTextbookLEF (h : IsTextbookLEF J) : IsPrintedLEFGroup J := by
  intro t
  obtain ⟨M, f, hf, hmul⟩ := h t
  refine ⟨M.groupCarrier, inferInstance, inferInstance, fun a => f a, ?_,
    fun a b hab => hmul a a.2 b b.2 hab, fun h1 => ?_⟩
  · intro a b hab
    exact Subtype.ext (hf (Finset.mem_coe.2 a.2) (Finset.mem_coe.2 b.2) hab)
  · have hm := hmul 1 h1 1 h1 (by rw [one_mul]; exact h1)
    rw [one_mul] at hm
    exact mul_eq_left.1 hm.symm

theorem isPrintedLEFGroup_iff_isTextbookLEF (J : Type*) [Group J] :
    IsPrintedLEFGroup J ↔ IsTextbookLEF J :=
  ⟨IsPrintedLEFGroup.isTextbookLEF, isPrintedLEFGroup_of_isTextbookLEF⟩

theorem isPrintedLEFGroup_iff (J : Type*) [Group J] : IsPrintedLEFGroup J ↔ IsLEF J :=
  (isPrintedLEFGroup_iff_isTextbookLEF J).trans (isLEF_iff_textbook J).symm

end Group

/-- **tex 1354–1357**: "A ring is \emph{LEF} if every finite subset admits an injective map into a
finite ring preserving the additions and multiplications that stay in that subset, and preserving
$0$ and $1$ when present."  The printed definition `IsPrintedLEFRing` agrees with the working
definition `Pestov91.IsLEFRing`. -/
def PrintedLEFRingDefinition : Prop :=
  ∀ (A : Type) [Ring A], IsPrintedLEFRing A ↔ Pestov91.IsLEFRing A

theorem printedLEFRingDefinition : PrintedLEFRingDefinition := by
  intro A _
  exact isPrintedLEFRing_iff A

/-- **tex 1357–1358**: "A group is LEF with the analogous multiplicative definition."  The printed
definition `IsPrintedLEFGroup` agrees with the working definition `IsLEF`. -/
def PrintedLEFGroupDefinition : Prop :=
  ∀ (J : Type) [Group J], IsPrintedLEFGroup J ↔ IsLEF J

theorem printedLEFGroupDefinition : PrintedLEFGroupDefinition := by
  intro J _
  exact isPrintedLEFGroup_iff J

end GroupApproximation

open GroupApproximation

#audit_closed_axioms GroupApproximation.printedLEFRingDefinition
#audit_closed_axioms GroupApproximation.printedLEFGroupDefinition
