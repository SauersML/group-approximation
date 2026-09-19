import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFCharacterization
import GroupApproximation.Sofic.LEF
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic

/-!
# The restricted direct sum in the proof of `cor:host`

`simple_kazhdan_sofic_group.tex` at origin/main 696c4b602, proof of `cor:host` (tex l.430–434):

> For the second statement of Corollary `cor:host`, apply the first to the restricted direct sum of
> representatives of countably many isomorphism classes of finitely generated LEF groups, which is
> a countable LEF group, as finite subsets lie in finite products.

* `restrictedSum H`: the finitely supported elements of `∀ j, H j`.
* `countable_restrictedSum`: it is countable when `J` and every `H j` are countable. Each element is
  determined by its graph on its support, which is a finite subset of the countable type `Σ j, H j`.
* `isLEF_restrictedSum`: it is LEF when every `H j` is. A finite subset of the sum lies in the
  product over the finitely many indices where its elements are nontrivial, and there the product
  of finite models is a finite model.
* `restrictedSumSingle`: `H j` embeds in the sum.
* `restrictedSumLEFStatement : RestrictedSumLEFStatement`: the piece consumed by
  `printedLEFFamilyHost_of_pieces` and `printedRecursivelyPresentedLEFHost_of_pieces`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

section RestrictedSum

variable {J : Type} (H : J → Type) [∀ j, Group (H j)]

/-- **The restricted direct sum**: the elements of `∀ j, H j` with finite support. -/
def restrictedSum : Subgroup (∀ j, H j) where
  carrier := {f | {j | f j ≠ 1}.Finite}
  one_mem' := by
    change {j | (1 : ∀ j, H j) j ≠ 1}.Finite
    simp
  mul_mem' := by
    intro a b ha hb
    change {j | a j ≠ 1}.Finite at ha
    change {j | b j ≠ 1}.Finite at hb
    change {j | (a * b) j ≠ 1}.Finite
    refine (ha.union hb).subset fun j hj => ?_
    simp only [Set.mem_union, Set.mem_setOf_eq] at hj ⊢
    by_contra h
    simp only [not_or, ne_eq, not_not] at h
    exact hj (by simp [h.1, h.2])
  inv_mem' := by
    intro a ha
    change {j | a j ≠ 1}.Finite at ha
    change {j | a⁻¹ j ≠ 1}.Finite
    refine ha.subset fun j hj => ?_
    simpa using hj

theorem mem_restrictedSum {f : ∀ j, H j} : f ∈ restrictedSum H ↔ {j | f j ≠ 1}.Finite :=
  Iff.rfl

/-- The graph of `f` on its support. -/
def supportGraph (f : ∀ j, H j) : Set (Σ j, H j) :=
  {p | f p.1 = p.2 ∧ p.2 ≠ 1}

theorem mem_supportGraph {f : ∀ j, H j} {p : Σ j, H j} :
    p ∈ supportGraph H f ↔ f p.1 = p.2 ∧ p.2 ≠ 1 :=
  Iff.rfl

theorem supportGraph_finite {f : ∀ j, H j} (hf : {j | f j ≠ 1}.Finite) :
    (supportGraph H f).Finite := by
  refine (hf.image fun j => (⟨j, f j⟩ : Σ j, H j)).subset ?_
  rintro ⟨j, x⟩ hp
  obtain ⟨hjx, hx⟩ := (mem_supportGraph H).mp hp
  dsimp only at hjx hx
  subst hjx
  exact Set.mem_image_of_mem (fun j => (⟨j, f j⟩ : Σ j, H j)) hx

theorem supportGraph_injective : Function.Injective (supportGraph H) := by
  intro f g hfg
  funext j
  by_cases hf : f j = 1
  · by_cases hg : g j = 1
    · rw [hf, hg]
    · have hmem : (⟨j, g j⟩ : Σ j, H j) ∈ supportGraph H f := by
        rw [hfg]
        exact (mem_supportGraph H).mpr ⟨rfl, hg⟩
      exact absurd (((mem_supportGraph H).mp hmem).1.symm.trans hf) hg
  · have hmem : (⟨j, f j⟩ : Σ j, H j) ∈ supportGraph H g := by
      rw [← hfg]
      exact (mem_supportGraph H).mpr ⟨rfl, hf⟩
    exact ((mem_supportGraph H).mp hmem).1.symm

/-- **The restricted direct sum of countably many countable groups is countable.** -/
theorem countable_restrictedSum [Countable J] [∀ j, Countable (H j)] :
    Countable ↥(restrictedSum H) := by
  have hc : {t : Set (Σ j, H j) | t.Finite ∧ t ⊆ Set.univ}.Countable :=
    Set.countable_setOf_finite_subset Set.countable_univ
  haveI := hc.to_subtype
  let code : ↥(restrictedSum H) → ↥{t : Set (Σ j, H j) | t.Finite ∧ t ⊆ Set.univ} :=
    fun f => ⟨supportGraph H f.1,
      ⟨supportGraph_finite H ((mem_restrictedSum H).mp f.2), Set.subset_univ _⟩⟩
  refine Function.Injective.countable (f := code) ?_
  intro f g hfg
  exact Subtype.ext (supportGraph_injective H (congrArg Subtype.val hfg))

/-- **The restricted direct sum of LEF groups is LEF**, "as finite subsets lie in finite
products". -/
theorem isLEF_restrictedSum (hH : ∀ j, IsLEF (H j)) : IsLEF ↥(restrictedSum H) := by
  classical
  rw [isLEF_iff_textbook]
  intro s
  let F : Set J := ⋃ p ∈ (s : Set ↥(restrictedSum H)), {j | p.1 j ≠ 1}
  have hF : F.Finite :=
    Set.Finite.biUnion s.finite_toSet fun p _ => (mem_restrictedSum H).mp p.2
  choose M g hginj hgmul using
    fun j => (isLEF_iff_textbook (H j)).mp (hH j) (s.image fun p => p.1 j)
  let P : FiniteGroupModel :=
    { groupCarrier := ∀ k : ↥hF.toFinset, (M k.1).groupCarrier
      group := inferInstance
      fintype := inferInstance
      decidableEq := inferInstance }
  refine ⟨P, fun p k => g k.1 (p.1 k.1), ?_, ?_⟩
  · intro p hp q hq hpq
    have hp' : p ∈ s := Finset.mem_coe.mp hp
    have hq' : q ∈ s := Finset.mem_coe.mp hq
    apply Subtype.ext
    funext j
    by_cases hj : j ∈ F
    · have hk : j ∈ hF.toFinset := hF.mem_toFinset.mpr hj
      have h1 : g j (p.1 j) = g j (q.1 j) := congrFun hpq ⟨j, hk⟩
      exact hginj j (Finset.mem_coe.mpr (Finset.mem_image_of_mem (fun p => p.1 j) hp'))
        (Finset.mem_coe.mpr (Finset.mem_image_of_mem (fun p => p.1 j) hq')) h1
    · have hpj : p.1 j = 1 := by
        by_contra h
        exact hj (Set.mem_biUnion (Finset.mem_coe.mpr hp') h)
      have hqj : q.1 j = 1 := by
        by_contra h
        exact hj (Set.mem_biUnion (Finset.mem_coe.mpr hq') h)
      rw [hpj, hqj]
  · intro x hx y hy hxy
    funext k
    exact hgmul k.1 (x.1 k.1) (Finset.mem_image_of_mem (fun p => p.1 k.1) hx) (y.1 k.1)
      (Finset.mem_image_of_mem (fun p => p.1 k.1) hy)
      (Finset.mem_image_of_mem (fun p => p.1 k.1) hxy)

/-- The inclusion of `H j` in the restricted direct sum. -/
def restrictedSumSingle [DecidableEq J] (j : J) : H j →* ↥(restrictedSum H) where
  toFun x := ⟨Pi.mulSingle j x, (mem_restrictedSum H).mpr ((Set.finite_singleton j).subset
    fun k hk => Set.mem_singleton_iff.mpr (by
      by_contra hkj
      exact hk (Pi.mulSingle_eq_of_ne hkj x)))⟩
  map_one' := Subtype.ext (Pi.mulSingle_one j)
  map_mul' x y := Subtype.ext (Pi.mulSingle_mul j x y)

theorem restrictedSumSingle_injective [DecidableEq J] (j : J) :
    Function.Injective (restrictedSumSingle H j) := by
  intro x y hxy
  exact Pi.mulSingle_injective j (congrArg Subtype.val hxy)

end RestrictedSum

/-- **The restricted direct sum** (tex l.430–434): countably many countable LEF groups embed in
one countable LEF group. -/
theorem restrictedSumLEFStatement : RestrictedSumLEFStatement := by
  intro J _ H _ hcount hlef
  classical
  haveI : ∀ j, Countable (H j) := hcount
  exact ⟨↥(restrictedSum H), inferInstance, countable_restrictedSum H, isLEF_restrictedSum H hlef,
    fun j => ⟨restrictedSumSingle H j, restrictedSumSingle_injective H j⟩⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.countable_restrictedSum
#audit_axioms GroupApproximation.SimpleKazhdanSofic.isLEF_restrictedSum
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.restrictedSumLEFStatement

end SimpleKazhdanSofic
end GroupApproximation
