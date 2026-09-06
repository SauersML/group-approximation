import GroupApproximation.CharClass.LerayHirschUnion
import GroupApproximation.CharClass.BundleBasic

/-!
# The diagonal cover of a projection-valued bundle

A projection of trace one cannot have all its diagonal entries vanish, so the sets
where the `i`-th diagonal entry is nonzero are an open cover of the base, indexed
by the index type itself.  That cover is *finite for free*, because the index type
is, so this route needs no compactness of the base at all.

It is also the cover the chart trivialisation is stated over: `cc-bundle`'s
`projPlusOneHomeoCPOne` takes exactly the hypothesis that the `i`-th diagonal
entry does not vanish.  So this is the cover the bootstrap actually uses, rather
than the determinant loci, which are a different family and would need a
comparison.

## Main declarations

* `diagOpen` — the open set where the `i`-th diagonal entry is nonzero.
* `exists_mem_diagOpen` — **they cover**, because the trace is one.
* `lerayHirschGraded_of_diagCover` — **Leray–Hirsch from the diagonal cover**, with
  no compactness hypothesis.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory TopologicalSpace

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] {P : TopCat.{0}}

/-- The open set of the base where the `i`-th diagonal entry does not vanish. -/
def diagOpen (p : Bundle X ι) (i : ι) : Opens (TopCat.of X) :=
  ⟨{x : X | p x i i ≠ 0},
    (p.continuous.matrix_elem i i).isOpen_preimage {0}ᶜ isOpen_compl_singleton⟩

@[simp] theorem mem_diagOpen {p : Bundle X ι} {i : ι} {x : X} :
    x ∈ diagOpen p i ↔ p x i i ≠ 0 := Iff.rfl

/-- **The diagonal sets cover the base.**  A projection of trace one cannot have
all its diagonal entries vanish. -/
theorem exists_mem_diagOpen (p : Bundle X ι) (hp : ∀ x, (p x).trace = 1) (x : X) :
    ∃ i : ι, x ∈ diagOpen p i := by
  by_contra h
  have hall : ∀ i : ι, p x i i = 0 := by
    intro i
    by_contra hne
    exact h ⟨i, hne⟩
  have htr : (p x).trace = 0 := by
    show (∑ i, p x i i) = 0
    exact Finset.sum_eq_zero fun i _ => hall i
  rw [hp x] at htr
  exact one_ne_zero htr

/-- **Leray–Hirsch from the diagonal cover.**  No compactness: the index type is
finite, so the cover is finite for free. -/
theorem lerayHirschGraded_of_diagCover [Nonempty ι] (p : Bundle X ι)
    (hp : ∀ x, (p x).trace = 1) (f : P ⟶ TopCat.of X) (ξ : Hmod2 P 2) (r : ℕ)
    (hLH : ∀ (i : ι) (W : Opens (TopCat.of X)), LHOver f ξ r (diagOpen p i ⊓ W)) :
    LerayHirschGraded f ξ r := by
  classical
  refine lerayHirschGraded_of_finite_cover f ξ r
    (fun A => ∃ (i : ι) (W : Opens (TopCat.of X)), A = diagOpen p i ⊓ W)
    ?_ ?_ ((Finset.univ : Finset ι).toList.map (fun i => diagOpen p i)) ?_ ⊥ ?_ ?_
  · rintro A W ⟨i, W', rfl⟩
    exact ⟨i, W' ⊓ W, by rw [inf_assoc]⟩
  · rintro A ⟨i, W, rfl⟩
    exact hLH i W
  · intro B hB
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hB
    exact ⟨i, ⊤, by rw [inf_top_eq]⟩
  · exact ⟨Classical.arbitrary ι, ⊥, by rw [inf_bot_eq]⟩
  · refine foldr_sup_eq_top _ _ fun x => ?_
    obtain ⟨i, hi⟩ := exists_mem_diagOpen p hp x
    exact Or.inr ⟨diagOpen p i,
      List.mem_map.mpr ⟨i, Finset.mem_toList.mpr (Finset.mem_univ i), rfl⟩, hi⟩

end

end LH
end CharClass
end GroupApproximation
