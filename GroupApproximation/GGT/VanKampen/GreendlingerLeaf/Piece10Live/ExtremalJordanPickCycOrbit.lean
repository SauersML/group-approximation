import Mathlib.GroupTheory.Perm.Cycle.Type
import GroupApproximation.Meta.AxiomGuard

/-!
# Counting the orbits of a permutation through a class map

Lane gl-p10-44.  A finite-set lemma for `ExtremalJordanPickCountParityCyclesStatement`.

**Statement** (`extremalJordanPickCyc_card_image`).  Let `f` be a permutation of a finite type,
`s` a finset containing the support of `f`, and `φ` a map that identifies two points of `s`
exactly when they lie in one cycle of `f`.  Then

  `#(s.image φ) + #(supp f) = #s + #(cycleType f)`,

so `#(s.image φ) = #s - #(supp f) + #(cycleType f)`: the number of `f`-orbits on `s`.

**Proof.**  Split `s` into the fixed points `A = s \ supp f` and the support.
1. `φ` is injective on `A`: two fixed points in one cycle are equal.
2. The images `φ(A)` and `φ(supp f)` are disjoint: a point in one cycle with a fixed point is
   itself fixed.
3. On `supp f`, the map `φ` has the same kernel as `x ↦ cycleOf f x`
   (`extremalJordanPickCyc_cycleOf_eq_iff`).  Two maps with the same kernel on a finset have
   images of the same size (`extremalJordanPickCyc_card_image_congr`, by induction on the finset).
4. `(supp f).image (cycleOf f)` is `cycleFactorsFinset f` (`extremalJordanPickCyc_image_cycleOf`),
   and its size is `#(cycleType f)`, since `cycleType f` is that finset mapped by
   `card ∘ support`.
So `#(s.image φ) = #A + #(cycleType f)` and `#A + #(supp f) = #s`.

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

section CycOrbit

variable {α β γ : Type*}

/-- **Kernel transfer**: two maps that identify the same pairs of a finset have images of the same
size. -/
theorem extremalJordanPickCyc_card_image_congr [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (φ : α → β) (ψ : α → γ) (s : Finset α) :
    (∀ x ∈ s, ∀ y ∈ s, (φ x = φ y ↔ ψ x = ψ y)) → (s.image φ).card = (s.image ψ).card := by
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | insert a s _ ih =>
    intro h
    have h' : ∀ x ∈ s, ∀ y ∈ s, (φ x = φ y ↔ ψ x = ψ y) := fun x hx y hy =>
      h x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)
    have key : φ a ∈ s.image φ ↔ ψ a ∈ s.image ψ := by
      rw [Finset.mem_image, Finset.mem_image]
      constructor
      · rintro ⟨b, hb, hba⟩
        exact ⟨b, hb, (h b (Finset.mem_insert_of_mem hb) a (Finset.mem_insert_self a s)).mp hba⟩
      · rintro ⟨b, hb, hba⟩
        exact ⟨b, hb, (h b (Finset.mem_insert_of_mem hb) a (Finset.mem_insert_self a s)).mpr hba⟩
    rw [Finset.image_insert, Finset.image_insert]
    by_cases hφ : φ a ∈ s.image φ
    · rw [Finset.card_insert_of_mem hφ, Finset.card_insert_of_mem (key.mp hφ), ih h']
    · rw [Finset.card_insert_of_notMem hφ, Finset.card_insert_of_notMem (mt key.mpr hφ), ih h']

/-- On the support, two points have the same cycle factor exactly when they lie in one cycle. -/
theorem extremalJordanPickCyc_cycleOf_eq_iff [DecidableEq α] [Fintype α] (f : Equiv.Perm α)
    {x y : α} (hx : x ∈ f.support) :
    f.cycleOf x = f.cycleOf y ↔ f.SameCycle x y := by
  constructor
  · intro h
    have hxx : x ∈ (f.cycleOf x).support :=
      Equiv.Perm.mem_support_cycleOf_iff.mpr ⟨Equiv.Perm.SameCycle.refl f x, hx⟩
    rw [h] at hxx
    exact (Equiv.Perm.mem_support_cycleOf_iff.mp hxx).1.symm
  · intro h
    exact h.cycleOf_eq

/-- The cycle factors of the points of the support are the cycle factors of the permutation. -/
theorem extremalJordanPickCyc_image_cycleOf [DecidableEq α] [Fintype α] (f : Equiv.Perm α) :
    f.support.image f.cycleOf = f.cycleFactorsFinset := by
  ext p
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hx
  · intro hp
    obtain ⟨a, ha⟩ := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hp).1.nonempty_support
    exact ⟨a, Finset.le_iff_subset.mp (Equiv.Perm.mem_cycleFactorsFinset_support_le hp) ha,
      (Equiv.Perm.cycle_is_cycleOf ha hp).symm⟩

/-- The number of cycles is the number of cycle factors. -/
theorem extremalJordanPickCyc_card_cycleType [DecidableEq α] [Fintype α] (f : Equiv.Perm α) :
    f.cycleType.card = f.cycleFactorsFinset.card := by
  rw [Equiv.Perm.cycleType_def, Multiset.card_map, Finset.card_def]

/-- **The orbit count**: a map on `s ⊇ supp f` whose kernel is `SameCycle f` takes
`#s - #(supp f) + #(cycleType f)` values. -/
theorem extremalJordanPickCyc_card_image [DecidableEq α] [Fintype α] [DecidableEq β]
    (f : Equiv.Perm α) (s : Finset α) (φ : α → β) (hs : f.support ⊆ s)
    (hφ : ∀ x ∈ s, ∀ y ∈ s, (φ x = φ y ↔ f.SameCycle x y)) :
    (s.image φ).card + f.support.card = s.card + f.cycleType.card := by
  have hA : (s \ f.support).card + f.support.card = s.card :=
    Finset.card_sdiff_add_card_eq_card hs
  have hinj : Set.InjOn φ ↑(s \ f.support) := by
    intro x hx y hy hxy
    have hx' := Finset.mem_sdiff.mp (Finset.mem_coe.mp hx)
    have hy' := Finset.mem_sdiff.mp (Finset.mem_coe.mp hy)
    exact ((hφ x hx'.1 y hy'.1).mp hxy).eq_of_left (Equiv.Perm.notMem_support.mp hx'.2)
  have hS : (f.support.image φ).card = f.cycleType.card := by
    rw [extremalJordanPickCyc_card_cycleType, ← extremalJordanPickCyc_image_cycleOf]
    refine extremalJordanPickCyc_card_image_congr φ f.cycleOf f.support ?_
    intro x hx y hy
    rw [hφ x (hs hx) y (hs hy), extremalJordanPickCyc_cycleOf_eq_iff f hx]
  have hdisj : Disjoint ((s \ f.support).image φ) (f.support.image φ) := by
    rw [Finset.disjoint_left]
    intro b hb hb'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hb'
    have hx' := Finset.mem_sdiff.mp hx
    have hc := (hφ y (hs hy) x hx'.1).mp hyx
    exact Equiv.Perm.mem_support.mp hy
      (hc.apply_eq_self_iff.mpr (Equiv.Perm.notMem_support.mp hx'.2))
  have hsplit : s.image φ = (s \ f.support).image φ ∪ f.support.image φ := by
    rw [← Finset.image_union, Finset.sdiff_union_of_subset hs]
  rw [hsplit, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj]
  omega

end CycOrbit

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCyc_card_image_congr
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCyc_cycleOf_eq_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCyc_image_cycleOf
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCyc_card_cycleType
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCyc_card_image
