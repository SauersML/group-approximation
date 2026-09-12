import GroupApproximation.Sofic.BoundedConjProductAlgebra
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Toward bounded normal generation: what one commutator with `s` produces

`Sofic/SoficEnvelopeSimplicity.lean` carries the one external input of the
Elek--Szabó envelope theorem (proof-ledger row `SO.17`) as the spelled-out
premise `hBNG`, **bounded normal generation of finite alternating groups**:

> for every `δ > 0` there are `K` and `M` such that whenever `Ω` is a finite
> set with `|Ω| ≥ M` and `s` is an even permutation of `Ω` with
> `|supp s| ≥ δ|Ω|`, every even permutation of `Ω` is a product of at most `K`
> conjugates of `s` and `s⁻¹`.

**This file does not prove that premise, and nothing here may be read as
proving it.**  What it proves is the *production* half of the elementary route
to it, unconditionally and with explicit constants: exactly which elements are
reachable by a single commutator with `s`, and how large that supply is as a
function of `|supp s|` alone.  The consumption half — how many such elements a
given even permutation needs — is stated at the end of this docstring and is
not formalized anywhere in this repository.

## What is proved

* `exists_independent_subset` — every permutation `s` has a subset `A` of its
  support with `s A ∩ A = ∅` and `|supp s| ≤ 3|A|`.  The proof is the greedy
  one, and it is what replaces the cycle decomposition: take `A` of maximum
  cardinality among the independent subsets of the support; then every point
  of the support is in `A`, in `sA`, or in `s⁻¹A`, since otherwise it could be
  added to `A`.  No cycle type, no parity, no `cycleFactorsFinset`.
* `cycleType_commutator_of_independent` — if `supp g ⊆ A` for such an `A`,
  then `s g s⁻¹` and `g⁻¹` have disjoint supports, so the commutator
  `s g s⁻¹ g⁻¹` has cycle type `g.cycleType + g.cycleType`: it is two disjoint
  copies of `g`.  This is where the independence of `A` is spent, and it is
  spent only here.
* `isBoundedConjProduct_two_of_cycleType_eq` — hence **every** permutation
  whose cycle type is a doubled one, `T + T` with `T` realized by a
  permutation supported in `A`, is a product of at most `2` conjugates of
  `s^{±1}`.  Position is free: `Sofic.BoundedConjProductAlgebra`'s
  `isBoundedConjProduct_conj` moves a produced element anywhere in its
  conjugacy class at no cost in length, and `isConj_iff_cycleType_eq` says
  that class is exactly the cycle type.

The length `2` is uniform in everything: in `|Ω|`, in `δ`, in `g`, and in the
target.  That is the whole point — a bound depending on the index is what the
metric ultraproduct cannot absorb, as the module docstring of
`Sofic/SoficEnvelopeSimplicity.lean` records.

## What remains, stated precisely

Write `m = |supp s| ≥ δ|Ω|`.  The three results above say that the reachable
set at length `2` contains every element of cycle type `T + T` with
`|T| ≤ m/3`.  Bounded normal generation follows from exactly one more
statement:

> every even permutation of `Ω` is a product of at most `C·|Ω|/m + C` elements,
> each of cycle type `T + T` for some partition `T` of at most `m/3` points.

and the classical route to it factors a permutation as a product of two
involutions (the two reflections of each cycle), splits each involution into
blocks of at most `m/6` disjoint transpositions — an involution with `2k`
disjoint transpositions has cycle type `2^k + 2^k`, so each block is reachable
— and corrects the parity of the two leftover blocks by the identity
`(ab)(cd) = [(ab)(uv)]·[(uv)(cd)]`, which is a product of two reachable
elements whenever four spare points exist.  The missing Lean input is the
factorization into two involutions; mathlib at the pin has no such result, and
proving it needs the cycle decomposition this file was arranged to avoid.

Until that lands, `hBNG` stays a premise, `SO.17` stays open, and no
declaration of `Sofic/SoficEnvelopeSimplicity.lean` may carry a badge.
-/

namespace GroupApproximation
namespace AlternatingBoundedNormalGeneration

open BoundedConjProductAlgebra SoficEnvelopeSimplicity
open scoped commutatorElement

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-! ## A large independent set inside the support -/

/-- **The greedy independent set.**  Every permutation `s` has a subset `A` of
its support with `s x ∉ A` for every `x ∈ A`, of cardinality at least a third
of the support.

The bound is the greedy one and needs no structure theory: choose `A`
independent of maximum cardinality; a support point outside `A` cannot be
added, so it is the image or the preimage of a point of `A`, and therefore
`supp s ⊆ A ∪ sA ∪ s⁻¹A`. -/
theorem exists_independent_subset (s : Equiv.Perm Y) :
    ∃ A : Finset Y, A ⊆ s.support ∧ (∀ x ∈ A, s x ∉ A) ∧
      s.support.card ≤ 3 * A.card := by
  have hne : (s.support.powerset.filter
      (fun B : Finset Y ↦ ∀ x ∈ B, s x ∉ B)).Nonempty := by
    refine ⟨∅, ?_⟩
    simp
  obtain ⟨A, hAF, hAmax⟩ :=
    (s.support.powerset.filter
      (fun B : Finset Y ↦ ∀ x ∈ B, s x ∉ B)).exists_max_image Finset.card hne
  rw [Finset.mem_filter, Finset.mem_powerset] at hAF
  obtain ⟨hAsub, hAind⟩ := hAF
  refine ⟨A, hAsub, hAind, ?_⟩
  have hcover : s.support ⊆ A ∪ A.image s ∪ A.image (s⁻¹ : Equiv.Perm Y) := by
    intro x hx
    by_cases hxA : x ∈ A
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hxA)
    · have hsub : insert x A ⊆ s.support := by
        intro y hy
        rcases Finset.mem_insert.mp hy with hyx | hyA
        · rw [hyx]
          exact hx
        · exact hAsub hyA
      -- maximality forbids `insert x A` from being independent
      have hnotind : ¬ ∀ y ∈ insert x A, s y ∉ insert x A := by
        intro hall
        have hcard := hAmax (insert x A)
          (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hall⟩)
        rw [Finset.card_insert_of_notMem hxA] at hcard
        omega
      have hex : ∃ y ∈ insert x A, s y ∈ insert x A := by
        by_contra hcon
        exact hnotind fun y hy hsy ↦ hcon ⟨y, hy, hsy⟩
      obtain ⟨y, hy, hsy⟩ := hex
      rcases Finset.mem_insert.mp hy with hyx | hyA
      · rw [hyx] at hsy
        rcases Finset.mem_insert.mp hsy with hfix | hsxA
        · exact absurd hfix (Equiv.Perm.mem_support.mp hx)
        · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s x, hsxA, ?_⟩)
          simp
      · rcases Finset.mem_insert.mp hsy with hsyx | hsyA
        · exact Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y, hyA, hsyx⟩))
        · exact absurd hsyA (hAind y hyA)
  calc s.support.card
      ≤ (A ∪ A.image s ∪ A.image (s⁻¹ : Equiv.Perm Y)).card :=
        Finset.card_le_card hcover
    _ ≤ (A ∪ A.image s).card + (A.image (s⁻¹ : Equiv.Perm Y)).card :=
        Finset.card_union_le _ _
    _ ≤ A.card + (A.image s).card + (A.image (s⁻¹ : Equiv.Perm Y)).card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ A.card + A.card + A.card :=
        Nat.add_le_add (Nat.add_le_add_left Finset.card_image_le _)
          Finset.card_image_le
    _ = 3 * A.card := by ring

/-! ## One commutator doubles a permutation -/

/-- **The commutator with `s` of a permutation supported in an independent set
is two disjoint copies of it.**  `s g s⁻¹` is supported in `sA` and `g⁻¹` in
`A`, which are disjoint, so the cycle types add and both summands are
`g.cycleType`.

This is the only place the independence of `A` is used, and the only place any
hypothesis on `g` is used. -/
theorem cycleType_commutator_of_independent {s g : Equiv.Perm Y} {A : Finset Y}
    (hAind : ∀ x ∈ A, s x ∉ A) (hg : g.support ⊆ A) :
    (s * g * s⁻¹ * g⁻¹).cycleType = g.cycleType + g.cycleType := by
  have hdisj : Equiv.Perm.Disjoint (s * g * s⁻¹) g⁻¹ := by
    rw [Equiv.Perm.disjoint_iff_disjoint_support, Equiv.Perm.support_conj,
      Equiv.Perm.support_inv, Finset.disjoint_left]
    intro z hz hzg
    obtain ⟨y, hy, hyz⟩ := Finset.mem_map.mp hz
    have hsy : s y ∈ A := by
      rw [show s y = z from hyz]
      exact hg hzg
    exact hAind y (hg hy) hsy
  rw [hdisj.cycleType_mul, Equiv.Perm.cycleType_conj, Equiv.Perm.cycleType_inv]

/-! ## The production theorem -/

/-- **Every doubled cycle type is reached by two conjugates.**  If `A` is
independent for `s` and `g` is supported in `A`, then every permutation whose
cycle type is `g.cycleType + g.cycleType` is a product of at most two
conjugates of `s` and `s⁻¹`.

The two ingredients are `cycleType_commutator_of_independent`, which produces
one such element, and `isBoundedConjProduct_conj`, which moves it across its
whole conjugacy class without lengthening the product; `isConj_iff_cycleType_eq`
identifies that class with the cycle type. -/
theorem isBoundedConjProduct_two_of_cycleType_eq {s g : Equiv.Perm Y}
    {A : Finset Y} (hAind : ∀ x ∈ A, s x ∉ A) (hg : g.support ⊆ A)
    {z : Equiv.Perm Y} (hz : z.cycleType = g.cycleType + g.cycleType) :
    IsBoundedConjProduct s 2 z := by
  have hcomm : IsBoundedConjProduct s 2 (s * g * s⁻¹ * g⁻¹) := by
    have h := isBoundedConjProduct_commutator s g
    rwa [commutatorElement_def] at h
  have hconj : IsConj (s * g * s⁻¹ * g⁻¹) z :=
    Equiv.Perm.isConj_iff_cycleType_eq.mpr
      ((cycleType_commutator_of_independent hAind hg).trans hz.symm)
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  rw [← hc]
  exact isBoundedConjProduct_conj 2 (s * g * s⁻¹ * g⁻¹) c hcomm

end AlternatingBoundedNormalGeneration
end GroupApproximation
