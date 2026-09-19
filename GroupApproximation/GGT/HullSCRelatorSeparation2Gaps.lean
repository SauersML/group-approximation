import GroupApproximation.GGT.HullSCRelatorSeparation2Component

/-!
# The forbidden set of one exponent, and deep powers for a family

The exponent design of `GGT/HullSCRelatorSeparationGaps.lean` avoided, for each
exponent already chosen, three finite families of group elements.  Over two
subgroups the same three families appear for each of the two loxodromic
elements, so it is worth naming them once.

`badSet a j T` is the set of elements a short two-sided translate carries onto
`a ^ j`, or that it carries `a ^ j` onto, together with the mirrored family for
`(a ^ j)⁻¹`.  Avoiding it with both `a ^ m` and `(a ^ m)⁻¹` gives all four
separation clauses at once, which is why `exists_deep_pow_family` produces both.

Nothing here is about the relator; it is the counting that
`GGT.RelGenSet.IsHyperbolicallyEmbedded.locallyFinite` makes available, stated
for a family of elements indexed by `Bool` so that the two subgroups of the
alternating relator are treated together.
-/

namespace GroupApproximation
namespace HullSC

universe u

section BadSet

variable {G : Type u} [Group G]

/-- **The forbidden values for one exponent.**  An element of `badSet a j T` is
carried onto `a ^ j` by elements of `T` on either side, or carries `a ^ j` onto
itself that way, or is carried onto `(a ^ j)⁻¹`. -/
def badSet (a : G) (j : ℕ) (T : Set G) : Set G :=
  Set.image2 (fun x x' : G => x⁻¹ * a ^ j * x'⁻¹) T T
    ∪ Set.image2 (fun x x' : G => x * a ^ j * x') T T
    ∪ Set.image2 (fun x x' : G => x⁻¹ * (a ^ j)⁻¹ * x'⁻¹) T T

theorem finite_badSet (a : G) (j : ℕ) {T : Set G} (hT : T.Finite) :
    (badSet a j T).Finite :=
  ((Set.Finite.image2 _ hT hT).union (Set.Finite.image2 _ hT hT)).union
    (Set.Finite.image2 _ hT hT)

theorem mem_badSet_of_left {a : G} {j : ℕ} {T : Set G} {x x' : G}
    (hx : x ∈ T) (hx' : x' ∈ T) : x⁻¹ * a ^ j * x'⁻¹ ∈ badSet a j T :=
  Set.mem_union_left _
    (Set.mem_union_left _ (Set.mem_image2.mpr ⟨x, hx, x', hx', rfl⟩))

theorem mem_badSet_of_mid {a : G} {j : ℕ} {T : Set G} {x x' : G}
    (hx : x ∈ T) (hx' : x' ∈ T) : x * a ^ j * x' ∈ badSet a j T :=
  Set.mem_union_left _
    (Set.mem_union_right _ (Set.mem_image2.mpr ⟨x, hx, x', hx', rfl⟩))

theorem mem_badSet_of_right {a : G} {j : ℕ} {T : Set G} {x x' : G}
    (hx : x ∈ T) (hx' : x' ∈ T) : x⁻¹ * (a ^ j)⁻¹ * x'⁻¹ ∈ badSet a j T :=
  Set.mem_union_right _ (Set.mem_image2.mpr ⟨x, hx, x', hx', rfl⟩)

end BadSet

/-! ## Deep powers for two elements at once -/

section Family

variable {G : Type u} [Group G]

/-- **All but finitely many exponents are deep for both elements.**

This is `HullSC.exists_deep_pow` for a family indexed by `Bool`: the preimage of
a finite set under each of the two power maps is finite, and the union of two
finite sets of exponents is bounded, so any exponent past that bound is deep for
both. -/
theorem exists_deep_pow_family {a : Bool → G}
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    {S : Set G} (hS : S.Finite) (n₀ : ℕ) :
    ∃ m : ℕ, n₀ ≤ m ∧ ∀ s : Bool, a s ^ m ∉ S ∧ (a s ^ m)⁻¹ ∉ S := by
  have hS' : (S ∪ (fun x : G => x⁻¹) '' S).Finite := hS.union (hS.image _)
  have hpre : ∀ s : Bool,
      ((fun n : ℕ => a s ^ n) ⁻¹' (S ∪ (fun x : G => x⁻¹) '' S)).Finite :=
    fun s => Set.Finite.preimage (fun _ _ _ _ hxy => hinj s hxy) hS'
  obtain ⟨M₀, hM₀⟩ := (hpre false).bddAbove
  obtain ⟨M₁, hM₁⟩ := (hpre true).bddAbove
  refine ⟨max n₀ (max M₀ M₁ + 1), le_max_left _ _, ?_⟩
  intro s
  have hlt : max M₀ M₁ < max n₀ (max M₀ M₁ + 1) := by
    have h := le_max_right n₀ (max M₀ M₁ + 1)
    omega
  have hkey : a s ^ max n₀ (max M₀ M₁ + 1)
      ∉ S ∪ (fun x : G => x⁻¹) '' S := by
    intro hmem
    cases s with
    | false =>
        have hle := hM₀ (show max n₀ (max M₀ M₁ + 1) ∈ _ from hmem)
        omega
    | true =>
        have hle := hM₁ (show max n₀ (max M₀ M₁ + 1) ∈ _ from hmem)
        omega
  exact ⟨fun hc => hkey (Or.inl hc),
    fun hc => hkey (Or.inr ⟨(a s ^ max n₀ (max M₀ M₁ + 1))⁻¹, hc, inv_inv _⟩)⟩

end Family

end HullSC
end GroupApproximation
