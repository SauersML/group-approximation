import GroupApproximation.Computability.RabinConstructionSource
import GroupApproximation.Computability.PresentedGroupBasisChange
import Mathlib.GroupTheory.OrderOfElement

/-!
# Stage E2: the shifted generators have infinite order

Stage **E2** of the Adian--Rabin roadmap in
`GroupApproximation/Computability/RabinConstruction.lean`.  The construction
needs each element of the shifted basis

```text
s₀ ,      sᵢ = s₀ xᵢ      (i ≥ 1)
```

of `G = Γ * ℤ` to have infinite order, because stages E3 and E4 form HNN
extensions with associated subgroups `⟨sᵢ⟩` and `⟨sᵢ²⟩` and need those to be
infinite cyclic.

## The short proof

The roadmap costed this stage through the free-product normal form —
`CoprodI.Word`, `NeWord`, and an order-of-an-element consequence that Mathlib
does not carry.  None of that is needed.

Kill the source factor.  The retraction

```text
π : Γ * ℤ ↠ ℤ ,      xᵢ ↦ 0 ,      s₀ ↦ 1
```

sends *every* shifted generator to the same place: `sᵢ = s₀xᵢ ↦ 1 + 0 = 1`,
and `s₀ ↦ 1`.  The generator of `ℤ` has infinite order, and an element whose
image under a homomorphism has infinite order has infinite order itself.  So
all `n+1` cases are one line, and no normal form appears.

This works precisely because the shift is by the *free* letter: the whole
point of the basis change of `E1(ii)` is that each new generator carries
exactly one copy of `s₀`, which is what `π` sees.

## What this does not claim

Nothing about the subgroups `⟨s₀, …, sₙ⟩` or `⟨s₀², …, sₙ²⟩` being free —
that is E3, and freeness is strictly stronger than each generator having
infinite order.  The retraction here collapses all of them to a single copy of
`ℤ`, so it cannot see freeness at all.

Never compiled.
-/

namespace GroupApproximation
namespace RabinFreeLetterOrder

open RabinConstructionSource PresentedGroupBasisChange

variable {α : Type} (rels : Set (FreeGroup α))

/-! ## The retraction onto the free letter -/

/-- Send every source generator to `0` and the free letter to `1`. -/
def freeLetterGen : α ⊕ Unit → Multiplicative ℤ
  | Sum.inl _ => 1
  | Sum.inr () => Multiplicative.ofAdd 1

/-- Every relator of the free-product presentation dies: the relators of the
source factor are words in the source generators, all of which are sent to `1`,
and the free factor contributes none. -/
theorem freeLetterGen_kills :
    ∀ w ∈ coprodRels rels (∅ : Set (FreeGroup Unit)),
      FreeGroup.lift (freeLetterGen (α := α)) w = 1 := by
  rintro w (⟨v, _, rfl⟩ | ⟨v, hv, rfl⟩)
  · -- a relator of the source factor, relabelled by `inl`
    have h : (FreeGroup.lift (freeLetterGen (α := α))).comp
        (FreeGroup.map (Sum.inl : α → α ⊕ Unit))
        = (1 : FreeGroup α →* Multiplicative ℤ) := by
      refine FreeGroup.ext_hom _ _ ?_
      intro a
      -- `map` on a generator, `lift` on a generator and the generator table all
      -- reduce definitionally
      rfl
    exact DFunLike.congr_fun h v
  · exact absurd hv (Set.notMem_empty v)

/-- **The retraction `Γ * ℤ ↠ ℤ`.** -/
def freeLetterRetraction :
    CoprodPresented rels (∅ : Set (FreeGroup Unit)) →* Multiplicative ℤ :=
  PresentedGroup.toGroup (freeLetterGen_kills rels)

@[simp] theorem freeLetterRetraction_inl (a : α) :
    freeLetterRetraction rels (PresentedGroup.of (Sum.inl a)) = 1 :=
  PresentedGroup.toGroup.of _

@[simp] theorem freeLetterRetraction_inr :
    freeLetterRetraction rels (PresentedGroup.of (Sum.inr ()))
      = Multiplicative.ofAdd 1 :=
  PresentedGroup.toGroup.of _

/-! ## Infinite order -/

/-- An element whose image has infinite order has infinite order. -/
theorem infinite_order_of_image {G H : Type*} [Group G] [Group H]
    (f : G →* H) {g : G} (h : ∀ n : ℕ, 0 < n → f g ^ n ≠ 1) :
    ∀ n : ℕ, 0 < n → g ^ n ≠ 1 := by
  intro n hn hg
  exact h n hn (by rw [← map_pow, hg, map_one])

/-- The image of the free letter generates a copy of `ℤ`, so its powers are
never trivial. -/
theorem ofAdd_one_pow_ne_one (n : ℕ) (hn : 0 < n) :
    (Multiplicative.ofAdd (1 : ℤ)) ^ n ≠ 1 := by
  intro h
  have : ((n : ℤ) • (1 : ℤ)) = 0 := by
    simpa [← ofAdd_nsmul] using congrArg Multiplicative.toAdd h
  simp only [smul_eq_mul, mul_one, Int.natCast_eq_zero] at this
  exact hn.ne' this

/-- **The free letter has infinite order.** -/
theorem freeLetter_infinite_order (n : ℕ) (hn : 0 < n) :
    (PresentedGroup.of (Sum.inr ()) :
      CoprodPresented rels (∅ : Set (FreeGroup Unit))) ^ n ≠ 1 := by
  refine infinite_order_of_image (freeLetterRetraction rels) ?_ n hn
  intro m hm
  rw [freeLetterRetraction_inr]
  exact ofAdd_one_pow_ne_one m hm

/-- **Every shifted generator has infinite order.**  The shifted generator
`sᵢ = s₀ xᵢ` carries exactly one copy of the free letter, so the retraction
sends it to the generator of `ℤ` regardless of `i`. -/
theorem shifted_infinite_order (a : α) (n : ℕ) (hn : 0 < n) :
    ((PresentedGroup.of (Sum.inr ()) : CoprodPresented rels
        (∅ : Set (FreeGroup Unit))) * PresentedGroup.of (Sum.inl a)) ^ n
      ≠ 1 := by
  refine infinite_order_of_image (freeLetterRetraction rels) ?_ n hn
  intro m hm
  rw [map_mul, freeLetterRetraction_inr, freeLetterRetraction_inl, mul_one]
  exact ofAdd_one_pow_ne_one m hm

end RabinFreeLetterOrder
end GroupApproximation
