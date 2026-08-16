import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# The squaring endomorphism of a free group is injective

The remaining half of stage **E3** of the Adian--Rabin roadmap in
`GroupApproximation/Computability/RabinConstruction.lean`.

`FreeByRetraction` proves that the stable letters `t₀, …, tₙ` of the Rabin
tower are free of rank `n+1`, by a retraction that kills the base.  The `u`
layer is an HNN extension whose two associated subgroups are `⟨t₀, …, tₙ⟩` and
`⟨t₀², …, tₙ²⟩`, so forming it needs an isomorphism between them — and the
retraction cannot supply that, because it sends `tᵢ²` to `of i ^ 2` and thereby
reduces the question to one entirely inside the free group:

```text
sq : FreeGroup α →* FreeGroup α ,      of a ↦ of a ^ 2
```

is injective.  That is what this file proves.

## The proof

Reducedness in Mathlib is `IsReduced L := L.IsChain fun a b ↦ a.1 = b.1 → a.2 = b.2`:
adjacent letters naming the same generator must carry the same sign, since a
cancellation is exactly a same-generator opposite-sign pair.

Squaring doubles every letter of a word in place.  The doubled list is still
reduced, and the reason is immediate once the predicate is written out: a new
adjacency is either a letter beside *itself*, which trivially satisfies the
relation, or an adjacency that was already present in the original, which
satisfied it there.

Then `sq` sends the class of a reduced word to the class of the doubled word,
the doubled word is reduced and is empty only when the original is, and a free
group element is trivial exactly when its reduced word is empty.

No ping-pong, no Nielsen--Schreier, no rank computation: the whole content is
that doubling a letter cannot create a cancellation.

## Scope

This is the last free-group fact the `t`-layer needs.  It says nothing about
stages E4 and E5, which `RabinBrittonFreeness` shows are behind a
Baumslag--Solitar relation that no free quotient can carry.

Never compiled.
-/

namespace GroupApproximation
namespace FreeGroupSquaring

open FreeGroup List

variable {α : Type*}

/-! ## Doubling a word -/

/-- Every letter of a word, repeated. -/
def double (L : List (α × Bool)) : List (α × Bool) :=
  L.flatMap fun p => [p, p]

@[simp] theorem double_nil : double ([] : List (α × Bool)) = [] := rfl

@[simp] theorem double_cons (p : α × Bool) (L : List (α × Bool)) :
    double (p :: L) = p :: p :: double L := by
  simp [double]

theorem double_eq_nil_iff {L : List (α × Bool)} : double L = [] ↔ L = [] := by
  cases L with
  | nil => simp
  | cons p L => simp [double_cons]

/-- **Doubling preserves reducedness.**  A new adjacency is either a letter
beside itself, or one that was already there. -/
theorem isReduced_double {L : List (α × Bool)} (h : IsReduced L) :
    IsReduced (double L) := by
  induction L with
  | nil => simpa using isChain_nil
  | cons p L ih =>
      rw [double_cons]
      rcases L with _ | ⟨q, L⟩
      · -- `[p, p]`: the only adjacency is `p` beside itself
        simp only [double_nil]
        rw [isChain_cons_iff]
        refine ⟨?_, isChain_singleton _⟩
        intro _
        rfl
      · -- `p :: p :: double (q :: L)`
        have hchain := (isChain_cons_iff _ _ _).mp h
        have htail : IsReduced (q :: L) := hchain.2
        have hpq : p.1 = q.1 → p.2 = q.2 := by
          have := hchain.1
          simpa using this
        rw [isChain_cons_iff]
        refine ⟨fun _ => rfl, ?_⟩
        rw [double_cons] at ih ⊢
        rw [isChain_cons_iff]
        exact ⟨hpq, (ih htail).tail⟩

/-! ## The endomorphism -/

/-- The endomorphism sending each generator to its square. -/
def sq : FreeGroup α →* FreeGroup α :=
  FreeGroup.lift fun a => FreeGroup.of a ^ 2

@[simp] theorem sq_of (a : α) : sq (FreeGroup.of a) = FreeGroup.of a ^ 2 :=
  FreeGroup.lift_apply_of

/-- Squaring sends the class of a word to the class of its doubling. -/
theorem sq_mk (L : List (α × Bool)) :
    sq (FreeGroup.mk L) = FreeGroup.mk (double L) := by
  induction L with
  | nil => simp [double, sq]
  | cons p L ih =>
      obtain ⟨a, b⟩ := p
      have hcons : FreeGroup.mk ((a, b) :: L)
          = (cond b (FreeGroup.of a) (FreeGroup.of a)⁻¹) * FreeGroup.mk L := by
        cases b <;> simp [FreeGroup.mk, FreeGroup.of] <;> rfl
      rw [hcons, map_mul, ih, double_cons]
      have hdbl : FreeGroup.mk ((a, b) :: (a, b) :: double L)
          = (cond b (FreeGroup.of a) (FreeGroup.of a)⁻¹) *
            ((cond b (FreeGroup.of a) (FreeGroup.of a)⁻¹) *
              FreeGroup.mk (double L)) := by
        cases b <;> simp [FreeGroup.mk, FreeGroup.of] <;> rfl
      rw [hdbl]
      cases b <;> simp [sq, FreeGroup.lift_apply_of, pow_two, mul_assoc]

/-! ## Injectivity -/

/-- **The squaring endomorphism is injective.** -/
theorem sq_injective : Function.Injective (sq : FreeGroup α →* FreeGroup α) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hword : sq x = FreeGroup.mk (double x.toWord) := by
    conv_lhs => rw [← FreeGroup.mk_toWord (x := x)]
    exact sq_mk x.toWord
  have hred : IsReduced (double x.toWord) :=
    isReduced_double FreeGroup.isReduced_toWord
  have hnil : double x.toWord = [] := by
    have : FreeGroup.mk (double x.toWord) = 1 := by rw [← hword, hx]
    have hre : FreeGroup.reduce (double x.toWord) = [] := by
      rw [← FreeGroup.toWord_mk, ← FreeGroup.toWord_eq_nil_iff.mpr this]
    rwa [hred.reduce_eq] at hre
  rw [← FreeGroup.toWord_eq_nil_iff]
  exact double_eq_nil_iff.mp hnil

/-- The image of the squaring endomorphism is the subgroup generated by the
squares of the basis, so `sq_injective` says exactly that those squares are a
free basis of that subgroup. -/
theorem sq_range :
    (sq : FreeGroup α →* FreeGroup α).range
      = Subgroup.closure (Set.range fun a : α => FreeGroup.of a ^ 2) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    induction x using FreeGroup.induction_on with
    | C1 => simpa using Subgroup.one_mem _
    | of a => simpa using Subgroup.subset_closure ⟨a, rfl⟩
    | inv_of a _ => simpa using
        Subgroup.inv_mem _ (Subgroup.subset_closure ⟨a, rfl⟩)
    | mul _ _ hx hy => simpa using Subgroup.mul_mem _ hx hy
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨a, rfl⟩
    exact ⟨FreeGroup.of a, by simp⟩

end FreeGroupSquaring
end GroupApproximation
