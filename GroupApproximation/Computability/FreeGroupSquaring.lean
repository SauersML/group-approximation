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
-/

namespace GroupApproximation
namespace FreeGroupSquaring

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
theorem isReduced_double {L : List (α × Bool)} (h : FreeGroup.IsReduced L) :
    FreeGroup.IsReduced (double L) := by
  induction L with
  | nil =>
      rw [double_nil]
      exact FreeGroup.IsReduced.nil
  | cons p L ih =>
      cases L with
      | nil =>
          -- `[p, p]`: the only adjacency is `p` beside itself
          rw [double_cons, double_nil, FreeGroup.isReduced_cons_cons]
          exact ⟨fun _ => rfl, FreeGroup.IsReduced.singleton⟩
      | cons q L =>
          rw [FreeGroup.isReduced_cons_cons] at h
          rw [double_cons, double_cons, FreeGroup.isReduced_cons_cons]
          refine ⟨fun _ => rfl, ?_⟩
          rw [FreeGroup.isReduced_cons_cons]
          refine ⟨h.1, ?_⟩
          have hrec := ih h.2
          rwa [double_cons] at hrec

/-! ## The endomorphism -/

/-- The endomorphism sending each generator to its square. -/
def sq : FreeGroup α →* FreeGroup α :=
  FreeGroup.lift fun a => FreeGroup.of a ^ 2

@[simp] theorem sq_of (a : α) : sq (FreeGroup.of a) = FreeGroup.of a ^ 2 :=
  FreeGroup.lift_apply_of

/-- Splitting the leading letter off a word. -/
theorem mk_cons (p : α × Bool) (L : List (α × Bool)) :
    FreeGroup.mk (p :: L) = FreeGroup.mk [p] * FreeGroup.mk L := by
  rw [FreeGroup.mul_mk]
  rfl

/-- On a one-letter word, `sq` really is squaring: the letter is a generator or
the inverse of one, and `(g⁻¹)² = g⁻¹g⁻¹` either way. -/
theorem sq_mk_singleton (p : α × Bool) :
    sq (FreeGroup.mk [p]) = FreeGroup.mk [p] * FreeGroup.mk [p] := by
  obtain ⟨a, b⟩ := p
  cases b with
  | true =>
      have h : FreeGroup.mk [(a, true)] = FreeGroup.of a := rfl
      rw [h, sq_of, pow_two]
  | false =>
      have h : FreeGroup.mk [(a, false)] = (FreeGroup.of a)⁻¹ := by
        show FreeGroup.mk [(a, false)] = (FreeGroup.mk [(a, true)])⁻¹
        rw [FreeGroup.inv_mk]
        rfl
      rw [h, map_inv, sq_of, pow_two, mul_inv_rev]

/-- Squaring sends the class of a word to the class of its doubling. -/
theorem sq_mk (L : List (α × Bool)) :
    sq (FreeGroup.mk L) = FreeGroup.mk (double L) := by
  induction L with
  | nil =>
      rw [double_nil, ← FreeGroup.one_eq_mk]
      exact map_one sq
  | cons p L ih =>
      rw [double_cons, mk_cons p L, mk_cons p (p :: double L), mk_cons p (double L),
        map_mul, ih, ← mul_assoc, ← sq_mk_singleton]

/-! ## Injectivity -/

/-- **The squaring endomorphism is injective.** -/
theorem sq_injective : Function.Injective (sq : FreeGroup α →* FreeGroup α) := by
  classical
  rw [injective_iff_map_eq_one]
  intro x hx
  have hword : sq x = FreeGroup.mk (double x.toWord) := by
    rw [← sq_mk, FreeGroup.mk_toWord]
  have hred : FreeGroup.IsReduced (double x.toWord) :=
    isReduced_double FreeGroup.isReduced_toWord
  have hone : FreeGroup.mk (double x.toWord) = 1 := by rw [← hword, hx]
  have hnil : double x.toWord = [] := by
    have h2 : (FreeGroup.mk (double x.toWord)).toWord = [] :=
      FreeGroup.toWord_eq_nil_iff.mpr hone
    rwa [FreeGroup.toWord_mk, hred.reduce_eq] at h2
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
    | C1 => simp
    | of a =>
        rw [sq_of]
        exact Subgroup.subset_closure (Set.mem_range_self a)
    | inv_of a _ =>
        rw [map_inv, sq_of]
        exact Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_range_self a))
    | mul x y hx hy =>
        rw [map_mul]
        exact Subgroup.mul_mem _ hx hy
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨a, rfl⟩
    exact ⟨FreeGroup.of a, by simp⟩

end FreeGroupSquaring
end GroupApproximation
