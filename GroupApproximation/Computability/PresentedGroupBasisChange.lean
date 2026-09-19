import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Tietze change of free basis

Stage **E1(ii)** of the Adian--Rabin roadmap in
`GroupApproximation/Computability/RabinConstruction.lean`.

A presented group does not change when the free basis is changed by an
automorphism of the free group, provided the relator set is carried along.
`PresentedGroup.equivPresentedGroup` handles only relabelling of the alphabet;
what the Rabin construction needs is the substitution

```text
s₀ ↦ s₀ ,      sᵢ ↦ s₀ xᵢ      (i ≥ 1)
```

which is an automorphism of the free group but not a permutation of letters.
The tool for that is `PresentedGroup.map`, which transports along any
`FreeGroup α →* FreeGroup β` carrying relators into relators; running it in both
directions and gluing with `MonoidHom.toMulEquiv` gives the isomorphism.

## The general statement

`basisChangeEquiv` asks only for what is actually used: two free-group
homomorphisms, each carrying one relator set into the other, which are mutually
inverse *on generators*.  Being inverse on generators is enough, because
`FreeGroup.ext_hom` propagates it to the whole free group, and the induced maps
on the quotients are determined by their values on generators.

This is deliberately stated for two different alphabets and two different
relator sets rather than for an automorphism of one, because that is the shape
the construction produces: the substitution above rewrites the source relators
into different words, so the target relator set is the image of the source one
and not the same set.

## What this is for

The Rabin construction needs `G = Γ * ℤ` presented on the basis
`s₀, s₁, …, sₙ` rather than on `x₁, …, xₙ, s₀`, because the later stages
(`E2`–`E4`) are statements about the `sᵢ` — that each has infinite order, and
that the subgroups they generate are as free as they look.  Stage `E1(i)`,
that a presentation on a disjoint union of alphabets presents the free product,
is already available as `RabinConstructionSource.coprodEquiv`.

Never compiled.
-/

namespace GroupApproximation
namespace PresentedGroupBasisChange

variable {α β : Type*}

/-! ## The general basis change -/

/-- Being mutually inverse on generators is inherited by the whole free
group. -/
theorem comp_eq_id_of_generators {f : FreeGroup α →* FreeGroup β}
    {g : FreeGroup β →* FreeGroup α}
    (h : ∀ a : α, g (f (FreeGroup.of a)) = FreeGroup.of a) :
    g.comp f = MonoidHom.id (FreeGroup α) :=
  FreeGroup.ext_hom _ _ (by simpa using h)

/-- **Tietze change of free basis.**  Two free-group homomorphisms that carry
each relator set into the other and are mutually inverse on generators induce
an isomorphism of the presented groups. -/
def basisChangeEquiv {s : Set (FreeGroup α)} {t : Set (FreeGroup β)}
    (f : FreeGroup α →* FreeGroup β) (g : FreeGroup β →* FreeGroup α)
    (hst : s.MapsTo f t) (hts : t.MapsTo g s)
    (hgf : ∀ a : α, g (f (FreeGroup.of a)) = FreeGroup.of a)
    (hfg : ∀ b : β, f (g (FreeGroup.of b)) = FreeGroup.of b) :
    PresentedGroup s ≃* PresentedGroup t :=
  MonoidHom.toMulEquiv (PresentedGroup.map f hst) (PresentedGroup.map g hts)
    (by
      refine PresentedGroup.ext ?_
      intro a
      show (PresentedGroup.map g hts) ((PresentedGroup.map f hst)
        (PresentedGroup.of a)) = PresentedGroup.of a
      -- `QuotientGroup.map_mk` is `rfl`, so the two sides are already
      -- definitionally equal and no simp set is needed.
      exact congrArg (PresentedGroup.mk s) (hgf a))
    (by
      refine PresentedGroup.ext ?_
      intro b
      show (PresentedGroup.map f hst) ((PresentedGroup.map g hts)
        (PresentedGroup.of b)) = PresentedGroup.of b
      -- `QuotientGroup.map_mk` is `rfl`, so the two sides are already
      -- definitionally equal and no simp set is needed.
      exact congrArg (PresentedGroup.mk t) (hfg b))

/-- The forward map of a basis change sends a generator to the substituted
word. -/
@[simp] theorem basisChangeEquiv_of {s : Set (FreeGroup α)} {t : Set (FreeGroup β)}
    (f : FreeGroup α →* FreeGroup β) (g : FreeGroup β →* FreeGroup α)
    (hst : s.MapsTo f t) (hts : t.MapsTo g s)
    (hgf : ∀ a : α, g (f (FreeGroup.of a)) = FreeGroup.of a)
    (hfg : ∀ b : β, f (g (FreeGroup.of b)) = FreeGroup.of b) (a : α) :
    basisChangeEquiv f g hst hts hgf hfg (PresentedGroup.of a)
      = PresentedGroup.mk t (f (FreeGroup.of a)) := rfl

/-! ## The substitution the Rabin construction uses

The alphabet is `α ⊕ Unit`: the source generators together with the free
letter `s₀`.  The substitution fixes `s₀` and multiplies every source generator
by it on the left. -/

section RabinSubstitution

variable (α)

/-- `s₀`, the free letter adjoined to the source generators. -/
abbrev freeLetter : FreeGroup (α ⊕ Unit) := FreeGroup.of (Sum.inr ())

/-- The substitution `xᵢ ↦ s₀ xᵢ`, fixing `s₀`. -/
def shiftBasis : FreeGroup (α ⊕ Unit) →* FreeGroup (α ⊕ Unit) :=
  FreeGroup.lift fun c =>
    match c with
    | Sum.inl a => freeLetter α * FreeGroup.of (Sum.inl a)
    | Sum.inr () => freeLetter α

/-- The inverse substitution `xᵢ ↦ s₀⁻¹ xᵢ`, fixing `s₀`. -/
def unshiftBasis : FreeGroup (α ⊕ Unit) →* FreeGroup (α ⊕ Unit) :=
  FreeGroup.lift fun c =>
    match c with
    | Sum.inl a => (freeLetter α)⁻¹ * FreeGroup.of (Sum.inl a)
    | Sum.inr () => freeLetter α

variable {α}

@[simp] theorem shiftBasis_inl (a : α) :
    shiftBasis α (FreeGroup.of (Sum.inl a))
      = freeLetter α * FreeGroup.of (Sum.inl a) :=
  FreeGroup.lift_apply_of

@[simp] theorem shiftBasis_inr :
    shiftBasis α (FreeGroup.of (Sum.inr ())) = freeLetter α :=
  FreeGroup.lift_apply_of

@[simp] theorem unshiftBasis_inl (a : α) :
    unshiftBasis α (FreeGroup.of (Sum.inl a))
      = (freeLetter α)⁻¹ * FreeGroup.of (Sum.inl a) :=
  FreeGroup.lift_apply_of

@[simp] theorem unshiftBasis_inr :
    unshiftBasis α (FreeGroup.of (Sum.inr ())) = freeLetter α :=
  FreeGroup.lift_apply_of

/-- The two substitutions are mutually inverse on generators. -/
theorem unshift_shift (c : α ⊕ Unit) :
    unshiftBasis α (shiftBasis α (FreeGroup.of c)) = FreeGroup.of c := by
  match c with
  | Sum.inl a =>
      rw [shiftBasis_inl, map_mul, unshiftBasis_inr, unshiftBasis_inl,
        ← mul_assoc, mul_inv_cancel, one_mul]
  | Sum.inr () => rw [shiftBasis_inr, unshiftBasis_inr]

theorem shift_unshift (c : α ⊕ Unit) :
    shiftBasis α (unshiftBasis α (FreeGroup.of c)) = FreeGroup.of c := by
  match c with
  | Sum.inl a =>
      rw [unshiftBasis_inl, map_mul, map_inv, shiftBasis_inr, shiftBasis_inl,
        ← mul_assoc, inv_mul_cancel, one_mul]
  | Sum.inr () => rw [unshiftBasis_inr, shiftBasis_inr]

/-- **The change of basis, for any relator set.**  The source presentation on
`x₁,…,xₙ,s₀` and the substituted presentation on `s₀,s₁,…,sₙ` present the same
group.  The target relator set is the image of the source one, which is what
the substitution produces; it is not the same set of words. -/
def rabinBasisEquiv (s : Set (FreeGroup (α ⊕ Unit))) :
    PresentedGroup s ≃* PresentedGroup (shiftBasis α '' s) :=
  basisChangeEquiv (shiftBasis α) (unshiftBasis α)
    (fun _ hx => Set.mem_image_of_mem _ hx)
    (by
      rintro _ ⟨x, hx, rfl⟩
      have : unshiftBasis α (shiftBasis α x) = x :=
        DFunLike.congr_fun (comp_eq_id_of_generators unshift_shift) x
      rw [this]
      exact hx)
    unshift_shift shift_unshift

end RabinSubstitution

end PresentedGroupBasisChange
end GroupApproximation
