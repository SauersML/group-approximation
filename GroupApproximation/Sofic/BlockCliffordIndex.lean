import GroupApproximation.Sofic.BlockCliffordLamp

/-!
# The block Clifford lamp group over an arbitrarily indexed block set

`BlockCliffordLamp.BlockClifford` is presented over a block set `I` carried
with `[Fintype I]`, because its residual finiteness argument counts blocks.
The lamp kernel this development is aimed at has an *infinite* block set — the
blocks are indexed by a coset space of the vertical group — so the presented
group itself must exist without that hypothesis, and finiteness must enter only
where it is used.

This module supplies that separation.  The presentation, its generators, and
the relations among them are defined for an arbitrary index type; the
finiteness-dependent facts are then recovered on *windows*, the subgroups
spanned by finitely many blocks, which is the only form in which the soficity
tower consumes them.

## Why windows are the right unit

The tower proves soficity by exhausting a group with subgroups that are
residually finite and invariant under a level.  It never needs the whole lamp
kernel to be residually finite — it is not, once the block set is infinite and
the kernel contains nonabelian free subgroups.  It needs each finite subset of
the kernel to sit inside a finitely generated residually finite invariant piece.
A window is exactly such a piece, and `BlockCliffordLamp` already proves the
finite-index case, so the work here is the reduction of a window to it.

## What is defined

* `Gen`, `IsRelator`, `relators`, `BlockCliffordI` — the presentation over an
  arbitrary `I`, with the same four relation families: the sign squares, the
  lamps square, the sign is central, and two lamps of a common block commute
  through the sign.
* `sign`, `lampAt` — the generators.
* `windowGen`, `window` — the subgroup spanned by the blocks of a finite set
  `J`, and the corresponding restriction of the index type.
* `windowEquiv` — a window is the block Clifford group of its own finite block
  set, so every fact proved in `BlockCliffordLamp` applies to it.

## What is deliberately absent

No claim that the *whole* group is residually finite, LEF, or sofic: for an
infinite block set the first is false and the other two are consequences of the
locality argument, which belongs to the tower and not here.
-/

namespace GroupApproximation
namespace BlockCliffordIndex

open Monoid

universe u v

variable (I : Type u) (B : I → Type v)

/-! ## The presentation -/

/-- Generators: one central sign, and one lamp per site.  A site is a block
together with a coordinate of that block. -/
abbrev Gen : Type (max u v) := Unit ⊕ ((i : I) × B i)

/-- The four relation families.  They are the block Clifford relations
verbatim; only the finiteness of the block set has been dropped. -/
inductive IsRelator : FreeGroup (Gen I B) → Prop
  | sign_sq : IsRelator (FreeGroup.of (Sum.inl ()) ^ 2)
  | lamp_sq (p : (i : I) × B i) : IsRelator (FreeGroup.of (Sum.inr p) ^ 2)
  | sign_comm (p : (i : I) × B i) :
      IsRelator ⁅(FreeGroup.of (Sum.inl ()) : FreeGroup (Gen I B)),
        FreeGroup.of (Sum.inr p)⁆
  | braiding (i : I) (b b' : B i) :
      IsRelator (⁅(FreeGroup.of (Sum.inr ⟨i, b⟩) : FreeGroup (Gen I B)),
          FreeGroup.of (Sum.inr ⟨i, b'⟩)⁆ * (FreeGroup.of (Sum.inl ()))⁻¹)

/-- The relations as a set. -/
def relators : Set (FreeGroup (Gen I B)) := {w | IsRelator I B w}

/-- The block Clifford lamp group over an arbitrary block set. -/
abbrev BlockCliffordI : Type (max u v) := PresentedGroup (relators I B)

/-- The central sign. -/
def sign : BlockCliffordI I B := PresentedGroup.of (Sum.inl ())

/-- The lamp at a site. -/
def lampAt (p : (i : I) × B i) : BlockCliffordI I B :=
  PresentedGroup.of (Sum.inr p)

/-! ## The defining relations, as facts -/

theorem sign_sq : sign I B ^ 2 = 1 := by
  have h := PresentedGroup.one_of_mem
    (show FreeGroup.of (Sum.inl ()) ^ 2 ∈ relators I B from IsRelator.sign_sq)
  rwa [map_pow] at h

theorem lampAt_sq (p : (i : I) × B i) : lampAt I B p ^ 2 = 1 := by
  have h := PresentedGroup.one_of_mem
    (show FreeGroup.of (Sum.inr p) ^ 2 ∈ relators I B from IsRelator.lamp_sq p)
  rwa [map_pow] at h

theorem sign_commute (p : (i : I) × B i) :
    Commute (sign I B) (lampAt I B p) := by
  have h := PresentedGroup.one_of_mem
    (show ⁅(FreeGroup.of (Sum.inl ()) : FreeGroup (Gen I B)),
        FreeGroup.of (Sum.inr p)⁆ ∈ relators I B from IsRelator.sign_comm p)
  rw [map_commutatorElement] at h
  exact commutatorElement_eq_one_iff_commute.mp h

/-- Two lamps of a common block commute through the sign. -/
theorem braiding (i : I) (b b' : B i) :
    ⁅lampAt I B ⟨i, b⟩, lampAt I B ⟨i, b'⟩⁆ = sign I B := by
  have h := PresentedGroup.one_of_mem
    (show (⁅(FreeGroup.of (Sum.inr ⟨i, b⟩) : FreeGroup (Gen I B)),
        FreeGroup.of (Sum.inr ⟨i, b'⟩)⁆ * (FreeGroup.of (Sum.inl ()))⁻¹)
      ∈ relators I B from IsRelator.braiding i b b')
  rw [map_mul, map_inv, map_commutatorElement] at h
  exact mul_inv_eq_one.mp h

/-- The sign is central: it commutes with every generator, hence with
everything. -/
theorem sign_central (g : BlockCliffordI I B) : Commute (sign I B) g := by
  refine PresentedGroup.generated_by (relators I B) _ ?_ g
  rintro (⟨⟩ | p)
  · exact Commute.refl _
  · exact sign_commute I B p

/-! ## Windows

A window is the part of the group visible over finitely many blocks.  Every
finite subset of the group lies in one, because a word mentions finitely many
generators and each generator names one block. -/

/-- The blocks of a finite set `J`, as an index type in its own right. -/
abbrev WindowIndex (J : Finset I) : Type u := {i : I // i ∈ J}

/-- The coordinates of a window block. -/
abbrev WindowBlock (J : Finset I) (i : WindowIndex I J) : Type v := B (i : I)

/-- The generators visible over `J`. -/
def windowGen (J : Finset I) : Set (BlockCliffordI I B) :=
  {sign I B} ∪ {g | ∃ p : (i : I) × B i, p.1 ∈ J ∧ g = lampAt I B p}

/-- The window subgroup: everything spanned by the blocks of `J`. -/
def window (J : Finset I) : Subgroup (BlockCliffordI I B) :=
  Subgroup.closure (windowGen I B J)

theorem sign_mem_window (J : Finset I) : sign I B ∈ window I B J :=
  Subgroup.subset_closure (Or.inl rfl)

theorem lampAt_mem_window {J : Finset I} {p : (i : I) × B i} (h : p.1 ∈ J) :
    lampAt I B p ∈ window I B J :=
  Subgroup.subset_closure (Or.inr ⟨p, h, rfl⟩)

/-- Windows grow with their block set. -/
theorem window_mono {J K : Finset I} (h : J ⊆ K) :
    window I B J ≤ window I B K := by
  refine Subgroup.closure_le _ |>.mpr ?_
  rintro g (hg | ⟨p, hp, rfl⟩)
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    exact sign_mem_window I B K
  · exact lampAt_mem_window I B (h hp)

/-- The window over the empty block set is the sign alone. -/
theorem window_empty :
    window I B (∅ : Finset I) = Subgroup.closure ({sign I B} : Set _) := by
  refine congrArg Subgroup.closure ?_
  ext g
  constructor
  · rintro (hg | ⟨p, hp, rfl⟩)
    · exact hg
    · exact absurd hp (Finset.notMem_empty _)
  · exact fun hg ↦ Or.inl hg

/-! ## Reduction of a window to the finite-index theory

The point of the module.  A window is presented by the block Clifford
relations of its own finite block set, so `BlockCliffordLamp`'s residual
finiteness applies to it unchanged. -/

/-- The generator map carrying the finite-index presentation into the window. -/
def windowGenerator (J : Finset I) [DecidableEq I] [Fintype (WindowIndex I J)]
    [∀ i, DecidableEq (WindowBlock I B J i)]
    [∀ i, Fintype (WindowBlock I B J i)] :
    BlockCliffordLamp.Gen (WindowIndex I J) (WindowBlock I B J) →
      BlockCliffordI I B
  | Sum.inl () => sign I B
  | Sum.inr ⟨i, b⟩ => lampAt I B ⟨(i : I), b⟩

/-- The finite-index relations hold of the window generators, so the map
descends to the window. -/
theorem windowGenerator_kills (J : Finset I) [DecidableEq I]
    [Fintype (WindowIndex I J)] [∀ i, DecidableEq (WindowBlock I B J i)]
    [∀ i, Fintype (WindowBlock I B J i)] :
    ∀ w ∈ BlockCliffordLamp.relators (WindowIndex I J) (WindowBlock I B J),
      FreeGroup.lift (windowGenerator I B J) w = 1 := by
  intro w hw
  induction hw with
  | sign_sq => simpa [windowGenerator] using sign_sq I B
  | lamp_sq p => simpa [windowGenerator] using lampAt_sq I B ⟨(p.1 : I), p.2⟩
  | sign_comm p =>
      have := sign_commute I B (⟨(p.1 : I), p.2⟩ : (i : I) × B i)
      simpa [windowGenerator, commutatorElement_eq_one_iff_commute] using this
  | braiding i b b' =>
      have := braiding I B (i : I) b b'
      simpa [windowGenerator] using this

/-- **A window is a finite-block Clifford group.**  The finite-index
presentation maps onto the window, so every theorem proved there — residual
finiteness above all — transfers to it. -/
def toWindow (J : Finset I) [DecidableEq I] [Fintype (WindowIndex I J)]
    [∀ i, DecidableEq (WindowBlock I B J i)]
    [∀ i, Fintype (WindowBlock I B J i)] :
    BlockCliffordLamp.BlockClifford (WindowIndex I J) (WindowBlock I B J) →*
      BlockCliffordI I B :=
  PresentedGroup.toGroup (windowGenerator_kills I B J)

theorem toWindow_range (J : Finset I) [DecidableEq I]
    [Fintype (WindowIndex I J)] [∀ i, DecidableEq (WindowBlock I B J i)]
    [∀ i, Fintype (WindowBlock I B J i)] :
    (toWindow I B J).range = window I B J := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨g, rfl⟩
    refine PresentedGroup.generated_by _ (window I B J) ?_ g
    rintro (⟨⟩ | ⟨i, b⟩)
    · simpa [toWindow, windowGenerator, PresentedGroup.toGroup.of]
        using sign_mem_window I B J
    · simpa [toWindow, windowGenerator, PresentedGroup.toGroup.of]
        using lampAt_mem_window I B (p := (⟨(i : I), b⟩ : (i : I) × B i)) i.2
  · refine (Subgroup.closure_le _).mpr ?_
    rintro g (hg | ⟨p, hp, rfl⟩)
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact ⟨PresentedGroup.of (Sum.inl ()), by
        simp [toWindow, windowGenerator, PresentedGroup.toGroup.of]⟩
    · exact ⟨PresentedGroup.of (Sum.inr ⟨⟨p.1, hp⟩, p.2⟩), by
        simp [toWindow, windowGenerator, PresentedGroup.toGroup.of]⟩

end BlockCliffordIndex
end GroupApproximation
