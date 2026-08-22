import GroupApproximation.Higman.GeneratedValue
import GroupApproximation.Higman.OperationClosureRho

/-!
# Route C: `τ` is droppable, and here is the replacement

`Higman.SwapCarrierWitness` proves that every construction mechanism this
repository has for a coded family is excluded for `τ`.  This file takes the
other exit: it shows that the live chain does not need `τ` at all.

`OperationClosures.tau` is spent in exactly one place ---
`Seq.benignTF_of_higmanGenerated`, on the `tau` constructor --- so `τ` is spent
exactly when a `HigmanGenerated` derivation uses that constructor.  There are
four such uses in the repository.  Three are in `Higman.GeneratedValue`, and
this file removes them; the fourth is the base case of
`HigmanVariableCalculus.higmanGenerated_swapAt`, in a module no module imports
and whose `swapAt` has no consumer anywhere.

## The replacement, in one line

`pinZero c = {f | f 0 = c}` and `pinOne c = {f | f 1 = c}` are *pins*: one
coordinate fixed, all others free.  `σ` is induced by a **bijection** of the
index set, so it carries the pin at `0` to the pin at `1`:

    σ (pinZero c) = pinOne c        (`sigmaOp_pinZero`)

and `higmanGenerated_pinOne'` is the resulting `τ`-free proof, replacing
`Seq.higmanGenerated_pinOne`.  The remaining `GeneratedValue` site --- the
`succ` step of `higmanGenerated_singleZero`, which uses `τ` only to move the
value at coordinate `1` down to coordinate `0` so that `θ` can read it --- is
served by the **down-shift**, which is `ρ σ ρ` and is built here as `downOf`.

So what those three sites need is a bijection of the index set carrying
coordinate `1` to coordinate `0`, and the infinite dihedral group `⟨σ, ρ⟩`
supplies one.  The transposition is simply the wrong tool; it was chosen
because its name matches the intent.

## The limit of derivability

Section 3 records how far `τ` is derivable from the rest, which is the sharp
answer to the other half of route C.  On a set whose two window coordinates are
pinned, `τ` is a composite of `ι`, coordinate-freeing, and the pins
(`tauOp_windowClass`), with no `τ` anywhere.  The general case is the union of
these over `(c, c') ∈ ℤ × ℤ`, and the operation list has only the *binary*
union, so the derivation does not close.  That gap --- uniformity in the window
values --- is the whole of what is unresolved, and
`notes/W6_TAU_ROUTE_C_2026-08-22.md` explains why the obvious repair routes back
through the transposition calculus.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

/-! ## 1.  The down-shift is `ρ σ ρ` -/

/-- The down-shift of a sequence, built from the two operations that are
induced by index bijections.  `ρ` reverses, `σ` shifts up, `ρ` reverses back. -/
noncomputable def downOf (f : E) : E := rhoSeq (shiftSeq (rhoSeq f))

@[simp] theorem downOf_apply (f : E) (i : ℤ) : downOf f i = f (i + 1) := by
  unfold downOf
  rw [rhoSeq_apply, shiftSeq_apply, rhoSeq_apply]
  congr 1
  ring

/-- **The down-shift undoes the shift**, so `σ` acts on sets by a bijection. -/
theorem shiftSeq_downOf (f : E) : shiftSeq (downOf f) = f := by
  refine Finsupp.ext fun i => ?_
  rw [shiftSeq_apply, downOf_apply]
  congr 1
  ring

/-! ## 2.  `σ` carries the pin at `0` to the pin at `1` -/

/-- **The replacement identity.**  `Seq.pinOne` is `σ` of `Seq.pinZero`, not `τ`
of it.  Both operations move the pinned coordinate from `0` to `1`; only one of
them costs an open leaf. -/
theorem sigmaOp_pinZero (c : ℤ) : sigmaOp (pinZero c) = pinOne c := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hg0 : g 0 = c := hg
    show shiftSeq g 1 = c
    rw [shiftSeq_apply, show (1 : ℤ) - 1 = 0 from by ring]
    exact hg0
  · intro hf
    have hf1 : f 1 = c := hf
    refine ⟨downOf f, ?_, shiftSeq_downOf f⟩
    show downOf f 0 = c
    rw [downOf_apply, show (0 : ℤ) + 1 = 1 from by ring]
    exact hf1

/-- **The pin at coordinate `1` is generated, without `τ`.**  This replaces
`Seq.higmanGenerated_pinOne`, which is one of the three live consumers of the
`tau` constructor. -/
theorem higmanGenerated_pinOne' (c : ℤ) : HigmanGenerated (pinOne c) := by
  rw [← sigmaOp_pinZero c]
  exact HigmanGenerated.sigma (higmanGenerated_pinZero' c)

/-! ## 3.  How far `τ` is derivable from the rest -/

/-- A set with both window coordinates freed.  This is
`HigmanAtoms.freeAt 1 ∘ HigmanAtoms.freeAt 0`, and
`HigmanAtoms.higmanGenerated_freeAt` generates it; it is spelled out here so
that this file needs no import of that module. -/
def freeWindow (B : Set E) : Set E :=
  {f | ∃ g ∈ B, ∀ i : ℤ, i ≠ 0 → i ≠ 1 → f i = g i}

/-- **`τ` is derivable on a window class.**

If both window coordinates of `B` are pinned, transposing them is the same as
freeing them and re-pinning them the other way round --- an intersection of a
coordinate-freeing with two pins, and no transposition anywhere.  The reason it
works is that on `B ∩ pinZero c ∩ pinOne c'` the window of the witness `g` is
determined, so re-pinning cannot pick up a different `g`.

The general `τ` is the union of these over all `(c, c') ∈ ℤ × ℤ`, and the
operation list has only the binary union.  That is exactly where derivability
stops. -/
theorem tauOp_windowClass (B : Set E) (c c' : ℤ) :
    tauOp (B ∩ pinZero c ∩ pinOne c')
      = freeWindow (B ∩ pinZero c ∩ pinOne c') ∩ pinZero c' ∩ pinOne c := by
  ext f
  constructor
  · rintro ⟨g, hg, h0, h1, hrest⟩
    have hg0 : g 0 = c := hg.1.2
    have hg1 : g 1 = c' := hg.2
    refine ⟨⟨⟨g, hg, hrest⟩, ?_⟩, ?_⟩
    · show f 0 = c'
      rw [h0, hg1]
    · show f 1 = c
      rw [h1, hg0]
  · rintro ⟨⟨⟨g, hg, hrest⟩, hf0⟩, hf1⟩
    have hg0 : g 0 = c := hg.1.2
    have hg1 : g 1 = c' := hg.2
    have hf0' : f 0 = c' := hf0
    have hf1' : f 1 = c := hf1
    exact ⟨g, hg, by rw [hf0', hg1], by rw [hf1', hg0], hrest⟩

end Seq
end Higman
end GroupApproximation
