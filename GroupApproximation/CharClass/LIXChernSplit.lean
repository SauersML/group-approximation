import GroupApproximation.CharClass.LIXChernSliceNatural

/-!
# The `ChernSplit` of the Chern classes on a mapping torus

Lane `cc-projective` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.4, item 5).

`WuStepDLix`'s first field, `S`, is documented as open and owned by this lane.  It
is not open: `Wu.chernSplitOfGraded` builds it from the degree concentration of the
classes alone, and `lixChernOf_mappingTorus` supplies that concentration on a
mapping torus with the proof arguments already in the shape it wants.  So the
field is one application, and this file is that application under a name the
assembly can cite.

Landing it also settles a seam.  `WuStepDLix.S` looks like a free choice, but its
fourth field `hslice` is stated against whichever `S` was chosen, and
`hslice_of_props` proves that statement only for `Wu.chernSplitOfGraded`.  So `S`
is not free, and `lixChernSplit` is the choice that keeps `hslice` dischargeable.

## Main declarations

* `lixChernSplit` — **the `S` field**, for the Chern classes of a mapping torus.

## Manuscript status

Machinery.  Closes one of the three inputs `CharClass/LemmaTwoStepDLix.lean`
records as open.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open GroupApproximation.STW59

noncomputable section

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-- **`WuStepDLix`'s `S` field**, for the mod-2 Chern classes of a mapping torus.

Nothing is assumed beyond continuity and the corner-unitary condition, because the
splitting is not a property of the classes: it follows from their sitting in even
degrees, which `lixChern`'s type records and `lixChernOf_mappingTorus` transfers to
the ring-valued family.

This is the choice of `S` that `hslice_of_props` is stated against.  Any other
splitting leaves `hslice` reopened, so an assembly should cite this one. -/
def lixChernSplit (dd : Fin ℓ → ℕ)
    (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ) (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    KnTwo.ChernSplit (baseY dd)
      (fun k => TotalH.map (Wu.lixIso dd).inv
        (lixChernOf (lixChern dd)
          (mappingTorus Vmat G circHoriz circHeight) k)) :=
  Wu.chernSplitOfGraded dd
    (lixChernOf (lixChern dd) (mappingTorus Vmat G circHoriz circHeight))
    (lixChern dd (mappingTorus Vmat G circHoriz circHeight)
      (continuous_mappingTorus_lix hGc) (isStarProjection_mappingTorus_lix hGu))
    (fun k => lixChernOf_mappingTorus (lixChern dd) hGc hGu k)

end

end CharClass
end GroupApproximation
