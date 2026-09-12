import GroupApproximation.Algebra.CoprodIPresentation
import GroupApproximation.Algebra.PresentedGroupRelabel
import GroupApproximation.Manuscript.MFRecognition.MarkedHigmanOutput

/-!
# The fixed universal group of a rank-three family

For a family `Q_e` on three generators, put all generator alphabets in
disjoint blocks and take the presentation with precisely the relators of the
individual blocks.  The indexed free-product presentation theorem identifies
the result with `⨿ e, Q_e`; in particular every factor map is injective.

The alphabet `Σ e, Fin 3` is numbered explicitly by `3 * e + i`.  Thus this
is already a presentation on the standard countable alphabet used by the
effective HNN bridge, and the three generators of the `e`-th input have the
literal numbers `3 * e`, `3 * e + 1`, and `3 * e + 2`.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HigmanCompiler
namespace FixedUniversalFamily

noncomputable section

open CoprodIPresentation

/-- Number the disjoint union of three-letter blocks by consecutive naturals. -/
def blockEquiv : (Σ _e : ℕ, Fin 3) ≃ ℕ where
  toFun x := 3 * x.1 + x.2
  invFun n := ⟨n / 3, ⟨n % 3, Nat.mod_lt _ (by omega)⟩⟩
  left_inv x := by
    rcases x with ⟨e, i⟩
    have hdiv : (3 * e + (i : ℕ)) / 3 = e := by omega
    apply Sigma.ext hdiv
    apply heq_of_eq
    apply Fin.ext
    simp only
    omega
  right_inv n := by
    simp only
    omega

@[simp] theorem blockEquiv_mk (e : ℕ) (i : Fin 3) :
    blockEquiv ⟨e, i⟩ = 3 * e + i := rfl

/-- The free-product relators before numbering the block alphabet. -/
def sigmaRelators (qcode : ℕ → RecPresCode) :
    Set (FreeGroup (Σ _e : ℕ, Fin 3)) :=
  coprodRels fun e => rank3Relators (qcode e)

/-- The same relators on the standard countable alphabet. -/
def relators (qcode : ℕ → RecPresCode) : Set (FreeGroup ℕ) :=
  PresentedGroupRelabel.relabelRels blockEquiv (sigmaRelators qcode)

/-- One fixed group containing every member of the family. -/
abbrev U (qcode : ℕ → RecPresCode) : Type := PresentedGroup (relators qcode)

/-- The numbered presentation is exactly the indexed free product of the
family. -/
def universalEquiv (qcode : ℕ → RecPresCode) :
    U qcode ≃* Monoid.CoprodI (fun e => PresentedQ (qcode e)) :=
  (PresentedGroupRelabel.congrEquiv blockEquiv (sigmaRelators qcode)).symm.trans
    (coprodIPresentation fun e => rank3Relators (qcode e))

@[simp] theorem universalEquiv_of (qcode : ℕ → RecPresCode)
    (x : Σ _e : ℕ, Fin 3) :
    universalEquiv qcode (PresentedGroup.of (blockEquiv x)) =
      Monoid.CoprodI.of (i := x.1) (PresentedGroup.of x.2) := by
  unfold universalEquiv relators sigmaRelators
  change (coprodIPresentation fun e => rank3Relators (qcode e))
    ((PresentedGroupRelabel.congrEquiv blockEquiv
      (coprodRels fun e => rank3Relators (qcode e))).symm
      (PresentedGroup.of (blockEquiv x))) = _
  change (coprodIPresentation fun e => rank3Relators (qcode e))
    (PresentedGroupRelabel.relabelHomSymm blockEquiv
      (coprodRels fun e => rank3Relators (qcode e))
      (PresentedGroup.of (blockEquiv x))) = _
  rw [PresentedGroupRelabel.relabelHomSymm_of]
  simp only [Equiv.symm_apply_apply]
  exact coprodIPresentation_of (fun e => rank3Relators (qcode e)) x

/-- The canonical inclusion of the `e`-th input group into the fixed group. -/
def sourceEmb (qcode : ℕ → RecPresCode) (e : ℕ) :
    PresentedQ (qcode e) →* U qcode :=
  (universalEquiv qcode).symm.toMonoidHom.comp
    (Monoid.CoprodI.of (M := fun e => PresentedQ (qcode e)) (i := e))

theorem sourceEmb_injective (qcode : ℕ → RecPresCode) (e : ℕ) :
    Function.Injective (sourceEmb qcode e) :=
  (universalEquiv qcode).symm.injective.comp (Monoid.CoprodI.of_injective e)

/-- On a source generator, the factor inclusion is literally the generator
numbered by its three-letter block. -/
@[simp] theorem sourceEmb_of (qcode : ℕ → RecPresCode) (e : ℕ) (i : Fin 3) :
    sourceEmb qcode e (PresentedGroup.of i) =
      (PresentedGroup.of (3 * e + i) : U qcode) := by
  apply (universalEquiv qcode).injective
  change (universalEquiv qcode)
      ((universalEquiv qcode).symm
        (Monoid.CoprodI.of (i := e) (PresentedGroup.of i))) = _
  rw [MulEquiv.apply_symm_apply]
  change Monoid.CoprodI.of (i := e) (PresentedGroup.of i) =
    (universalEquiv qcode)
      (PresentedGroup.of (blockEquiv ⟨e, i⟩))
  exact (universalEquiv_of qcode ⟨e, i⟩).symm

/-- The canonical countable generating family used by the once-only HNN
bridge. -/
def gen (qcode : ℕ → RecPresCode) (n : ℕ) : U qcode := PresentedGroup.of n

theorem gen_spans (qcode : ℕ → RecPresCode) :
    Subgroup.closure (Set.range (gen qcode)) = ⊤ :=
  PresentedGroup.closure_range_of _

@[simp] theorem sourceEmb_quotient_of (qcode : ℕ → RecPresCode)
    (e : ℕ) (i : Fin 3) :
    sourceEmb qcode e (quotientQ (qcode e) (FreeGroup.of i)) =
      gen qcode (3 * e + i) := by
  change sourceEmb qcode e (PresentedGroup.of i) =
    (PresentedGroup.of (3 * e + i) : U qcode)
  exact sourceEmb_of qcode e i

end

end FixedUniversalFamily
end HigmanCompiler
end MFRecognition
end Manuscript
end GroupApproximation
