import GroupApproximation.Manuscript.MFRecognition.MarkedHigmanOutput

/-!
# A fixed universal host replaces the uniform Higman compiler

For a fixed family of rank-three recursively presented groups, it is enough
to embed all of them in one group `U` and embed `U` once in one finitely
presented host.  The host presentation and its embedding are constants.
Only the three marked words vary with the input index, so computability of
those words gives the required computable raw output family.

This module records exactly that interface and constructs
`MarkedHigmanOutput` without importing the old, uninhabited
`EffectiveHigmanCompiler`.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HigmanCompiler

noncomputable section

/-- One fixed universal group, one fixed finitely presented host, and the
computable marked inclusions of a family `Q_e` into that universal group. -/
structure FixedUniversalHostCompiler (qcode : ℕ → RecPresCode) where
  /-- The fixed universal group containing every group in the family. -/
  U : Type
  /-- Its group structure. -/
  [UGroup : Group U]
  /-- The single finite presentation used for every output. -/
  host : PresentationCodes.PresentationCode
  /-- The single embedding of the universal group in the fixed host. -/
  hostEmb : U →* Host host
  hostEmb_injective : Function.Injective hostEmb
  /-- The three marked host words for input `e`. -/
  wordX : ℕ → Higman.RawWord
  wordY : ℕ → Higman.RawWord
  wordT : ℕ → Higman.RawWord
  computable_wordX : Computable wordX
  computable_wordY : Computable wordY
  computable_wordT : Computable wordT
  /-- The computable inclusion represented by the marked words, after
  passage to the presented input group. -/
  sourceEmb : ∀ e, PresentedQ (qcode e) →* U
  sourceEmb_injective : ∀ e, Function.Injective (sourceEmb e)
  /-- The marked words spell the composite of the input inclusion with the
  one fixed host embedding. -/
  marked_comm : ∀ e,
    (hostQuotient host).comp (markedHom host (wordX e) (wordY e) (wordT e)) =
      hostEmb.comp ((sourceEmb e).comp (quotientQ (qcode e)))

attribute [instance] FixedUniversalHostCompiler.UGroup

namespace FixedUniversalHostCompiler

variable {qcode : ℕ → RecPresCode} (C : FixedUniversalHostCompiler qcode)

/-- The marked semantic output at one index. -/
def output (e : ℕ) : MarkedHigmanOutput (qcode e) where
  host := C.host
  wordX := C.wordX e
  wordY := C.wordY e
  wordT := C.wordT e
  emb := C.hostEmb.comp (C.sourceEmb e)
  emb_comm := by
    rw [C.marked_comm e]
    rfl
  emb_injective := C.hostEmb_injective.comp (C.sourceEmb_injective e)

/-- The raw compiler output: the host code is constant and only the three
marked words vary. -/
def compile (e : ℕ) : RawMarkedOutput :=
  (C.host, C.wordX e, C.wordY e, C.wordT e)

/-- The fixed-host raw output family is computable. -/
theorem computable_compile : Computable C.compile := by
  exact (Computable.const C.host).pair
    (C.computable_wordX.pair
      (C.computable_wordY.pair C.computable_wordT))

/-- The semantic marked output has exactly the raw value emitted by the
fixed-host compiler. -/
theorem output_raw (e : ℕ) : (C.output e).raw = C.compile e := rfl

/-- Closed replacement for the useful conclusion of the old uniform Higman
compiler, specialized to the actual family of inputs. -/
theorem exists_output (e : ℕ) :
    ∃ o : MarkedHigmanOutput (qcode e), o.raw = C.compile e :=
  ⟨C.output e, C.output_raw e⟩

end FixedUniversalHostCompiler

end

end HigmanCompiler
end MFRecognition
end Manuscript
end GroupApproximation
