import GroupApproximation.Sofic.ExplicitNonMFBase
import GroupApproximation.Sofic.MarkedCompressionGroup

/-!
# The internal explicit marked-compression group

This module instantiates the generic marked-compression construction with the
binary Leavitt compressor.  Keeping the instantiation separate lets other
constructions use the generic group without importing this coefficient model.
-/

namespace GroupApproximation
namespace MarkedCompression
namespace Explicit

open ExplicitNonMFBase

/-- The explicit marked-compression group over the internal Kazhdan base. -/
noncomputable def theGroup : Type :=
  Ambient (BinaryLeavitt.elementaryShift (ZMod 2)) compression_injective

noncomputable instance : Group theGroup :=
  inferInstanceAs (Group
    (Ambient (BinaryLeavitt.elementaryShift (ZMod 2)) compression_injective))

instance : Countable theGroup :=
  inferInstanceAs (Countable
    (Ambient (BinaryLeavitt.elementaryShift (ZMod 2)) compression_injective))

/-- The embedding data of the base. -/
noncomputable def theIota : Base →* theGroup :=
  iotaAmbient (BinaryLeavitt.elementaryShift (ZMod 2)) compression_injective

/-- The stable letter. -/
noncomputable def theT : theGroup :=
  tAmbient (BinaryLeavitt.elementaryShift (ZMod 2)) compression_injective

/-- The root lamp. -/
noncomputable def theC : theGroup :=
  cAmbient (BinaryLeavitt.elementaryShift (ZMod 2)) compression_injective

/-- The compression relation. -/
theorem theCompress (γ : Base) :
    theT * theIota γ * theT⁻¹ = theIota (compression γ) :=
  compress (BinaryLeavitt.elementaryShift (ZMod 2)) compression_injective γ

/-- The root lamp centralises the base. -/
theorem theCommC (γ : Base) : Commute theC (theIota γ) :=
  comm_c (BinaryLeavitt.elementaryShift (ZMod 2)) compression_injective γ

/-- The root lamp is an involution. -/
theorem theCSq : theC ^ 2 = 1 := by
  exact cAmbient_sq _ _

/-- The marked word squares to one. -/
theorem theWordSq :
    markedCompressionWord theT (theIota omitted) theC ^ 2 = 1 := by
  change markedCompressionWord
    (tAmbient compression compression_injective)
    (iotaAmbient compression compression_injective omitted)
    (cAmbient compression compression_injective) ^ 2 = 1
  rw [marked_word_eq_sign _ _ omitted_not_mem_range]
  exact signAmbient_sq _ _

/-- The marked word is central. -/
theorem theWordCentral (g : theGroup) :
    Commute (markedCompressionWord theT (theIota omitted) theC) g := by
  change Commute (markedCompressionWord
    (tAmbient compression compression_injective)
    (iotaAmbient compression compression_injective omitted)
    (cAmbient compression compression_injective)) g
  rw [marked_word_eq_sign _ _ omitted_not_mem_range]
  exact signAmbient_central _ _ g

/-- The marked word is the surviving Clifford sign. -/
theorem theWordNeOne :
    markedCompressionWord theT (theIota omitted) theC ≠ 1 := by
  change markedCompressionWord
    (tAmbient compression compression_injective)
    (iotaAmbient compression compression_injective omitted)
    (cAmbient compression compression_injective) ≠ 1
  rw [marked_word_eq_sign _ _ omitted_not_mem_range]
  exact signAmbient_ne_one _ _

end Explicit
end MarkedCompression
end GroupApproximation
