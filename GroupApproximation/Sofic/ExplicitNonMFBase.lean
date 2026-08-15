import GroupApproximation.Leavitt.ShiftEndomorphism
import GroupApproximation.Leavitt.UniversalPropertyT
import GroupApproximation.Leavitt.UniversalRankFour

/-!
# The explicit Kazhdan compressor used by the non-MF construction

This file fixes an entirely internal base group for the operator-norm
compressor obstruction.  It is the rank-four elementary group over the
universal binary Leavitt algebra over `ZMod 2`.  Earlier modules prove its
property `(T)` directly and construct the binary coefficient shift.  Here we
package the exact data needed downstream:

* an explicit group `Base`;
* an explicit injective, non-surjective endomorphism `compression`;
* an explicit element `omitted` outside its range; and
* property `(T)` for `Base`.

No external classification or matrix-group theorem enters this package.
-/

namespace GroupApproximation
namespace ExplicitNonMFBase

/-- The explicit Kazhdan group carrying the strict self-compression. -/
noncomputable abbrev Base := UniversalRankFour.Ambient

/-- The coefficientwise binary Leavitt shift on the rank-four elementary
group. -/
noncomputable def compression : Base →* Base :=
  BinaryLeavitt.elementaryShift (ZMod 2)

/-- The self-compression is injective. -/
theorem compression_injective : Function.Injective compression :=
  BinaryLeavitt.elementaryShift_injective (ZMod 2)

/-- A concrete elementary transvection omitted by the self-compression. -/
noncomputable def omitted : Base :=
  elementaryRoot
    (R := UniversalLeavitt.BinaryLeavittAlgebra)
    (0 : Fin 4) (1 : Fin 4) (by decide)
    UniversalRankFour.family.s0

/-- The displayed transvection is not in the compression range. -/
theorem omitted_not_mem_range : omitted ∉ Set.range compression := by
  exact BinaryLeavitt.elementaryRoot_s0_not_mem_shift_range (ZMod 2)

/-- In particular, the compression is proper. -/
theorem compression_not_surjective : ¬ Function.Surjective compression := by
  intro h
  exact omitted_not_mem_range (h omitted)

universe v

/-- The base group has Kazhdan's property `(T)`, proved internally from the
finite-type characteristic-two elementary-group theorem. -/
theorem base_hasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, v} Base :=
  UniversalRankFour.ambient_hasKazhdanPropertyT.{v}

/-- The exact closed package consumed by the marked non-MF presentation. -/
theorem base_profile :
    Countable Base ∧ Group.FG Base ∧
      HasKazhdanPropertyT.{0, 0} Base ∧
      Function.Injective compression ∧
      omitted ∉ Set.range compression := by
  exact ⟨inferInstance, inferInstance, base_hasKazhdanPropertyT,
    compression_injective, omitted_not_mem_range⟩

end ExplicitNonMFBase
end GroupApproximation
