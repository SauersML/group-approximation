import GroupApproximation.Pestov91.WitnessSimple
import GroupApproximation.Pestov91.Assembly
import GroupApproximation.Pestov91.LEF
import GroupApproximation.Pestov91.LEFWitness

/-!
# The Pestov 9.1 witness from the witness ring

`EL₃(WitnessRing)` is the witness, where `WitnessRing = LC(X, 𝔽₂) ⋊ ℤ` over the Toeplitz
subshift `X`.  `exists_infinite_simple_kazhdan_lef` is the existential that
`Palomar/Pestov91Solution.lean` consumes.

* Simplicity: `isSimpleGroup_elementaryGroup_witnessRing`.
* Property (T): `elementary_hasKazhdanPropertyT`, through
  `exists_infinite_simple_kazhdan_lef_of_elementary`.
* Infiniteness: `elementaryModCentre_crossedProduct_infinite`.
* LEF: `isLEF_elementaryGroup`, from `witnessRing_isLEFRing`.
* Finite generation: `witnessRing_isFinitelyGeneratedRing`.

The prose of this module was written by Claude (Anthropic).
-/

namespace GroupApproximation

namespace Pestov91

/-- **Pestov 9.1 from the witness ring.**  Finite generation and the LEF property of
`LC(X, 𝔽₂) ⋊ ℤ` give an infinite simple Kazhdan LEF group. -/
theorem exists_infinite_simple_kazhdan_lef_of_witnessRing
    (hA : IsFinitelyGeneratedRing WitnessRing) (hLEF : IsLEFRing WitnessRing) :
    ∃ (E : Type) (_ : Group E), Infinite E ∧ IsSimpleGroup E ∧ HasKazhdanPropertyT.{0, 0} E ∧
      IsLEF E :=
  haveI : Nontrivial (ZMod 2) := nontrivial_of_ne (0 : ZMod 2) 1 (by decide)
  exists_infinite_simple_kazhdan_lef_of_elementary hA isSimpleGroup_elementaryGroup_witnessRing
    elementaryModCentre_crossedProduct_infinite (isLEF_elementaryGroup hLEF)

/-- **Pestov 9.1.**  `EL₃(LC(X, 𝔽₂) ⋊ ℤ)`, over the Toeplitz subshift `X`, is an infinite
simple LEF group with property `(T)`. -/
theorem exists_infinite_simple_kazhdan_lef :
    ∃ (E : Type) (_ : Group E), Infinite E ∧ IsSimpleGroup E ∧ HasKazhdanPropertyT.{0, 0} E ∧
      IsLEF E :=
  exists_infinite_simple_kazhdan_lef_of_witnessRing witnessRing_isFinitelyGeneratedRing
    witnessRing_isLEFRing

end Pestov91

end GroupApproximation
