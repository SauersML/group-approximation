import GroupApproximation.CharClass.LIXStepDGenRealTorus
import GroupApproximation.CharClass.LIXSectionManuscript
import GroupApproximation.Meta.AxiomGuard

/-!
# The characteristic inputs of Step D mod `p` at the base of a stage

Lane `lx-bundleP` of the LIX strongest swarm (`notes/lix-strong-swarm/lx-bundleP.md`).

Step D mod `p` at the real mapping torus (`Gen.lemmaTwoFor_powers_of_stepC_realModP`,
`CharClass/LIXStepDGenReal.lean`) asks for the instance `ExpChar (evenPart K (Y j)) p` at the base
`Y j = ∏ᵢ ℂP^{dᵢ}` of every stage, and the producer of the bundle data
(`Gen.realBundleModP_of_split`, `CharClass/LIXStepDGenBundleP.lean`) asks for `p = 0` on `Y` and for
its normalisation `m` to be a unit there.  Over `K = F_p` all three are about `H⁰`: the naturals act
through `ZMod p`, and the unit class of a nonempty space does not vanish
(`Gen.charP_evenPart`, `CharClass/LIXStepDGenRealTorus.lean`).  The base of a stage is nonempty
because it carries the base point, the empty product at stage `0` included.

## Main results

* `Gen.nonempty_baseY` — the base of a stage is nonempty.
* `Gen.expChar_evenPart_baseY` — **the instance** `ExpChar (evenPart (ZMod p) (TopCat.of (baseY dd))) p`.
* `Gen.natCast_p_evenPart` — `p = 0` in the even part over `F_p`.
* `Gen.isUnit_intCast_evenPart` — an integer that is a unit mod `p` is a unit of the even part.
-/

set_option autoImplicit false

noncomputable section

namespace GroupApproximation
namespace CharClass

open CategoryTheory

namespace Gen

variable {ℓ : ℕ}

/-- **The base of a stage is nonempty**: it carries the base point, including at stage `0`,
where `dd` is the empty family and the base is a point. -/
theorem nonempty_baseY (dd : Fin ℓ → ℕ) : Nonempty (TopCat.of (baseY dd)) :=
  ⟨baseYPoint dd⟩

/-- **`ExpChar` of the even part of `H^*(∏ᵢ ℂP^{dᵢ}; F_p)`**, the instance Step D mod `p` asks for
at every stage. -/
instance expChar_evenPart_baseY (p : ℕ) [Fact p.Prime] (dd : Fin ℓ → ℕ) :
    ExpChar (evenPart (ZMod p) (TopCat.of (baseY dd))) p :=
  haveI := nonempty_baseY dd
  expChar_evenPart p _

/-- **`p = 0` in the even part of `H^*(Y; F_p)`**, for a nonempty `Y`. -/
theorem natCast_p_evenPart (p : ℕ) [Fact p.Prime] (Y : TopCat.{0}) [Nonempty Y] :
    ((p : ℕ) : evenPart (ZMod p) Y) = 0 :=
  haveI := charP_evenPart p Y
  CharP.cast_eq_zero _ p

/-- **An integer that is a unit mod `p` is a unit of the even part** of `H^*(Y; F_p)`, for a
nonempty `Y`: the cast factors through `ZMod p`. -/
theorem isUnit_intCast_evenPart (p : ℕ) [Fact p.Prime] (Y : TopCat.{0}) [Nonempty Y] {m : ℤ}
    (hm : IsUnit (m : ZMod p)) : IsUnit ((m : ℤ) : evenPart (ZMod p) Y) := by
  haveI := charP_evenPart p Y
  have h := hm.map (ZMod.castHom (dvd_refl p) (evenPart (ZMod p) Y))
  rwa [map_intCast] at h

end Gen

#audit_axioms Gen.nonempty_baseY
#audit_axioms Gen.expChar_evenPart_baseY
#audit_axioms Gen.natCast_p_evenPart
#audit_axioms Gen.isUnit_intCast_evenPart

end CharClass
end GroupApproximation

end
