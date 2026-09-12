import GroupApproximation.CharClass.LIXStepDGenTorusPPtot
import GroupApproximation.CharClass.CohomologyKunnethLixN
import GroupApproximation.Meta.AxiomGuard

/-!
# The torus data of Step D mod `p` at every stage of the rank-`n` tower

Lane `lx-torusP` of the LIX strongest swarm (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`, §1.4–1.5).

`Gen.realTorusModP_ofIso` (`CharClass/LIXStepDGenTorusPPtot.lean`) builds `Gen.RealTorusModP` at
any space isomorphic to the Künneth model.  This file instantiates it at the real mapping-torus base
`KGen.lixN n dd` through `lx-kunneth`'s model isomorphism `KnLix.lixIso n dd`, with the projections
`KnLix.prY`, `KnLix.prS1`, `KnLix.prSodd` and the canonical sphere classes `sphereTopClassOf`, which
are the classes `lx-kunneth`'s Chern split uses.  The dimensions `dd` are arbitrary, so every stage
`dd := LIX.Gen.lixDD n j` is covered, stage `0` included.

## Main results

* `Gen.realTorusModP_lix` — the torus data at `KGen.lixN n dd`.
* `Gen.realTorusModP_lixStage` — the family over the stages of the tower.
-/

set_option autoImplicit false

noncomputable section

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace Gen

variable {ℓ : ℕ}

/-- **The torus data at the real mapping-torus base `KGen.lixN n dd`**, from the reduced powers,
at `lx-kunneth`'s projections and the canonical sphere classes. -/
def realTorusModP_lix {p : ℕ} [Fact p.Prime] (ops : OddPTotal.EvenReducedPowers p) (n : ℕ)
    (dd : Fin ℓ → ℕ) :
    RealTorusModP n (ZMod p) (KnLix.prY n dd) (KnLix.prS1 n dd) (KnLix.prSodd n dd)
      (sphereTopClassOf (ZMod p) 1 le_rfl) (sphereTopClassOf (ZMod p) (2 * n + 1) (by omega)) :=
  realTorusModP_ofIso ops (baseY dd) n (KnLix.lixIso n dd)
    (sphereTopClassOf (ZMod p) 1 le_rfl) (sphereTopClassOf_ne_zero (ZMod p) 1 le_rfl)
    (sphereTopClassOf (ZMod p) (2 * n + 1) (by omega))
    (sphereTopClassOf_ne_zero (ZMod p) (2 * n + 1) (by omega))

/-- **The torus data at every stage of the rank-`n` tower**, `dd := LIX.Gen.lixDD n j`. -/
def realTorusModP_lixStage {p : ℕ} [Fact p.Prime] (ops : OddPTotal.EvenReducedPowers p) (n : ℕ)
    (j : ℕ) :
    RealTorusModP n (ZMod p) (KnLix.prY n (LIX.Gen.lixDD n j)) (KnLix.prS1 n (LIX.Gen.lixDD n j))
      (KnLix.prSodd n (LIX.Gen.lixDD n j))
      (sphereTopClassOf (ZMod p) 1 le_rfl) (sphereTopClassOf (ZMod p) (2 * n + 1) (by omega)) :=
  realTorusModP_lix ops n (LIX.Gen.lixDD n j)

end Gen

#audit_axioms Gen.realTorusModP_lix
#audit_axioms Gen.realTorusModP_lixStage

end CharClass
end GroupApproximation

end
