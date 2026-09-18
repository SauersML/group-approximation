import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittCoeffLoc
import Mathlib.Algebra.Module.Injective
import Mathlib.RingTheory.Artinian.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# Interface for the module side of the Witt coefficient gap

`EHighWittCoeffModuleStatement` (PureCharPrimeEHighWittCoeffGap.lean) asks for an embedding of
`M` into `Dⁿ`, where `D = ZMod (p²)[X₁..X_d]` is localized at `(p)` (`eHighWittCoeff_D`), with
`Q` acting through `D`-matrices. The paper's steps 3–4 are pure commutative algebra over `D`.
This file names them, so that the lane proving them and the lane reducing the gap to them
share one interface:

* `EHighWittModSelfInjStatement`: `D` is self-injective (the only ideals are `0`, `pD` and `D`;
  Baer's criterion);
* `EHighWittModEmbedStatement`: every finitely generated, finite-length `D`-module embeds
  `D`-linearly in some `Dˢ`.

Both are only definitions here; nothing is proved in this file.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

/-- `D = ZMod (p²)[X₁..X_d]_(p)` is self-injective. -/
def EHighWittModSelfInjStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (d : ℕ),
    Module.Injective (eHighWittCoeff_D p (Fin d)) (eHighWittCoeff_D p (Fin d))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.EHighWittModSelfInjStatement

/-- Every finitely generated, finite-length `D`-module embeds `D`-linearly in some `Dˢ`. -/
def EHighWittModEmbedStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (d : ℕ) (N : Type) [AddCommGroup N]
    [Module (eHighWittCoeff_D p (Fin d)) N],
    Module.Finite (eHighWittCoeff_D p (Fin d)) N → IsArtinian (eHighWittCoeff_D p (Fin d)) N →
      ∃ (s : ℕ) (ι : N →ₗ[eHighWittCoeff_D p (Fin d)] (Fin s → eHighWittCoeff_D p (Fin d))),
        Function.Injective ι

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.EHighWittModEmbedStatement

end GroupApproximation.BooneHigman.Metabelian.Coprimary
