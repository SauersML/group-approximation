import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittModRed
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittModInjEmbed
import GroupApproximation.Meta.AxiomGuard

/-!
# The Witt coefficient gap, closed

Lane bh-met-87f proves the interface `EHighWittModSelfInjStatement` and
`EHighWittModEmbedStatement` outright (`eHighWittModInj_selfInjStatement`,
`eHighWittModInj_embedStatement`). Lane bh-met-87g reduces `EHighWittCoeffModuleStatement` to
that interface (`eHighWittModRed_module_of_iface`). This file composes them, so that the module
side, the linear coefficient statement, the weight-polynomial Witt embedding, the Artin–Hasse
polynomial-function statement and the `e = 2` infinite mixed case all hold with no hypotheses.

The general `e ≥ 3` case (`eHighMixed_InfiniteStatement`) is not covered here.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

/-- **The module side of the Witt coefficient gap, proved.** -/
theorem eHighWittModWire_module : EHighWittCoeffModuleStatement :=
  eHighWittModRed_module_of_iface eHighWittModInj_selfInjStatement eHighWittModInj_embedStatement

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModWire_module

/-- The linear coefficient statement, proved. -/
theorem eHighWittModWire_linCoeff : EHighWittLinCoeffStatement :=
  eHighWittCoeff_of_module eHighWittModWire_module

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModWire_linCoeff

/-- The weight-polynomial Witt embedding, proved. -/
theorem eHighWittModWire_wittEmbed : EHighArtinHasseWittEmbedStatement :=
  eHighWittCoeff_wittEmbed_of_module eHighWittModWire_module

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModWire_wittEmbed

/-- The Artin–Hasse polynomial-function statement, proved. -/
theorem eHighWittModWire_polyFun : EHighArtinHassePolyFunStatement :=
  eHighWittLin_polyFun_of_coeff eHighWittModWire_linCoeff

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModWire_polyFun

/-- **The `e = 2` infinite mixed case, proved.** -/
theorem eHighWittModWire_eTwo : EHighETwoStatement :=
  eHighWittCoeff_eTwo_of_module eHighWittModWire_module

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModWire_eTwo

end GroupApproximation.BooneHigman.Metabelian.Coprimary
