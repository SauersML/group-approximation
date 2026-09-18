import GroupApproximation.BooneHigman.Metabelian.PureCharZeroStatement
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeSplit
import GroupApproximation.BooneHigman.Metabelian.TorsionFreeCoprimaryAssembly
import GroupApproximation.BooneHigman.Metabelian.TorsionFreeNoetherMain
import GroupApproximation.Meta.AxiomGuard

/-!
# Torsion-free linearity, closed (lane bh-met-63)

Two results are now on disk:

* `coprimaryTorsionFreeLinearity : CoprimaryTorsionFreeLinearityStatement`
  (`TorsionFreeNoetherMain.lean:46`), with no hypotheses;
* `torsionFreeModuleLinearity_of_coprimary` (`TorsionFreeCoprimaryAssembly.lean:28`), which
  reduces `TorsionFreeModuleLinearityStatement` to the coprimary case.

Combining them gives `torsionFreeModuleLinearity`, with no hypotheses.  Feeding that to
`pureCharLinearityZero_of_torsionFreeModuleLinearity` (`PureCharZeroStatement.lean:58`) gives
`pureCharLinearityZero : PureCharLinearityZeroStatement`: a finitely generated metabelian group
whose derived subgroup is torsion-free embeds in `GL_d(K)` for a field `K` of characteristic `0`.

The zero case is then removed from the two linearity consumers that take it:

* `pureCharLinearity_of_prime`: `pureCharLinearity_of_prime_zero` (`PureCharSplit.lean:41`)
  without `hz`;
* `pureCharLinearity_of_split`: `pureCharLinearity_of_split_zero` (`PureCharPrimeSplit.lean:109`)
  without `hz`.

No new mathematics: every proof is a term application of on-disk declarations.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Coprimary

/-- **Torsion-free module linearity.** A finitely generated `ℤ[Q]`-module (`Q` a finitely
generated abelian group) that is torsion-free as an abelian group embeds `Q`-equivariantly into
`K^d` for a field `K` of characteristic zero. -/
theorem torsionFreeModuleLinearity : TorsionFreeModuleLinearityStatement :=
  torsionFreeModuleLinearity_of_coprimary coprimaryTorsionFreeLinearity

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.torsionFreeModuleLinearity

/-- **Linearity in characteristic zero.** A finitely generated metabelian group whose derived
subgroup is torsion-free embeds in `GL_d(K)` for a field `K` of characteristic zero. -/
theorem pureCharLinearityZero : PureCharLinearityZeroStatement :=
  pureCharLinearityZero_of_torsionFreeModuleLinearity torsionFreeModuleLinearity

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.pureCharLinearityZero

/-- The linearity of pure-characteristic pieces from the prime case alone; the zero case is
`pureCharLinearityZero`. -/
theorem pureCharLinearity_of_prime (hp : PureCharLinearityPrimeStatement) :
    PureCharLinearityStatement :=
  pureCharLinearity_of_prime_zero hp pureCharLinearityZero

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.pureCharLinearity_of_prime

/-- The linearity of pure-characteristic pieces from the split prime case alone; the zero case
is `pureCharLinearityZero`. -/
theorem pureCharLinearity_of_split (hs : PureCharPrimeSplitStatement) :
    PureCharLinearityStatement :=
  pureCharLinearity_of_split_zero hs pureCharLinearityZero

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.pureCharLinearity_of_split

end Coprimary
end Metabelian
end BooneHigman
end GroupApproximation
