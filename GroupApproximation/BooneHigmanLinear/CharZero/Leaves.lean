import GroupApproximation.BooneHigman.Metabelian.CharZeroCoordsAssembly
import GroupApproximation.BooneHigman.Metabelian.CharZeroHost.Endpoint
import GroupApproximation.BooneHigman.Metabelian.ChainWiredAffine
import GroupApproximation.BooneHigman.Metabelian.ChainCharZero
import GroupApproximation.Meta.AxiomGuard

/-!
# The characteristic-zero linear host: the proved leaves

T3 asks that every finitely generated linear group embed in a finitely presented simple group.
Its characteristic-zero half has three geometric or ring-theoretic leaves. The metabelian chain
in `GroupApproximation/BooneHigman/**` already proves all three with no hypotheses:

* `CharZeroHost.charZeroPolynomialCoordinates`: a finitely generated subgroup of `GL_n(K)`,
  `char K = 0`, embeds in `GL_M(ℤ[1/m][t_0, …, t_{k-1}])`;
* `CharZeroHost.charZeroAffineSelfSimilarStatement`: for `n ≥ 1` the affine group
  `S^n ⋊ E_n(S)`, `S = ℤ[1/m][t_0, …, t_{k-1}]`, acts faithfully and self-similarly on a regular
  rooted tree;
* `Chain.affineExtensionFPStatement_holds`: if `E_n(R)` is finitely presented, `n ≥ 4`, `R` a
  finitely generated commutative ring, then so is `R^n ⋊ E_n(R)`.

This module bundles them (`charZeroLeaves`). Given those leaves, the characteristic-zero linear
host reduces to two statements of pure K-theory about the single ring family
`ℤ[1/m][t_0, …, t_{k-1}]` (`charZeroLinearHost_of_absorption_of_fp`):

* absorption, `Chain.CharZeroElementaryAbsorptionStatement`: `GL_M(S)` embeds in `E_N(S)`
  for `N ≥ 3`, `N ≥ 2M` (from `SL_N(S) = E_N(S)`, Suslin);
* finite presentation, `Chain.CharZeroElementaryFPStatement`: `E_N(S)` is finitely presented
  for `N ≥ k + 4`.

No field, no linear group and no tree appears in either statement. This file only composes
existing endpoints and adds no new mathematics.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace CharZeroHalf

open GroupApproximation.BooneHigman.Metabelian

/-- **The three proved characteristic-zero leaves**: polynomial `S`-integer coordinates, the
faithful self-similar affine host, and finite presentation of the affine extension. -/
theorem charZeroLeaves :
    Chain.CharZeroPolynomialCoordinatesStatement ∧ Chain.CharZeroAffineSelfSimilarStatement ∧
      Chain.AffineExtensionFPStatement :=
  ⟨CharZeroHost.charZeroPolynomialCoordinates, CharZeroHost.charZeroAffineSelfSimilarStatement,
    Chain.affineExtensionFPStatement_holds⟩

#audit_axioms charZeroLeaves

/-- **The characteristic-zero linear host from K-theory alone.** Every finitely generated
subgroup of `GL_n(K)`, `char K = 0`, embeds in a finitely presented self-similar group, given
absorption into `E_N` and finite presentation of `E_N` over `ℤ[1/m][t_0, …, t_{k-1}]`. -/
theorem charZeroLinearHost_of_absorption_of_fp
    (habs : Chain.CharZeroElementaryAbsorptionStatement)
    (hfp : Chain.CharZeroElementaryFPStatement) : Chain.CharZeroLinearHostStatement :=
  Chain.charZeroLinearHostStatement_of_chain CharZeroHost.charZeroPolynomialCoordinates habs hfp
    Chain.affineExtensionFPStatement_holds CharZeroHost.charZeroAffineSelfSimilarStatement

#audit_axioms charZeroLinearHost_of_absorption_of_fp

end CharZeroHalf
end BooneHigmanLinear
end GroupApproximation
