import GroupApproximation.Kazhdan.GHBQuotientVertexForms
import GroupApproximation.Kazhdan.SharpExistenceLatticeUnconditional

/-!
# The lattice route through `GHB(7)`

`Hyperbolic.LatticeRouteInput` asks for an infinite finitely presented hyperbolic
Kazhdan group together with a torsion-free finite-index subgroup, and
`FiniteIndex.sharpExistence_of_latticeRoute_unconditional` turns one such datum into
`SharpExistence`.  The Kac–Moody–Steinberg group `GHB(7)` of Caprace–Conder–Kaluba–Witzel
(arXiv:2011.09276, Theorem 1.3) is the datum here, with `Sub := ker ψ` for the quotient
`ψ : GHB(7) → GL₄(F₇)` of CCKW Proposition 7.15.

Field by field:

| field | supplied by |
|---|---|
| `Carrier`, `groupCarrier`, `fpCarrier` | `KMSGroup.GHB 7`, `KMSGroup.isFinitelyPresented` — proved |
| `Sub`, `subFiniteIndex` | `GHBQuotient.psiKer`, `GHBQuotient.psiKer_finiteIndex` — proved |
| `infiniteCarrier`, `subInfinite` | `GHBQuotient.infinite_ghb7`, `infinite_psiKer` — over `hconj` |
| `subTorsionFree` | `GHBQuotient.isPowerTorsionFree_psiKer` — over `hconj`, `h3`, `h4` |
| `hyperbolic` | open leaf `hhyp` (CCKW Theorem 3.1(i): a nonpositively curved (6,8,8) triangle of groups) |
| `kazhdan` | open leaf `hT` (CCKW Theorem 1.3 / EJZ criterion, lane kh-ejz) |

The open leaves are ordinary hypotheses of this intermediate construction, never
binders of an endpoint:
* `hconj : CCKWFiniteOrderConjugateIntoVertex` — CCKW Theorem 3.1(ii), cyclic case
  (`Kazhdan/CCKWFiniteSubgroupsStatement.lean`);
* `h3`, `h4` with `Finite (U3 7)`, `Finite (U4 7)` — CCKW Proposition 7.2 order bounds
  (lane kh-hyperbolic, module 2);
* `hhyp` — hyperbolicity of `GHB(7)`;
* `hT` — property (T) of `GHB(7)`.
-/

namespace GroupApproximation
namespace KMSGroup
namespace GHBQuotient

/-- **The lattice datum from `GHB(7)`**, over the open leaves listed in the module
docstring. -/
def ghb7LatticeRouteInput (hconj : CCKWFiniteOrderConjugateIntoVertex)
    [Finite (U3 7)] [Finite (U4 7)] (h3 : Nat.card (U3 7) ≤ 7 ^ 3)
    (h4 : Nat.card (U4 7) ≤ 7 ^ 4) (hhyp : Hyperbolic.IsHyperbolicGroup (GHB 7))
    (hT : HasKazhdanPropertyT.{0, 0} (GHB 7)) : Hyperbolic.LatticeRouteInput where
  Carrier := GHB 7
  infiniteCarrier := infinite_ghb7 hconj
  hyperbolic := hhyp
  kazhdan := hT
  Sub := psiKer
  subFiniteIndex := psiKer_finiteIndex
  subTorsionFree := isPowerTorsionFree_psiKer hconj h3 h4
  subInfinite := infinite_psiKer hconj

/-- **`SharpExistence` from `GHB(7)`**, over the same open leaves. -/
theorem sharpExistence_of_ghb7Leaves (hconj : CCKWFiniteOrderConjugateIntoVertex)
    [Finite (U3 7)] [Finite (U4 7)] (h3 : Nat.card (U3 7) ≤ 7 ^ 3)
    (h4 : Nat.card (U4 7) ≤ 7 ^ 4) (hhyp : Hyperbolic.IsHyperbolicGroup (GHB 7))
    (hT : HasKazhdanPropertyT.{0, 0} (GHB 7)) : Hyperbolic.SharpExistence :=
  FiniteIndex.sharpExistence_of_latticeRoute_unconditional
    (ghb7LatticeRouteInput hconj h3 h4 hhyp hT)

end GHBQuotient
end KMSGroup
end GroupApproximation

#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.sharpExistence_of_ghb7Leaves
