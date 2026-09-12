import GroupApproximation.Kazhdan.GHBSharpExistence
import GroupApproximation.Kazhdan.GHBLatticeRouteKazhdan

/-!
# `SharpExistence` from `GHB(7)`, with the order bounds and property (T) spent

`sharpExistence_ghb7_of_systolicLeaves` (`Kazhdan/GHBSharpExistence.lean`) with the proved leaves
fed in: the orders of `U₃(7)`, `U₄(7)` (`card_U3_seven_le`, `card_U4_seven_le`) and property (T)
of `GHB(7)` (inside `GHBQuotient.sharpExistence_of_ghb7ConjHyp`).  The open leaves are named
hypotheses:
* `hT6 : CCKW.SystolicInvariantCliqueStatement` — the fixed-clique theorem for systolic complexes;
* `hsc`, `hconn` — the coset complex is simply connected and connected (Tits' lemma, CCKW T2:
  `CCKWTits.cckwCosetComplex_simplyConnected`, `CCKWTits.cckwCosetComplex_connected`);
* `hhyp` — `GHB(7)` is hyperbolic (CCKW Theorem 3.1(i)).
-/

namespace GroupApproximation
namespace KMSGroup

/-- **CCKW Theorem 3.1(ii), cyclic case, for `GHB(7)`**, over the fixed-clique theorem and Tits'
lemma, with the orders of `U₃(7)`, `U₄(7)` spent. -/
theorem cckwFiniteOrderConjugateIntoVertex_of_fixedCliqueTits
    (hT6 : CCKW.SystolicInvariantCliqueStatement)
    (hsc : Systolic.SimplyConnected CCKW.cosetComplex) (hconn : CCKW.cosetComplex.G.Connected) :
    CCKWFiniteOrderConjugateIntoVertex :=
  CCKW.cckwFiniteOrderConjugateIntoVertex_of_systolicLeaves hT6 hsc hconn card_U3_seven_le
    card_U4_seven_le

/-- **`SharpExistence` from `GHB(7)`**, over the fixed-clique theorem, Tits' lemma and
hyperbolicity. -/
theorem sharpExistence_ghb7_of_fixedCliqueTitsHyp (hT6 : CCKW.SystolicInvariantCliqueStatement)
    (hsc : Systolic.SimplyConnected CCKW.cosetComplex) (hconn : CCKW.cosetComplex.G.Connected)
    (hhyp : Hyperbolic.IsHyperbolicGroup (GHB 7)) : Hyperbolic.SharpExistence :=
  GHBQuotient.sharpExistence_of_ghb7ConjHyp
    (cckwFiniteOrderConjugateIntoVertex_of_fixedCliqueTits hT6 hsc hconn) hhyp

end KMSGroup
end GroupApproximation

#audit_axioms GroupApproximation.KMSGroup.cckwFiniteOrderConjugateIntoVertex_of_fixedCliqueTits
#audit_axioms GroupApproximation.KMSGroup.sharpExistence_ghb7_of_fixedCliqueTitsHyp
