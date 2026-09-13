import GroupApproximation.Kazhdan.CCKWSystolicInvariantClique
import GroupApproximation.GGT.SystolicDiscZip
import GroupApproximation.GGT.SystolicDiscMirrorFoldDistinct
import GroupApproximation.Meta.AxiomGuard

/-!
# The fixed-clique theorem over the pinched mirror fold

`CCKW.systolicInvariantClique_of_zipFold` proves `CCKW.SystolicInvariantCliqueStatement` from
HC3(d) and HC6 at every triangle complex.  Two of the three every-`X` producers are closed:

* `Systolic.zipSpurStatement : ZipSpurStatement X` (HC3(d));
* `Systolic.mirrorFoldDistinct X : MirrorFoldDistinctStatement X` (HC6, distinct third vertices).

Only HC6 at a common third vertex stays open, as the hypothesis `hpinch`.

* `CCKW.systolicInvariantClique_of_pinched`: T6 from `MirrorFoldPinchedStatement` at every `X`.
* `CCKW.cckwFiniteOrderConjugateIntoVertex_of_pinched`: CCKW Theorem 3.1(ii), cyclic case, from
  `MirrorFoldPinchedStatement` at `CCKW.cosetComplex` alone.

## Manuscript status

Infrastructure for the torsion-free hyperbolic property (T) witness on the
Kotowski--Ollivier route; certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace KMSGroup
namespace CCKW

/-- **The fixed-clique theorem for systolic complexes, over the pinched mirror fold.**  HC3(d)
and the distinct case of HC6 are proved at every triangle complex. -/
theorem systolicInvariantClique_of_pinched
    (hpinch : ∀ (V : Type) (X : Systolic.TriangleComplex V),
      Systolic.MirrorFoldPinchedStatement X) :
    SystolicInvariantCliqueStatement :=
  systolicInvariantClique_of_zipFold (fun _ _ => Systolic.zipSpurStatement)
    (fun V X => Systolic.mirrorFoldStatement_of_cases (Systolic.mirrorFoldDistinct X) (hpinch V X))

/-- **Finite-order elements of `GHB(7)` conjugate into a vertex group**, over the pinched mirror
fold at the coset complex. -/
theorem cckwFiniteOrderConjugateIntoVertex_of_pinched
    (hpinch : Systolic.MirrorFoldPinchedStatement cosetComplex) :
    CCKWFiniteOrderConjugateIntoVertex :=
  cckwFiniteOrderConjugateIntoVertex_of_zipFold zipSpur_cosetComplex
    (Systolic.mirrorFoldStatement_of_cases (Systolic.mirrorFoldDistinct cosetComplex) hpinch)

end CCKW
end KMSGroup
end GroupApproximation

open GroupApproximation.KMSGroup

#audit_axioms CCKW.systolicInvariantClique_of_pinched
#audit_axioms CCKW.cckwFiniteOrderConjugateIntoVertex_of_pinched
