import GroupApproximation.Manuscript.NonMF.GerasimovaOsinProposition41
import GroupApproximation.Manuscript.NonMF.GerasimovaOsinLemma42Proof
import GroupApproximation.Meta.AxiomGuard

/-!
# Gerasimova–Osin, Theorem 1.1, closed

`cor:regular-nonmf-algebra` (tex 1729–1731):

> Gerasimova and Osin give density of the invertible elements, which is stable rank
> one~\cite[Theorem~1.1]{GO}.

`GerasimovaOsinTheorem11Printed` is density of the invertible elements of `C*_r(G)` for an
acylindrically hyperbolic countable group with trivial finite radical.  It is proved here
along Gerasimova–Osin's own argument:

* §5: Dykema–de la Harpe's Theorem 1.4 (`dykemaDeLaHarpeTheorem14`), proved from Rørdam's
  norm-one distance-one element (`RordamDistanceOne`) and the faithful canonical trace;
* §2: Proposition 2.4, the norm estimate from a generalized combing
  (`GerasimovaOsinCombingNorm`);
* §4: Proposition 4.1 from Lemmas 4.3–4.8 (`gerasimovaOsinProposition41_of_lemma42`);
* Lemma 4.2 in its two-sided form (`gerasimovaOsinLemma42`).

## Manuscript status

Closes `GerasimovaOsinTheorem11Printed`, the Gerasimova–Osin input of
`cor:regular-nonmf-algebra`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

/-- **Gerasimova–Osin, Theorem 1.1**: the invertible elements of `C*_r(G)` are dense. -/
theorem gerasimovaOsinTheorem11Printed : GerasimovaOsinTheorem11Printed :=
  gerasimovaOsinTheorem11Printed_of_lemma42 gerasimovaOsinLemma42

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation

#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.gerasimovaOsinTheorem11Printed
