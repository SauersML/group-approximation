import GroupApproximation.Manuscript.NonMF.GerasimovaOsinGeometricInputs
import GroupApproximation.GGT.GerasimovaOsinCyclicTwoSided
import GroupApproximation.Meta.AxiomGuard

/-!
# Gerasimova--Osin's Lemma 4.2, proved

`Manuscript/NonMF/GerasimovaOsinGeometricInputs` fixes Gerasimova and Osin's
Lemma 4.2 with the standing choices of their §4 as
`GerasimovaOsinLemma42Statement`:

> There exists an infinite cyclic subgroup `H ↪h G` such that
> `F H F⁻¹ ∩ H = {1}`.

This module proves it: `H = ⟨y⟩` with `H ↪_h (G, X)` for a symmetric `X ⊇ F`,
and the intersection condition in its two-sided form
(`GGT.CyclicTwoSided.exists_cyclic_hypEmbedded_twoSided`).  The proof is one
product of deep powers of four detectors and DGO Lemma 4.21(a).  It replaces
Gerasimova--Osin's free subgroup from DGO Theorem 6.14 and its transfer through
DGO Proposition 4.35.

## Manuscript status

The hyperbolically embedded input of *"Gerasimova and Osin give density of the
invertible elements, which is stable rank one"* (`cor:regular-nonmf-algebra`).
The printed route runs through Gerasimova--Osin's own proof, so the census
status is `partial` (different route), not `formalized`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.GGT
open GroupApproximation.GGT.OsinComponents

/-- **Gerasimova--Osin, Lemma 4.2**, with `H = ⟨y⟩ ↪_h (G, X)`, `X ⊇ F` symmetric
and `F H F⁻¹ ∩ H = {1}` two-sided. -/
theorem gerasimovaOsinLemma42 : GerasimovaOsinLemma42Statement := by
  intro G _instG _instC _instAH hrad F hF
  exact GGT.CyclicTwoSided.exists_cyclic_hypEmbedded_twoSided G hrad F hF

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation

#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.gerasimovaOsinLemma42
