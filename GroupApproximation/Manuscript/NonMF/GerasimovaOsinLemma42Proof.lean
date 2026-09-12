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
(`GGT.CyclicTwoSided.exists_cyclic_hypEmbedded_twoSided`).

Route note: one product of deep powers of four detectors and DGO Lemma 4.21(a),
in place of Gerasimova--Osin's free subgroup (DGO Theorem 6.14, Proposition 4.35).

## Manuscript status

The hyperbolically embedded input of Gerasimova--Osin's Theorem 1.1, which
`cor:regular-nonmf-algebra` cites (*"Gerasimova and Osin give density of the
invertible elements, which is stable rank one"*).  Lemma 4.2 is internal to that
cited proof, so it carries no census row of its own.  The row for the printed
sentence follows the closed `GerasimovaOsinTheorem11Printed` producer.
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
