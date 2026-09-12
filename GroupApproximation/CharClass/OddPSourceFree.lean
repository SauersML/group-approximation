import GroupApproximation.CharClass.OddPSourceFunctor
import GroupApproximation.CharClass.AcyclicModels

/-!
# The odd-primary source is free on the standard simplices

This is the first of the two hypotheses the acyclic-models theorem consumes, and
it costs nothing, because of the indexing chosen two files back.

`FreeOnModels` wants, in degree `k`, a `Λ`-basis of the carrier indexed by pairs
of a basis index `b : B k` and a morphism `M (mdl k b) ⟶ X`.  Taking the models
to be the standard topological simplices and `B k := Fin (k + 1)`, the simplex
degree, that index type is `Σ n : Fin (k+1), (stdSimplexTop n.val ⟶ X)`, which
is `WSIndex k X` **on the nose**.  So the basis is `Finsupp.basisSingleOne` with
no reindexing, and `basis_apply` is `Category.id_comp`.

Nothing here mentions `p` beyond the coefficient ring: freeness is insensitive to
the differential, so the alternating resolution scalar and the Koszul sign play
no part.  This file is `CartanSourceFunctor.srcFree` with the ring changed.
-/

namespace GroupApproximation.CharClass

open CategoryTheory

noncomputable section

variable (p : ℕ) (data : OddPBoundaryData p)

/-- **The odd-primary source is free on the standard simplices.** -/
def oddSrcFree :
    FreeOnModels stdSimplexTop (GroupRingZMod p) (oddSrc p data) where
  B k := Fin (k + 1)
  mdl _ j := j.val
  gen k j := Finsupp.single
    (⟨j, 𝟙 (stdSimplexTop j.val)⟩ : WSIndex k (stdSimplexTop j.val))
    (1 : GroupRingZMod p)
  basis X k := Finsupp.basisSingleOne
  basis_apply X k j φ := by
    rw [oddSrc_map_single]
    show Finsupp.single (⟨j, φ⟩ : WSIndex k X) (1 : GroupRingZMod p)
      = Finsupp.single (⟨j, 𝟙 (stdSimplexTop j.val) ≫ φ⟩ : WSIndex k X) 1
    rw [Category.id_comp]

end

end GroupApproximation.CharClass
