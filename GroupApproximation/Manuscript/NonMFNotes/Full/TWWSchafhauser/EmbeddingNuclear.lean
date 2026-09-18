import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingConnes
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingEndpoint

/-!
# Separable nuclear C⋆-algebras embed tracially into `Q^ω`

Lane TWWSch3b1 (work order WO-TWWSch-3b-1).  Manuscript: `non_mf_group_notes.tex`, the
Tikuisis--White--Winter input.  Sources: Brown--Ozawa, Thm 6.2.7, and C. Schafhauser,
*A new proof of the Tikuisis--White--Winter theorem*, J. reine angew. Math. 759 (2020), §3.

A faithful trace on a separable nuclear C⋆-algebra is amenable
(`isAmenableTrace_of_isNuclearCStarAlgebra`), so it has a trace-preserving embedding with
a ucp lift (`hasTracialEmbedding_of_isAmenableTrace`).
-/

namespace GroupApproximation.Full.TWWSchafhauser

universe u

/-- **Tracial embedding of a separable nuclear C⋆-algebra** (Schafhauser §3 with
Brown--Ozawa 6.2.7). -/
theorem hasTracialEmbedding_of_isNuclearCStarAlgebra {A : Type u} [CStarAlgebra A]
    [TopologicalSpace.SeparableSpace A]
    (hnuc : CStarExactness.IsNuclearCStarAlgebra A) (τ : FaithfulTracialState A) :
    HasTracialEmbedding (fun a : A => τ a) :=
  hasTracialEmbedding_of_isAmenableTrace (isAmenableTrace_of_isNuclearCStarAlgebra hnuc τ)
    τ.map_one

end GroupApproximation.Full.TWWSchafhauser
