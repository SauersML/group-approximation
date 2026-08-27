import GroupApproximation.Higman.HigmanPrimitiveRecursiveRunSemantics
import GroupApproximation.Higman.TraceRelationRE
import GroupApproximation.Higman.REPredNormalForm

/-!
# The unconditional bounded-window theorem

Integer inputs are represented by differences of two natural auxiliary
coordinates.  The signed input itself is retained, while all natural codes,
the search witness, and the Boolean output are existentially forgotten.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

/-- Place `addGraph` as `positive = signed + negative`. -/
def signedInputCoord (n : ℕ) (i : Fin n) (j : ℕ) : ℤ :=
  if j = 0 then (i.val : ℤ)
  else if j = 1 then ((n + 2 * i.val + 1 : ℕ) : ℤ)
  else ((n + 2 * i.val : ℕ) : ℤ)

/-- Place a natural graph in the contiguous auxiliary interval beginning at
`n`.  Its `2n+1` inputs are the positive/negative pairs and search witness;
its last coordinate is the Boolean output. -/
def signedSearchCoord (n : ℕ) (j : ℕ) : ℤ := ((n + j : ℕ) : ℤ)

noncomputable def signedSearchAssembly (n : ℕ)
    (Q : List.Vector ℕ (2 * n + 1) → ℕ) : Set E :=
  (⋂ i ∈ (Finset.univ : Finset (Fin n)),
      placeAt 3 (signedInputCoord n i) addGraph) ∩
    placeAt (2 * n + 2) (signedSearchCoord n) (natGraph Q) ∩
      pinAt ((n + (2 * n + 1) : ℕ) : ℤ) 1

noncomputable def signedSearchProjection (n : ℕ)
    (Q : List.Vector ℕ (2 * n + 1) → ℕ) : Set E :=
  freeAux (2 * n + 2) n (signedSearchAssembly n Q) ∩ windowSupport n

theorem higmanGenerated_signedSearchProjection (n : ℕ)
    (Q : List.Vector ℕ (2 * n + 1) → ℕ)
    (hQ : HigmanGenerated (natGraph Q)) :
    HigmanGenerated (signedSearchProjection n Q) := by
  classical
  unfold signedSearchProjection signedSearchAssembly
  refine HigmanGenerated.inter (higmanGenerated_freeAux (2 * n + 2) n ?_)
    (higmanGenerated_windowSupport n)
  exact HigmanGenerated.inter
    (HigmanGenerated.inter
      (higmanGenerated_biInter Finset.univ
        (fun i : Fin n => placeAt 3 (signedInputCoord n i) addGraph)
        (fun i _ => higmanGenerated_placeAt 3 (signedInputCoord n i) addGraph
          higmanGenerated_addGraph_unconditional))
      (higmanGenerated_placeAt (2 * n + 2) (signedSearchCoord n)
        (natGraph Q) hQ))
    (higmanGenerated_pinAt ((n + (2 * n + 1) : ℕ) : ℤ) 1)

end Seq
end Higman
end GroupApproximation
