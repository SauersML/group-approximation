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

/-- Decode the positive/negative pairs supplied to the natural search graph. -/
def signedSearchTuple (n : ℕ) (a : List.Vector ℕ (2 * n + 1)) : Fin n → ℤ :=
  fun i => natDiffZ (a.get ⟨2 * i.val, by omega⟩)
    (a.get ⟨2 * i.val + 1, by omega⟩)

def signedSearchWitness (n : ℕ) (a : List.Vector ℕ (2 * n + 1)) : ℕ :=
  a.get ⟨2 * n, by omega⟩

/-- The Boolean matrix, encoded as the natural output `0` or `1`. -/
def signedSearchFn (n : ℕ) (search : (Fin n → ℤ) → ℕ → Bool)
    (a : List.Vector ℕ (2 * n + 1)) : ℕ :=
  Encodable.encode (search (signedSearchTuple n a) (signedSearchWitness n a))

theorem primrec'_signedSearchFn (n : ℕ) (search : (Fin n → ℤ) → ℕ → Bool)
    (hsearch : Primrec₂ search) : Nat.Primrec' (signedSearchFn n search) := by
  have htuple : Primrec (signedSearchTuple n) := by
    have hi : Primrec₂ fun (i : Fin n) (a : List.Vector ℕ (2 * n + 1)) =>
        natDiffZ (a.get ⟨2 * i.val, by omega⟩)
          (a.get ⟨2 * i.val + 1, by omega⟩) :=
      Primrec.fin_curry₁.2 fun i => primrec_natDiffZ.comp
        (Primrec.vector_get.comp Primrec.id
          (Primrec.const (⟨2 * i.val, by omega⟩ : Fin (2 * n + 1))))
        (Primrec.vector_get.comp Primrec.id
          (Primrec.const (⟨2 * i.val + 1, by omega⟩ : Fin (2 * n + 1))))
    exact Primrec.fin_curry.2 (hi.comp Primrec.snd Primrec.fst)
  have hwitness : Primrec (signedSearchWitness n) :=
    Primrec.vector_get.comp Primrec.id
      (Primrec.const (⟨2 * n, by omega⟩ : Fin (2 * n + 1)))
  have hb : Primrec fun a : List.Vector ℕ (2 * n + 1) =>
      search (signedSearchTuple n a) (signedSearchWitness n a) :=
    hsearch.comp htuple hwitness
  exact Nat.Primrec'.of_prim (Primrec.encode.comp hb)

theorem higmanGenerated_signedSearch (n : ℕ)
    (search : (Fin n → ℤ) → ℕ → Bool) (hsearch : Primrec₂ search) :
    HigmanGenerated (signedSearchProjection n (signedSearchFn n search)) :=
  higmanGenerated_signedSearchProjection n _
    (higmanGenerated_natGraph_of_primrec' (primrec'_signedSearchFn n search hsearch))

end Seq
end Higman
end GroupApproximation
