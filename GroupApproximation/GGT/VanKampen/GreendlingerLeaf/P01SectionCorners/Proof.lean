import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.Corners
import GroupApproximation.Meta.AxiomGuard

/-!
# Section corners: at most `4 n`

`OsinLemma94SectionCornersInput` (`Estimating/OsinLemma94ContactWords`), with `eps0 = 0`, `K = 4`,
`rho0 = 1`.  Let `n` be the number of relator cells and `X = S.diagram` (also with `n` cells).

* The section corners over the relator polygons form the finite set `cornerSet P` of pairs
  `(k, s)`; its cardinality is the sum of the statement (`card_cornerSet`).
* Every element is a corner at one of the `r ≤ 4` cut positions `cut i`, `i < r`
  (`exists_cornerAt`), so `cornerSet P` is covered by the `r` sets of corners at a cut position.
* On the corners at one cut position, the charged cell `charge P (k, s).1` is injective
  (`eq_of_cornerAt`), so each of these sets has at most `n` elements (`card_filter_cornerAt_le`).

Hence `#cornerSet P ≤ r n ≤ 4 n`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners

universe u w v

open scoped Classical

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- The section corners of the relator polygons, as pairs (polygon, side). -/
noncomputable def cornerSet (P : OsinLemma94RealizedPolygons S) :
    Finset (Σ _ : Fin P.count, ℕ) :=
  P.relatorPolygons.sigma fun k => P.sectionCorners k

theorem card_cornerSet (P : OsinLemma94RealizedPolygons S) :
    (cornerSet P).card = ∑ k ∈ P.relatorPolygons, (P.sectionCorners k).card :=
  Finset.card_sigma _ _

/-- **The corners at one cut position number at most `n`.** -/
theorem card_filter_cornerAt_le (P : OsinLemma94RealizedPolygons S)
    (hpos : 0 < S.diagram.rCellCount) (t : ℕ) :
    ((cornerSet P).filter fun a => CornerAt P a t).card ≤ S.diagram.rCellCount := by
  have hinj : Set.InjOn (fun a : Σ _ : Fin P.count, ℕ => charge P hpos a.1)
      (↑((cornerSet P).filter fun a => CornerAt P a t) : Set (Σ _ : Fin P.count, ℕ)) := by
    intro a ha a' ha' heq
    have hm := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
    have hm' := Finset.mem_filter.mp (Finset.mem_coe.mp ha')
    have hs : a ∈ P.relatorPolygons.sigma fun k => P.sectionCorners k := hm.1
    have hs' : a' ∈ P.relatorPolygons.sigma fun k => P.sectionCorners k := hm'.1
    exact eq_of_cornerAt P hpos (Finset.mem_sigma.mp hs).1 (Finset.mem_sigma.mp hs').1 hm.2 hm'.2
      heq
  have hmaps : Set.MapsTo (fun a : Σ _ : Fin P.count, ℕ => charge P hpos a.1)
      (↑((cornerSet P).filter fun a => CornerAt P a t) : Set (Σ _ : Fin P.count, ℕ))
      (↑(Finset.univ : Finset (Fin S.diagram.rCellCount)) : Set (Fin S.diagram.rCellCount)) := by
    intro a _
    exact Finset.mem_coe.mpr (Finset.mem_univ _)
  have h := Finset.card_le_card_of_injOn _ hmaps hinj
  rwa [Finset.card_fin] at h

/-- **The section corners number at most `r n`.** -/
theorem card_cornerSet_le (P : OsinLemma94RealizedPolygons S)
    (hpos : 0 < S.diagram.rCellCount) :
    (cornerSet P).card ≤ cuts.count * S.diagram.rCellCount := by
  have hsub : cornerSet P ⊆ Finset.univ.biUnion fun i : Fin cuts.count =>
      (cornerSet P).filter fun a => CornerAt P a (cuts.cut i.castSucc) := by
    rintro ⟨k, s⟩ ha
    have hs : (⟨k, s⟩ : Σ _ : Fin P.count, ℕ) ∈
        P.relatorPolygons.sigma fun k => P.sectionCorners k := ha
    obtain ⟨i, hi⟩ := exists_cornerAt P (Finset.mem_sigma.mp hs).2
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨ha, hi⟩⟩
  have h := Finset.card_biUnion_le_card_mul Finset.univ
    (fun i : Fin cuts.count => (cornerSet P).filter fun a => CornerAt P a (cuts.cut i.castSucc))
    S.diagram.rCellCount (fun i _ => card_filter_cornerAt_le P hpos (cuts.cut i.castSucc))
  rw [Finset.card_fin] at h
  exact (Finset.card_le_card hsub).trans h

/-- **The section corners over the relator polygons number at most `4 n`.** -/
theorem sum_sectionCorners_le (P : OsinLemma94RealizedPolygons S)
    (hpos : 0 < Delta.rCellCount) :
    ∑ k ∈ P.relatorPolygons, (P.sectionCorners k).card ≤ 4 * Delta.rCellCount := by
  have hpos' : 0 < S.diagram.rCellCount := by
    rw [S.equiv.rCellCount_eq]
    exact hpos
  have h := (card_cornerSet_le P hpos').trans
    (Nat.mul_le_mul_right S.diagram.rCellCount cuts.count_le)
  rwa [card_cornerSet, S.equiv.rCellCount_eq] at h

/-- **Lemma 9.4, the section corners.** -/
theorem proof : OsinLemma94SectionCornersInput.{u, w, v} := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _
  refine ⟨0, fun _ _ => ⟨4, 1, Nat.one_pos, ?_⟩⟩
  intro _ _ _ _ Delta cuts _ hpos _ S _ _ P _
  exact sum_sectionCorners_le (Delta := Delta) (cuts := cuts) (S := S) P hpos

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.proof
