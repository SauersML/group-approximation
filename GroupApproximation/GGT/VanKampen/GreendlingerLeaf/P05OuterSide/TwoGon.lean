import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterSide.Transport
import GroupApproximation.Meta.AxiomGuard

/-!
# A clean two-gon carried by a transport of `Φ'_M`

Osin, arXiv:math/0411039v3, Appendix, the assumption before Lemma 9.3: "inside every 2-gon of
`Φ′_M`, there is a vertex of `Φ_M`".

Let `T` carry the regions of a distinguished family `S` to those of `S'` (`RegionTransport`).
`PhiTransportAt T a₀` says that at the component of `a₀`, `phiMapO` is carried isomorphically along
the dart embedding of `T`, and that every face-class path to a relator cell after the step names
one before it.  Then a clean two-gon of `S` is carried to one of `S'`.
* The two-gon is carried: reversal and rotation commute with the correspondence, and regions,
  sides and orientations are those named by the carried crossing darts.
* No corner in the gap: target profiles are kept.
* No relator cell: the face-class paths are named back, and the ends of the component correspond.

* `PhiTransportAt`.
* `hasCleanTwoGon_of_transport`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(a);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterSide

open Equiv Embedded Embedded.RegionCandidate

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- **`Φ'_M` carried at the component of `a₀`**: a correspondence of retained darts along the dart
embedding, commuting with reversal and rotation, under which every face-class path to a relator cell
after the step names one before it. -/
def PhiTransportAt (T : RegionTransport S S') (a₀ : S.family) : Prop :=
  ∃ ι : (phiMapO S.family (linkedComponentO S.family a₀.1)).Dart ≃
      (phiMapO S'.family (linkedComponentO S'.family (T.map a₀))).Dart,
    (∀ y, (ι y).1.1 = T.darts y.1.1) ∧
    (∀ y, ι ((phiMapO S.family (linkedComponentO S.family a₀.1)).alpha y) =
      (phiMapO S'.family (linkedComponentO S'.family (T.map a₀))).alpha (ι y)) ∧
    (∀ y, ι ((phiMapO S.family (linkedComponentO S.family a₀.1)).sigma y) =
      (phiMapO S'.family (linkedComponentO S'.family (T.map a₀))).sigma (ι y)) ∧
    ∀ (y : (phiMapO S.family (linkedComponentO S.family a₀.1)).Dart)
      (x' : (collapsedMap S'.family).dual.Dart) (i' : Fin S'.diagram.rCellCount),
      Relation.EqvGen (CombMap.FaceClassStep (collapsedMap S'.family).dual
          (PhiKeepO S'.family (linkedComponentO S'.family (T.map a₀)))) (ι y).1 x' →
        S'.diagram.toCombMap.faceOf x'.1 = (cell S'.diagram i').face →
        ∃ x : (collapsedMap S.family).dual.Dart,
          Relation.EqvGen (CombMap.FaceClassStep (collapsedMap S.family).dual
              (PhiKeepO S.family (linkedComponentO S.family a₀.1))) y.1 x ∧
            S.diagram.toCombMap.faceOf x.1 = (cell S.diagram (T.cellIndex.symm i')).face

/-- **A clean two-gon is carried by a transport of `Φ'_M`.** -/
theorem hasCleanTwoGon_of_transport (hlea : Delta.LeastArea) (T : RegionTransport S S')
    (hphi : ∀ a₀, PhiTransportAt T a₀) (h : HasCleanTwoGon S) : HasCleanTwoGon S' := by
  obtain ⟨hloops, hmulti, a₀, ha₀, hat, P, f, hf, hcorner, hcell⟩ := h
  obtain ⟨ι, hval, hα, hσ, hsim⟩ := hphi ⟨a₀, ha₀⟩
  have P' : ExtPhiData S'.family (linkedComponentO S'.family (T.map ⟨a₀, ha₀⟩)) :=
    extPhiData_of_leastArea S' (S'.equiv.leastArea hlea) (T.noLoops hloops)
      (linkedComponentO_subset _ _)
  have hmemF : ∀ y : (phiMapO S.family (linkedComponentO S.family a₀)).Dart,
      phiRegionO y ∈ S.family := fun y => linkedComponentO_subset _ _ (phiRegionO_mem y)
  have hreg : ∀ y : (phiMapO S.family (linkedComponentO S.family a₀)).Dart,
      phiRegionO (ι y) = T.map ⟨phiRegionO y, hmemF y⟩ ∧ phiSideO (ι y) = phiSideO y ∧
        phiCellSideO (ι y) = phiCellSideO y := by
    intro y
    refine P'.phiO_eq (ι y) ((T.mem_linkedComponentO_map ⟨a₀, ha₀⟩).mpr
      ⟨⟨phiRegionO y, hmemF y⟩, rfl, phiRegionO_mem y⟩) ?_
    rw [T.cross, hval]
    exact congrArg (Option.map T.darts) (phiO_cross y)
  have hfp : ∀ y : (phiMapO S.family (linkedComponentO S.family a₀)).Dart,
      ι ((phiMapO S.family (linkedComponentO S.family a₀)).facePerm y) =
        (phiMapO S'.family (linkedComponentO S'.family (T.map ⟨a₀, ha₀⟩))).facePerm (ι y) := by
    intro y
    simp only [CombMap.facePerm, Perm.mul_apply]
    rw [hσ, hα]
  have hpow : ∀ (n : ℕ) (y : (phiMapO S.family (linkedComponentO S.family a₀)).Dart),
      ι (((phiMapO S.family (linkedComponentO S.family a₀)).facePerm ^ n) y) =
        ((phiMapO S'.family (linkedComponentO S'.family (T.map ⟨a₀, ha₀⟩))).facePerm ^ n)
          (ι y) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      simp only [pow_succ', Perm.mul_apply]
      rw [hfp, ih]
  have hfaceback : ∀ y z : (phiMapO S.family (linkedComponentO S.family a₀)).Dart,
      (phiMapO S'.family (linkedComponentO S'.family (T.map ⟨a₀, ha₀⟩))).faceOf (ι y) =
          (phiMapO S'.family (linkedComponentO S'.family (T.map ⟨a₀, ha₀⟩))).faceOf (ι z) →
        (phiMapO S.family (linkedComponentO S.family a₀)).faceOf y =
          (phiMapO S.family (linkedComponentO S.family a₀)).faceOf z := by
    intro y z hyz
    rw [CombMap.faceOf_eq_iff] at hyz ⊢
    obtain ⟨n, hn⟩ := hyz.exists_nat_pow_eq
    rw [← hpow] at hn
    exact ⟨n, by rw [zpow_natCast]; exact ι.injective hn⟩
  obtain ⟨d, hdcell, hdf, hd4, hdreg⟩ := hf
  refine ⟨T.noLoops hloops, T.noMultipleEdges hmulti, T.map ⟨a₀, ha₀⟩, T.map_mem _,
    by rw [T.target, hat]; rfl, P',
    (phiMapO S'.family (linkedComponentO S'.family (T.map ⟨a₀, ha₀⟩))).faceOf (ι d),
    ⟨ι d, (hreg d).2.2.trans hdcell, rfl, by rw [← hfp, ← hfp, ← hfp, ← hfp, hd4], ?_⟩, ?_, ?_⟩
  · intro heq
    apply hdreg
    have h2 : phiRegionO (ι ((phiMapO S.family (linkedComponentO S.family a₀)).facePerm
        ((phiMapO S.family (linkedComponentO S.family a₀)).facePerm d))) = phiRegionO (ι d) := by
      rw [hfp, hfp]
      exact heq
    rw [(hreg _).1, (hreg d).1] at h2
    exact congrArg Subtype.val (T.map.injective h2)
  · rintro ⟨y', hy'f, hcs, hnone, k, hgap⟩
    obtain ⟨y, rfl⟩ := ι.surjective y'
    refine hcorner ⟨y, (hfaceback y d hy'f).trans hdf, (hreg y).2.2.symm.trans hcs, ?_, k, ?_⟩
    · rw [(hreg y).1, (hreg y).2.1, T.sideCellO_map] at hnone
      exact Option.map_eq_none_iff.mp hnone
    · rw [← hfp, ← hfp, (hreg y).1, (hreg _).1] at hgap
      obtain ⟨-, hs1, hl1, -⟩ := T.profile ⟨phiRegionO y, hmemF y⟩
      obtain ⟨-, hs2, hl2, -⟩ := T.profile ⟨phiRegionO
        ((phiMapO S.family (linkedComponentO S.family a₀)).facePerm
          ((phiMapO S.family (linkedComponentO S.family a₀)).facePerm y)), hmemF _⟩
      simp only [GapHoldsCorner] at hgap ⊢
      rw [hs1, hl1, hs2, hl2] at hgap
      exact hgap
  · rintro ⟨i', hi', d', hd'f, x', hpath, hx'face⟩
    obtain ⟨z, rfl⟩ := ι.surjective d'
    obtain ⟨x, hpathx, hxface⟩ := hsim z x' i' hpath hx'face
    refine hcell ⟨T.cellIndex.symm i', fun hmem => hi' ?_, z, (hfaceback z d hd'f).trans hdf, x,
      hpathx, hxface⟩
    obtain ⟨b, hb, s, hbs⟩ := mem_endCellsO.mp hmem
    refine mem_endCellsO.mpr ⟨T.map ⟨b, linkedComponentO_subset _ _ hb⟩,
      (T.mem_linkedComponentO_map ⟨a₀, ha₀⟩).mpr ⟨_, rfl, hb⟩, s, ?_⟩
    rw [T.sideCellO_map]
    change Option.map T.cellIndex (sideCellO b s) = some i'
    rw [hbs]
    simp

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterSide

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterSide.PhiTransportAt
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterSide.hasCleanTwoGon_of_transport
