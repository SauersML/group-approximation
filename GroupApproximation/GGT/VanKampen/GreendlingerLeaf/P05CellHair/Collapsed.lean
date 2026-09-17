import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.TwoGon
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhiMapTransportDual
import GroupApproximation.Meta.AxiomGuard

/-!
# `Φ'_M` carried by an embedding of the collapsed maps

Osin, arXiv:math/0411039v3, Appendix, the assumption before Lemma 9.3: "inside every 2-gon of
`Φ′_M`, there is a vertex of `Φ_M`".

Let `T` carry the regions of `S` to those of `S'`, and let `ιc` embed the collapsed map of `S`
into that of `S'` along the dart embedding of `T`.  The crossing darts of the component of `a₀`
go exactly to the crossing darts of the carried component.  If the face rotations agree along
`ιc`, up to a detour past one dart that is not a crossing, `phiMapO` is carried; with a way to
name face-class paths back, `PhiTransportAt T a₀` holds.

* `not_regionInternal_of_crossO`: a crossing dart is in the collapsed map.
* `phiKeepO_map_iff`, `phiKeepO_range`.
* `phiTransportAt_of_bypass`, `phiTransportAt_of_semiconj`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(a);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair

open Equiv Embedded Embedded.RegionCandidate PhiMapTransport

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- **A crossing dart is in the collapsed map.** -/
theorem not_regionInternal_of_crossO
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {a : RegionCandidate D eps S.diagram} (ha : a ∈ S.family) {s o : Bool}
    {d : S.diagram.toCombMap.Dart} (hd : crossO a s o = some d) : ¬ RegionInternal S.family d := by
  cases o with
  | false => exact not_regionInternal_of_mem_cycle S.pairwise ha (mem_cycle_crossO_false a hd)
  | true =>
    have h' : crossO a s false = some (S.diagram.toCombMap.alpha d) :=
      (crossO_alpha a s true d).mpr hd
    rw [← regionInternal_alpha S.family d]
    exact not_regionInternal_of_mem_cycle S.pairwise ha (mem_cycle_crossO_false a h')

/-- **The crossings of the carried component are the carried crossings.** -/
theorem phiKeepO_map_iff (T : RegionTransport S S') (a₀ : S.family)
    (ιc : (collapsedMap S.family).Dart ↪ (collapsedMap S'.family).Dart)
    (hιc : ∀ x, (ιc x).1 = T.darts x.1) (x : (collapsedMap S.family).Dart) :
    PhiKeepO S'.family (linkedComponentO S'.family (T.map a₀)) (ιc x) ↔
      PhiKeepO S.family (linkedComponentO S.family a₀.1) x := by
  constructor
  · rintro ⟨b', hb', s, o, h⟩
    obtain ⟨b, rfl, hb⟩ := (T.mem_linkedComponentO_map a₀).mp hb'
    refine ⟨b.1, hb, s, o, ?_⟩
    rw [T.cross, hιc] at h
    obtain ⟨d, hd, hdx⟩ := Option.map_eq_some_iff.mp h
    rw [hd, T.darts.injective hdx]
  · rintro ⟨b, hb, s, o, h⟩
    refine ⟨T.map ⟨b, linkedComponentO_subset _ _ hb⟩,
      (T.mem_linkedComponentO_map a₀).mpr ⟨_, rfl, hb⟩, s, o, ?_⟩
    rw [T.cross, hιc]
    exact congrArg (Option.map T.darts) h

/-- **Every crossing of the carried component is carried.** -/
theorem phiKeepO_range (T : RegionTransport S S') (a₀ : S.family)
    (ιc : (collapsedMap S.family).Dart ↪ (collapsedMap S'.family).Dart)
    (hιc : ∀ x, (ιc x).1 = T.darts x.1) (x' : (collapsedMap S'.family).Dart)
    (h : PhiKeepO S'.family (linkedComponentO S'.family (T.map a₀)) x') : x' ∈ Set.range ιc := by
  obtain ⟨b', hb', s, o, hx⟩ := h
  obtain ⟨b, rfl, hb⟩ := (T.mem_linkedComponentO_map a₀).mp hb'
  rw [T.cross] at hx
  obtain ⟨d, hd, hdx⟩ := Option.map_eq_some_iff.mp hx
  exact ⟨⟨d, not_regionInternal_of_crossO S b.2 hd⟩, Subtype.ext ((hιc _).trans hdx)⟩

/-- **`Φ'_M` is carried when the face rotations agree up to a detour past a non-crossing dart.** -/
theorem phiTransportAt_of_bypass (T : RegionTransport S S') (a₀ : S.family)
    (ιc : (collapsedMap S.family).Dart ↪ (collapsedMap S'.family).Dart)
    (hιc : ∀ x, (ιc x).1 = T.darts x.1)
    (hαc : ∀ x, ιc ((collapsedMap S.family).alpha x) = (collapsedMap S'.family).alpha (ιc x))
    {w : (collapsedMap S.family).Dart} {s : (collapsedMap S'.family).Dart}
    (hs : s ∉ Set.range ιc) (hw : ¬ PhiKeepO S.family (linkedComponentO S.family a₀.1) w)
    (h0 : (collapsedMap S.family).facePerm w ≠ w)
    (h1 : ∀ x, x ≠ w → (collapsedMap S.family).facePerm x ≠ w →
      (collapsedMap S'.family).facePerm (ιc x) = ιc ((collapsedMap S.family).facePerm x))
    (h2 : ∀ x, x ≠ w → (collapsedMap S.family).facePerm x = w →
      (collapsedMap S'.family).facePerm (ιc x) = s)
    (h3 : (collapsedMap S'.family).facePerm s = ιc ((collapsedMap S.family).facePerm w))
    (back : (collapsedMap S'.family).Dart → (collapsedMap S.family).Dart)
    (hback : ∀ x, back (ιc x) = x)
    (hsim : ∀ x' y', Relation.EqvGen (CombMap.FaceClassStep (collapsedMap S'.family).dual
        (PhiKeepO S'.family (linkedComponentO S'.family (T.map a₀)))) x' y' →
      Relation.EqvGen (CombMap.FaceClassStep (collapsedMap S.family).dual
        (PhiKeepO S.family (linkedComponentO S.family a₀.1))) (back x') (back y'))
    (hcell : ∀ (x' : (collapsedMap S'.family).Dart) (i' : Fin S'.diagram.rCellCount),
      S'.diagram.toCombMap.faceOf x'.1 = (cell S'.diagram i').face →
        S.diagram.toCombMap.faceOf (back x').1 = (cell S.diagram (T.cellIndex.symm i')).face) :
    PhiTransportAt T a₀ := by
  refine ⟨retainedEquiv ιc phiKeepO_alpha phiKeepO_alpha (phiKeepO_map_iff T a₀ ιc hιc)
      (phiKeepO_range T a₀ ιc hιc), fun y => hιc y.1,
    retainedEquiv_alpha ιc phiKeepO_alpha phiKeepO_alpha (phiKeepO_map_iff T a₀ ιc hιc)
      (phiKeepO_range T a₀ ιc hιc) hαc,
    fun y => (retainedEquiv_sigma_bypass ιc phiKeepO_alpha phiKeepO_alpha
      (phiKeepO_map_iff T a₀ ιc hιc) (phiKeepO_range T a₀ ιc hιc) hs hw h0 h1 h2 h3 y).symm, ?_⟩
  intro y x' i' hpath hface
  have h1' : Relation.EqvGen (CombMap.FaceClassStep (collapsedMap S.family).dual
      (PhiKeepO S.family (linkedComponentO S.family a₀.1))) (back (ιc y.1)) (back x') :=
    hsim _ _ hpath
  rw [hback] at h1'
  exact ⟨back x', h1', hcell x' i' hface⟩

/-- **`Φ'_M` is carried when the face rotations agree along the embedding.** -/
theorem phiTransportAt_of_semiconj (T : RegionTransport S S') (a₀ : S.family)
    (ιc : (collapsedMap S.family).Dart ↪ (collapsedMap S'.family).Dart)
    (hιc : ∀ x, (ιc x).1 = T.darts x.1)
    (hαc : ∀ x, ιc ((collapsedMap S.family).alpha x) = (collapsedMap S'.family).alpha (ιc x))
    (h : ∀ x, (collapsedMap S'.family).facePerm (ιc x) = ιc ((collapsedMap S.family).facePerm x))
    (back : (collapsedMap S'.family).Dart → (collapsedMap S.family).Dart)
    (hback : ∀ x, back (ιc x) = x)
    (hsim : ∀ x' y', Relation.EqvGen (CombMap.FaceClassStep (collapsedMap S'.family).dual
        (PhiKeepO S'.family (linkedComponentO S'.family (T.map a₀)))) x' y' →
      Relation.EqvGen (CombMap.FaceClassStep (collapsedMap S.family).dual
        (PhiKeepO S.family (linkedComponentO S.family a₀.1))) (back x') (back y'))
    (hcell : ∀ (x' : (collapsedMap S'.family).Dart) (i' : Fin S'.diagram.rCellCount),
      S'.diagram.toCombMap.faceOf x'.1 = (cell S'.diagram i').face →
        S.diagram.toCombMap.faceOf (back x').1 = (cell S.diagram (T.cellIndex.symm i')).face) :
    PhiTransportAt T a₀ := by
  refine ⟨retainedEquiv ιc phiKeepO_alpha phiKeepO_alpha (phiKeepO_map_iff T a₀ ιc hιc)
      (phiKeepO_range T a₀ ιc hιc), fun y => hιc y.1,
    retainedEquiv_alpha ιc phiKeepO_alpha phiKeepO_alpha (phiKeepO_map_iff T a₀ ιc hιc)
      (phiKeepO_range T a₀ ιc hιc) hαc,
    fun y => (retainedEquiv_sigma_of_semiconj ιc phiKeepO_alpha phiKeepO_alpha
      (phiKeepO_map_iff T a₀ ιc hιc) (phiKeepO_range T a₀ ιc hιc) h y).symm, ?_⟩
  intro y x' i' hpath hface
  have h1' : Relation.EqvGen (CombMap.FaceClassStep (collapsedMap S.family).dual
      (PhiKeepO S.family (linkedComponentO S.family a₀.1))) (back (ιc y.1)) (back x') :=
    hsim _ _ hpath
  rw [hback] at h1'
  exact ⟨back x', h1', hcell x' i' hface⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.not_regionInternal_of_crossO
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.phiKeepO_map_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.phiKeepO_range
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.phiTransportAt_of_bypass
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.phiTransportAt_of_semiconj
