import GroupApproximation.Manuscript.NonMF.Full.GL06p.NearestPath
import GroupApproximation.GGT.OsinGeodesicWord
import GroupApproximation.GGT.OsinTheorem54SepFourGonPinning
import GroupApproximation.GGT.VanKampen.SymmetricLabelAlphabet
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06p: geodesic spellings of the collar and of the slit

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the collar `g` and the two slit sides
`s₁`, `s₂` of the slit pocket are geodesic words (`GL06h4.gl06h4Nearest_Pocket`, fields
`outer_geodesic`, `slitIn_geodesic`, `slitOut_geodesic`).  A minimal path in the diagram need not
spell a geodesic word.  The copy of the pocket only has to be `O`-equivalent to `Δ`, that is to
keep the boundary word and the relator cell words.  Its inner faces of trivial value are free.
So the collar and the slit may be spelled by geodesic words with the same values, the difference
filled by faces of trivial value.  This module supplies the words and their length bounds.
Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121).

* `exists_geodesicSpelling`: every element has a geodesic spelling from `1`, in the form the
  pocket fields ask for.
* `length_le_of_isGeodesicWord`: a geodesic spelling is no longer than any word over the
  symmetric label alphabet with the same value.  The diagrams' labels are letters of that
  alphabet.
* `length_le_boundary_of_isGeodesicWord`: the collar bound `outer_length_le`, when the collar
  has the value of a subword of the boundary word.
* `MetricClassMinimal`, `MetricNearestWalk`, `exists_metricNearestWalk`: a walk from the boundary
  to a relator cell whose value has least word norm over all walks of all diagrams `O`-equivalent
  to `Δ`.  This minimality survives gluing a copy of the pocket back; dart counts do not.
* `metricClassMinimal_of_geodesic`: a geodesic spelling of that value is metrically
  class-minimal (the `slitIn_minimal` / `slitOut_minimal` fields of `GL06p.SlitPocketCore`).

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.  No hypothesis is added.
-/

namespace GroupApproximation.Full.GL06p

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.WordMetric

section Geodesic

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **Every element has a geodesic spelling from `1`** (`OsinComponents.existsGeodesicWord`), in
the form of the pocket's geodesic fields. -/
theorem exists_geodesicSpelling (D : RelGenSet G Lambda) (g : G) :
    ∃ s : List (RelLetter G Lambda),
      OsinComponents.IsGeodesicWord D 1 (RelLetter.listVal s) s ∧ RelLetter.listVal s = g := by
  obtain ⟨s, hs⟩ := OsinComponents.existsGeodesicWord D 1 g
  have hval : RelLetter.listVal s = g := by simpa using hs.2.1
  refine ⟨s, ?_, hval⟩
  rw [hval]
  exact hs

#audit_axioms GroupApproximation.Full.GL06p.exists_geodesicSpelling

/-- **A geodesic spelling is no longer than any label word with the same value**: the word
metric of the symmetric label alphabet is that of `D` (`symmetricLabelAlphabet.carrier_eq`), and
a word's endpoints are at most its length apart. -/
theorem length_le_of_isGeodesicWord {D : RelGenSet G Lambda} {g : G}
    {s s' : List (RelLetter G Lambda)} (hs : OsinComponents.IsGeodesicWord D 1 g s)
    (hlet : ∀ a ∈ s', (symmetricLabelAlphabet D).IsLetter a)
    (hval : RelLetter.listVal s' = g) : s.length ≤ s'.length := by
  have h := OsinComponents.wordDist_vertex_le (symmetricLabelAlphabet D) hlet
    (Nat.zero_le s'.length) le_rfl
  rw [OsinComponents.vertex_zero, OsinComponents.vertex_length, one_mul, hval,
    symmetricLabelAlphabet.carrier_eq, Nat.sub_zero] at h
  rw [hs.2.2]
  exact h

#audit_axioms GroupApproximation.Full.GL06p.length_le_of_isGeodesicWord

variable {W : Set (List (RelLetter G Lambda))}

/-- **The collar bound** (`outer_length_le`): a geodesic spelling of the value of a part of the
boundary word is no longer than the boundary word. -/
theorem length_le_boundary_of_isGeodesicWord {D : RelGenSet G Lambda}
    {Delta : DiscDiagram.{u, w, v} W} {s part : List (RelLetter G Lambda)}
    (hs : OsinComponents.IsGeodesicWord D 1 (RelLetter.listVal s) s)
    (hlet : ∀ a ∈ part, (symmetricLabelAlphabet D).IsLetter a)
    (hval : RelLetter.listVal part = RelLetter.listVal s)
    (hpart : part.length ≤ Delta.boundaryWord.length) :
    s.length ≤ Delta.boundaryWord.length :=
  (length_le_of_isGeodesicWord hs hlet hval).trans hpart

#audit_axioms GroupApproximation.Full.GL06p.length_le_boundary_of_isGeodesicWord

/-- **Metric class-minimality** (Osin, proof of Lemma 9.7(b)): `m` is at most the word norm of
the value of every walk from the boundary to a relator cell, in every diagram `O`-equivalent to
`Δ`.  This is the minimality that survives gluing a copy of the pocket back
(`PocketRegion.glueDiagram`, which is `O`-equivalent to the diagram).  Counting darts would not:
a copy may join the boundary to a cell by one dart with an arbitrary label. -/
def MetricClassMinimal (D : RelGenSet G Lambda) (Delta : DiscDiagram.{u, w, v} W) (m : ℕ) :
    Prop :=
  ∀ (Y : DiscDiagram.{u, w, v} W), Nonempty (OEquivalentDiscDiagram Delta Y) →
    ∀ (j : Fin Y.rCellCount) (q : List Y.toCombMap.Dart), IsBoundaryToCellWalk Y j q →
      m ≤ wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord Y q))

/-- **A metrically nearest cell over the `O`-equivalence class** (Osin, proof of Lemma 9.7(b)):
a diagram `O`-equivalent to `Δ`, a relator cell of it and a walk to that cell from the boundary
whose value has least word norm among all such walks of all such diagrams. -/
structure MetricNearestWalk (D : RelGenSet G Lambda) (Delta : DiscDiagram.{u, w, v} W) where
  diagram : DiscDiagram.{u, w, v} W
  equiv : OEquivalentDiscDiagram Delta diagram
  cell : Fin diagram.rCellCount
  path : List diagram.toCombMap.Dart
  walk : IsBoundaryToCellWalk diagram cell path
  minimal : MetricClassMinimal D Delta
    (wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord diagram path)))

/-- **A metrically nearest walk exists** whenever `Δ` has a relator cell: the word norms realised
over the class form a nonempty set of naturals, since `Δ` itself has a walk from the boundary to
each of its cells. -/
theorem exists_metricNearestWalk (D : RelGenSet G Lambda) (Delta : DiscDiagram.{u, w, v} W)
    (h : 0 < Delta.rCellCount) : Nonempty (MetricNearestWalk D Delta) := by
  classical
  have hex : ∃ n : ℕ, ∃ (Y : DiscDiagram.{u, w, v} W) (_ : Nonempty (OEquivalentDiscDiagram Delta Y))
      (j : Fin Y.rCellCount) (q : List Y.toCombMap.Dart),
      IsBoundaryToCellWalk Y j q ∧
        wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord Y q)) = n := by
    obtain ⟨q, hq⟩ := exists_boundaryToCellWalk Delta ⟨0, h⟩
    exact ⟨_, Delta, ⟨OEquivalentDiscDiagram.refl Delta⟩, ⟨0, h⟩, q, hq, rfl⟩
  obtain ⟨Y, ⟨E⟩, j, q, hq, hn⟩ := Nat.find_spec hex
  refine ⟨⟨Y, E, j, q, hq, ?_⟩⟩
  intro Y' hY' j' q' hq'
  rw [hn]
  exact Nat.find_min' hex ⟨Y', hY', j', q', hq', rfl⟩

#audit_axioms GroupApproximation.Full.GL06p.exists_metricNearestWalk

/-- **A geodesic spelling of the nearest walk's value is metrically class-minimal** (Osin, proof
of Lemma 9.7(b)): its length is the word norm of that value (`wordDist_one_left`), which is least
over the class.  This supplies the `slitIn_minimal` / `slitOut_minimal` fields of
`GL06p.SlitPocketCore`. -/
theorem metricClassMinimal_of_geodesic {D : RelGenSet G Lambda} {Delta : DiscDiagram.{u, w, v} W}
    (N : MetricNearestWalk D Delta) {s : List (RelLetter G Lambda)}
    (hs : OsinComponents.IsGeodesicWord D 1 (RelLetter.listVal s) s)
    (hval : RelLetter.listVal s = RelLetter.listVal (dartWord N.diagram N.path)) :
    MetricClassMinimal D Delta s.length := by
  intro Y hY j q hq
  have hlen : s.length = wordNorm D.alphabet.carrier (RelLetter.listVal s) := by
    rw [hs.2.2, wordDist_one_left]
  rw [hlen, hval]
  exact N.minimal Y hY j q hq

#audit_axioms GroupApproximation.Full.GL06p.metricClassMinimal_of_geodesic

/-- **Metric class-minimality is inherited by shorter lengths.** -/
theorem MetricClassMinimal.mono {D : RelGenSet G Lambda} {Delta : DiscDiagram.{u, w, v} W}
    {m m' : ℕ} (h : MetricClassMinimal D Delta m) (hle : m' ≤ m) :
    MetricClassMinimal D Delta m' :=
  fun Y hY j q hq => hle.trans (h Y hY j q hq)

#audit_axioms GroupApproximation.Full.GL06p.MetricClassMinimal.mono

end Geodesic

end GroupApproximation.Full.GL06p
