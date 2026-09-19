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
* `slit_minimal_of_geodesic`: a geodesic spelling of the minimal path's value is no longer than
  any walk from the boundary to any relator cell (the `slitIn_minimal` / `slitOut_minimal`
  fields of `GL06p.SlitPocketCore`).

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

/-- **A geodesic spelling of the minimal path is no longer than every walk from the boundary to a
relator cell** (Osin, proof of Lemma 9.7(b)): it is no longer than the path's own label word,
which is as long as the path, which is minimal. -/
theorem slit_minimal_of_geodesic {D : RelGenSet G Lambda} {Delta : DiscDiagram.{u, w, v} W}
    (N : NearestCellPath Delta)
    (hletters : ∀ d, (symmetricLabelAlphabet D).IsLetter (Delta.label d))
    {s : List (RelLetter G Lambda)}
    (hs : OsinComponents.IsGeodesicWord D 1 (RelLetter.listVal s) s)
    (hval : RelLetter.listVal (dartWord Delta N.path) = RelLetter.listVal s) :
    ∀ (j : Fin Delta.rCellCount) (q : List Delta.toCombMap.Dart),
      IsBoundaryToCellWalk Delta j q → s.length ≤ q.length := by
  intro j q hq
  have hlet : ∀ a ∈ dartWord Delta N.path, (symmetricLabelAlphabet D).IsLetter a := by
    intro a ha
    unfold dartWord at ha
    obtain ⟨d, -, rfl⟩ := List.mem_map.mp ha
    exact hletters d
  have h1 := length_le_of_isGeodesicWord hs hlet hval
  have h2 : (dartWord Delta N.path).length = N.path.length := by
    unfold dartWord
    simp
  exact (h1.trans h2.le).trans (N.minimal j q hq)

#audit_axioms GroupApproximation.Full.GL06p.slit_minimal_of_geodesic

end Geodesic

end GroupApproximation.Full.GL06p
