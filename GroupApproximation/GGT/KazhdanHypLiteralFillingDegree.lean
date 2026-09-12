import GroupApproximation.GGT.KazhdanHypLiteralFilling
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# The degree obstruction for discs over positive relators

Let `χ : G →* Multiplicative ℤ` be a degree character.  Edge reversal inverts
labels, so the label degrees of all darts cancel in pairs, and the faces
partition the darts.  A disc diagram's inner faces are relator faces, reading a
word of the relator family, or freely trivial `G`-faces, and its boundary word
is the formal inverse of the outer face word.  So if every relator word has
degree `m`, the boundary value of any disc diagram has degree `m` times its
relator area (`toAdd_boundaryValue`).  The stored cell values play no part.

For a triangle table whose letters are all positive, as `GirthEightChecks`
requires, every relator word has degree `3`, so no disc diagram over
`triangleRelatorWords T` has a boundary of negative degree.  This refutes the
first statements of P1 and P2:

* `not_literalRelatorOnlyFilling_cubeTable`: at the table `x x x`, the word
  `x⁻¹ x⁻¹ x⁻¹` is one signed conjugate of the relator but bounds no disc;
* `not_leastLiteralDiscLocalData_of_girthEightChecks`: at a checked table with
  a triangle, the formal inverse of a triangle word is a cyclically reduced
  null word that bounds no disc.

Literal fillings must therefore be taken over the symmetrized family, in which a
face may read a triangle word or its formal inverse (`KazhdanHypSymRelators`).
-/

namespace GroupApproximation
namespace GGT
namespace KazhdanHypLiteralFillingDegree

open GroupApproximation.KazhdanHyp
open GirthEightVKInterface
open VanKampen
open KazhdanHypCactusDeletionCounting
open KazhdanHypLiteralFilling

universe u w v

section Generic

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  (χ : G →* Multiplicative ℤ)

/-- The additive degree of a relative letter. -/
def letterDeg (a : RelLetter G Lambda) : ℤ := Multiplicative.toAdd (χ a.val)

theorem letterDeg_inv (a : RelLetter G Lambda) :
    letterDeg χ (HullSC.RelWord.inv a) = -letterDeg χ a := by
  simp only [letterDeg, HullSC.RelWord.val_inv, map_inv, toAdd_inv]

/-- The degree of a word is the sum of its letter degrees. -/
theorem toAdd_listVal (l : List (RelLetter G Lambda)) :
    Multiplicative.toAdd (χ (RelLetter.listVal l)) = (l.map (letterDeg χ)).sum := by
  induction l with
  | nil => simp only [RelLetter.listVal_nil, map_one, toAdd_one, List.map_nil, List.sum_nil]
  | cons a t ih =>
      rw [HullSC.RelWord.listVal_cons, map_mul, toAdd_mul, ih, List.map_cons, List.sum_cons,
        letterDeg]

/-- **The label degrees of all darts cancel in pairs.** -/
theorem sum_letterDeg_label (Delta : DiscDiagram.{u, w, v} W) :
    ∑ d, letterDeg χ (Delta.label d) = 0 := by
  have h := Equiv.sum_comp Delta.toCombMap.alpha (fun d => letterDeg χ (Delta.label d))
  simp only [Delta.label_alpha, letterDeg_inv, Finset.sum_neg_distrib] at h
  omega

/-- **Summing along all face boundaries sums over all darts.** -/
theorem sum_faceBoundary (Delta : DiscDiagram.{u, w, v} W) (g : Delta.toCombMap.Dart → ℤ) :
    ∑ f : Delta.toCombMap.Face, ((Delta.faceBoundary f).darts.map g).sum = ∑ d, g d := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ Delta.toCombMap.faceOf g]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [← List.sum_toFinset g (Delta.faceBoundary f).nodup]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext d
  simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (Delta.faceBoundary f).mem_iff d

theorem toAdd_faceWord (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face) :
    Multiplicative.toAdd (χ (RelLetter.listVal (Delta.faceWord f))) =
      ((Delta.faceBoundary f).darts.map fun d => letterDeg χ (Delta.label d)).sum := by
  simp only [toAdd_listVal, DiscDiagram.faceWord, List.map_map, Function.comp_def]

/-- **The degree of the boundary counts relator faces.**  If every relator word
has degree `m`, the boundary value of a disc diagram has degree `m` times its
relator area. -/
theorem toAdd_boundaryValue (Delta : DiscDiagram.{u, w, v} W) (m : ℤ)
    (hW : ∀ word ∈ W, Multiplicative.toAdd (χ (RelLetter.listVal word)) = m) :
    Multiplicative.toAdd (χ Delta.boundaryValue) = m * Delta.rCellCount := by
  classical
  have hb : Multiplicative.toAdd (χ Delta.boundaryValue) =
      -Multiplicative.toAdd (χ (RelLetter.listVal (Delta.faceWord Delta.outerFace))) := by
    rw [DiscDiagram.boundaryValue, DiscDiagram.boundaryWord, HullSC.RelWord.listVal_revInv,
      map_inv, toAdd_inv]
  have hsum : ∑ f, Multiplicative.toAdd (χ (RelLetter.listVal (Delta.faceWord f))) = 0 := by
    simp only [toAdd_faceWord]
    rw [sum_faceBoundary]
    exact sum_letterDeg_label χ Delta
  have hsplit : Multiplicative.toAdd (χ (RelLetter.listVal (Delta.faceWord Delta.outerFace))) +
      ∑ f ∈ Finset.univ.erase Delta.outerFace,
        Multiplicative.toAdd (χ (RelLetter.listVal (Delta.faceWord f))) =
      ∑ f, Multiplicative.toAdd (χ (RelLetter.listVal (Delta.faceWord f))) :=
    Finset.add_sum_erase Finset.univ
      (fun f => Multiplicative.toAdd (χ (RelLetter.listVal (Delta.faceWord f))))
      (Finset.mem_univ Delta.outerFace)
  have hsub : (Delta.relatorCells.map RelatorCell.face).toFinset ⊆
      Finset.univ.erase Delta.outerFace := by
    intro f hf
    rw [List.mem_toFinset] at hf
    obtain ⟨C, _, rfl⟩ := List.mem_map.mp hf
    exact Finset.mem_erase.mpr ⟨C.face_ne_outer, Finset.mem_univ _⟩
  have hzero : ∀ f ∈ Finset.univ.erase Delta.outerFace,
      f ∉ (Delta.relatorCells.map RelatorCell.face).toFinset →
        Multiplicative.toAdd (χ (RelLetter.listVal (Delta.faceWord f))) = 0 := by
    intro f hf hnot
    have hne : f ≠ Delta.outerFace := (Finset.mem_erase.mp hf).1
    rcases Delta.inner_face f hne with ⟨C, hC, hCf⟩ | htriv
    · exact absurd (List.mem_toFinset.mpr (List.mem_map.mpr ⟨C, hC, hCf⟩)) hnot
    · rw [DiscDiagram.faceWord, htriv, map_one, toAdd_one]
  have hcount : ∀ l : List (RelatorCell Delta.toCombMap Delta.outerFace W),
      (∀ C ∈ l, Multiplicative.toAdd (χ (RelLetter.listVal (Delta.faceWord C.face))) = m) →
        (l.map fun C => Multiplicative.toAdd (χ (RelLetter.listVal (Delta.faceWord C.face)))).sum =
          m * l.length := by
    intro l hl
    induction l with
    | nil => simp
    | cons C l ih =>
        rw [List.map_cons, List.sum_cons, hl C List.mem_cons_self,
          ih (fun C' hC' => hl C' (List.mem_cons_of_mem C hC')), List.length_cons]
        push_cast
        ring
  have hinner : ∑ f ∈ Finset.univ.erase Delta.outerFace,
      Multiplicative.toAdd (χ (RelLetter.listVal (Delta.faceWord f))) = m * Delta.rCellCount := by
    rw [← Finset.sum_subset hsub hzero, List.sum_toFinset _ Delta.relatorCell_faces_nodup,
      List.map_map]
    exact hcount Delta.relatorCells fun C hC => by
      rw [DiscDiagram.faceWord, ← Delta.relatorCell_word C hC]
      exact hW C.word C.word_mem
  omega

end Generic

section Table

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]

/-- The degree character: every generator has degree one. -/
def degreeCharacter (Generator : Type) : FreeGroup Generator →* Multiplicative ℤ :=
  FreeGroup.lift fun _ => Multiplicative.ofAdd (1 : ℤ)

theorem degreeCharacter_letterValue_true (x : Generator) :
    degreeCharacter Generator (FoxBoundary.letterValue FreeGroup.of (x, true)) =
      Multiplicative.ofAdd (1 : ℤ) := by
  show degreeCharacter Generator (FreeGroup.of x) = _
  rw [degreeCharacter, FreeGroup.lift_apply_of]

/-- **A positive triangle word has degree three.** -/
theorem toAdd_degree_triangleRelatorWord
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (j : TriangleIndex)
    (hpos : ∀ k, (T j k).2 = true) :
    Multiplicative.toAdd (degreeCharacter Generator
      (GGT.RelLetter.listVal (triangleRelatorWord.{0} T j))) = 3 := by
  have hval : GGT.RelLetter.listVal (triangleRelatorWord.{0} T j) =
      FoxBoundary.letterValue FreeGroup.of (T j 0) *
        (FoxBoundary.letterValue FreeGroup.of (T j 1) *
          (FoxBoundary.letterValue FreeGroup.of (T j 2) * 1)) := by
    simp only [triangleRelatorWord, TriangularHodgeLayer.letters_eq_three, List.map_cons,
      List.map_nil, GGT.RelLetter.listVal, signedFreeRelLetter, GGT.RelLetter.val,
      List.prod_cons, List.prod_nil]
  have hlet : ∀ u : TriangularHodgeLayer.SignedGenerator Generator, u.2 = true →
      degreeCharacter Generator (FoxBoundary.letterValue FreeGroup.of u) =
        Multiplicative.ofAdd (1 : ℤ) := by
    rintro ⟨x, b⟩ hb
    cases b
    · cases hb
    · exact degreeCharacter_letterValue_true x
  have h3 : Multiplicative.toAdd (Multiplicative.ofAdd (1 : ℤ) *
      (Multiplicative.ofAdd (1 : ℤ) * (Multiplicative.ofAdd (1 : ℤ) * 1))) = 3 := rfl
  rw [hval, map_mul (degreeCharacter Generator), map_mul (degreeCharacter Generator),
    map_mul (degreeCharacter Generator), map_one (degreeCharacter Generator),
    hlet _ (hpos 0), hlet _ (hpos 1), hlet _ (hpos 2), h3]

/-- Every relator word of a positive table has degree three. -/
theorem toAdd_degree_of_mem (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (hpos : ∀ j k, (T j k).2 = true) :
    ∀ word ∈ triangleRelatorWords.{0} T,
      Multiplicative.toAdd (degreeCharacter Generator (GGT.RelLetter.listVal word)) = 3 := by
  rintro word ⟨j, rfl⟩
  exact toAdd_degree_triangleRelatorWord T j (hpos j)

/-- **Discs over a positive table have boundary degree three times their area.** -/
theorem toAdd_boundaryValue_eq (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (hpos : ∀ j k, (T j k).2 = true)
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords.{0} T)) :
    Multiplicative.toAdd (degreeCharacter Generator Delta.boundaryValue) =
      3 * Delta.rCellCount :=
  toAdd_boundaryValue (degreeCharacter Generator) Delta 3 (toAdd_degree_of_mem T hpos)

/-- The formal inverse of a triangle word spells the inverse relator. -/
theorem word_invRev_letters (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (j : TriangleIndex) :
    PresentedGroupRelatorReplay.word (FreeGroup.invRev (TriangularHodgeLayer.letters (T j))) =
      (GGT.RelLetter.listVal (triangleRelatorWord.{0} T j))⁻¹ := by
  rw [triangleRelatorWord, listVal_map_signedFreeRelLetter, PresentedGroupRelatorReplay.word,
    PresentedGroupRelatorReplay.word, FreeGroup.inv_mk]

/-- **P1 as first stated is false.**  At the table `x x x` the word
`x⁻¹ x⁻¹ x⁻¹` is one signed conjugate of the relator, but it has degree `-3`. -/
theorem not_literalRelatorOnlyFilling_cubeTable : ¬ LiteralRelatorOnlyFilling cubeTable := by
  intro hfill
  have hinv : PresentedGroupRelatorReplay.word [((), false), ((), false), ((), false)] =
      (GGT.RelLetter.listVal (triangleRelatorWord.{0} cubeTable ()))⁻¹ := by
    rw [← word_invRev_letters cubeTable ()]
    exact congrArg PresentedGroupRelatorReplay.word (by decide)
  have hcells : ∀ x ∈ [PresentedGroupRelatorReplay.word [((), false), ((), false), ((), false)]],
      RelatorDefectBudget.IsSignedConjugate
        (GGT.RelLetter.listVal '' triangleRelatorWords.{0} cubeTable) x := by
    intro x hx
    rw [List.mem_singleton] at hx
    rw [hx, hinv]
    exact ⟨1, GGT.RelLetter.listVal (triangleRelatorWord.{0} cubeTable ()),
      ⟨triangleRelatorWord cubeTable (), ⟨(), rfl⟩, rfl⟩, Or.inr (by group)⟩
  obtain ⟨Delta, hboundary, _, _⟩ := hfill [((), false), ((), false), ((), false)]
    [PresentedGroupRelatorReplay.word [((), false), ((), false), ((), false)]]
    (List.cons_ne_nil _ _) hcells List.prod_singleton
  have hdeg := toAdd_boundaryValue_eq cubeTable (fun _ _ => rfl) Delta
  rw [DiscDiagram.boundaryValue, hboundary, listVal_map_signedFreeRelLetter, hinv, map_inv,
    toAdd_inv, toAdd_degree_triangleRelatorWord cubeTable () (fun _ => rfl)] at hdeg
  omega

/-- **P2 as first stated is false at every checked table with a triangle.**  The
formal inverse of a triangle word is a nonempty cyclically reduced null word of
degree `-3`. -/
theorem not_leastLiteralDiscLocalData_of_girthEightChecks
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator} {d : ℕ}
    (hchecks : GirthEightChecks T d) (j : TriangleIndex) :
    ¬ LeastLiteralDiscLocalData T := by
  intro hP2
  have hpos : ∀ j k, (T j k).2 = true := hchecks.1
  have hne : FreeGroup.invRev (TriangularHodgeLayer.letters (T j)) ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [FreeGroup.invRev_length, TriangularHodgeLayer.letters_eq_three]
    exact Nat.zero_lt_succ _
  have hlist : FreeGroup.invRev (TriangularHodgeLayer.letters (T j)) =
      [((T j 2).1, false), ((T j 1).1, false), ((T j 0).1, false)] := by
    rw [TriangularHodgeLayer.letters_eq_three]
    simp [FreeGroup.invRev, hpos]
  have hcr : FreeGroup.IsCyclicallyReduced
      (FreeGroup.invRev (TriangularHodgeLayer.letters (T j))) := by
    rw [hlist]
    refine ⟨List.isChain_cons_cons.mpr ⟨fun _ => rfl, List.isChain_cons_cons.mpr
      ⟨fun _ => rfl, List.isChain_singleton _⟩⟩, ?_⟩
    intro a ha b hb _
    simp at ha hb
    subst ha
    subst hb
    rfl
  have hnull : PresentedGroup.mk (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
      (PresentedGroupRelatorReplay.word
        (FreeGroup.invRev (TriangularHodgeLayer.letters (T j)))) = 1 := by
    rw [word_invRev_letters, map_inv, inv_eq_one, triangleRelatorWord,
      listVal_map_signedFreeRelLetter]
    exact PresentedGroup.one_of_mem
      (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩))
  obtain ⟨Delta, hboundary, _, _⟩ := hP2 d hchecks _ hne hcr hnull
  have hdeg := toAdd_boundaryValue_eq T hpos Delta
  rw [DiscDiagram.boundaryValue, hboundary, listVal_map_signedFreeRelLetter,
    word_invRev_letters, map_inv, toAdd_inv, toAdd_degree_triangleRelatorWord T j (hpos j)] at hdeg
  omega

end Table

end KazhdanHypLiteralFillingDegree
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.KazhdanHypLiteralFillingDegree.sum_letterDeg_label
#audit_axioms GroupApproximation.GGT.KazhdanHypLiteralFillingDegree.sum_faceBoundary
#audit_axioms GroupApproximation.GGT.KazhdanHypLiteralFillingDegree.toAdd_boundaryValue
#audit_axioms GroupApproximation.GGT.KazhdanHypLiteralFillingDegree.toAdd_degree_triangleRelatorWord
#audit_axioms GroupApproximation.GGT.KazhdanHypLiteralFillingDegree.toAdd_boundaryValue_eq
#audit_closed_axioms
  GroupApproximation.GGT.KazhdanHypLiteralFillingDegree.not_literalRelatorOnlyFilling_cubeTable
#audit_axioms
  GroupApproximation.GGT.KazhdanHypLiteralFillingDegree.not_leastLiteralDiscLocalData_of_girthEightChecks
