import GroupApproximation.GGT.DGOProposition414TwoHalfProducer
import GroupApproximation.GGT.OsinTheorem54SepCommIndex
import GroupApproximation.GGT.OsinTheorem54SepSubGeodesic

/-!
# Orientation-safe chord intervals for DGO Proposition 4.14

The greedy broken components are ordered on the polygon arc, but their chosen
partners need not be ordered on the cutting chord.  Consequently the chord
piece in one auxiliary cycle must be allowed to run in either direction.

`orientedSegment w i j` is the subword from `i` to `j`: the ordinary segment
when `i ≤ j`, and the reversal of the ordinary segment from `j` to `i`
otherwise.  It always spells the difference of the two corresponding vertices
and remains geodesic.  Its length is `Nat.dist i j`, exactly the summand in
`chordTraversalCost`.

The final two lemmas add the initial and terminal chord intervals.  They cost
at most `2L` per half even when the interior partner traversal zigzags.  This
is the exact endpoint correction used by `PathLengthBounds.chord_total`.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- The word segment from index `i` to index `j`, with its orientation chosen
from the order of the endpoints. -/
def orientedSegment (word : List (RelLetter G Λ)) (i j : ℕ) :
    List (RelLetter G Λ) :=
  if i ≤ j then (word.drop i).take (j - i)
  else revWord ((word.drop j).take (i - j))

/-- The orientation-safe segment has the metric interval length. -/
theorem length_orientedSegment (word : List (RelLetter G Λ)) {i j : ℕ}
    (hi : i ≤ word.length) (hj : j ≤ word.length) :
    (orientedSegment word i j).length = Nat.dist i j := by
  by_cases hij : i ≤ j
  · rw [orientedSegment, if_pos hij, List.length_take, List.length_drop,
      Nat.dist_eq_sub_of_le hij]
    omega
  · have hji : j ≤ i := by omega
    rw [orientedSegment, if_neg hij, OsinComponents.length_revWord,
      List.length_take,
      List.length_drop, Nat.dist_comm, Nat.dist_eq_sub_of_le hji]
    omega

/-- The orientation-safe segment spells the difference of its endpoint
vertices. -/
theorem listVal_orientedSegment (word : List (RelLetter G Λ)) (v : G)
    {i j : ℕ} :
    vertex v word i * RelLetter.listVal (orientedSegment word i j) =
      vertex v word j := by
  by_cases hij : i ≤ j
  · rw [orientedSegment, if_pos hij]
    exact listVal_segment word v hij
  · have hji : j ≤ i := by omega
    have hsegment := listVal_segment word v hji
    rw [orientedSegment, if_neg hij, listVal_revWord]
    rw [← hsegment]
    group

/-- A segment of a geodesic chord remains geodesic in either orientation. -/
theorem isGeodesicWord_orientedSegment (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {v z : G}
    {word : List (RelLetter G Λ)} (hword : IsGeodesicWord D v z word)
    {i j : ℕ} (hi : i ≤ word.length) (hj : j ≤ word.length) :
    IsGeodesicWord D (vertex v word i) (vertex v word j)
      (orientedSegment word i j) := by
  by_cases hij : i ≤ j
  · rw [orientedSegment, if_pos hij]
    exact isGeodesicWord_segment D hword hij hj
  · have hji : j ≤ i := by omega
    rw [orientedSegment, if_neg hij]
    exact isGeodesicWord_revWord D hsymm
      (isGeodesicWord_segment D hword hji hi)

/-- Appending the terminal endpoint `L` costs at most one extra chord length. -/
theorem chordTraversalCost_append_endpoint_le {partners : List ℕ} {L : ℕ}
    (hupper : ∀ y ∈ partners, y ≤ L) :
    chordTraversalCost (partners ++ [L]) ≤
      chordTraversalCost partners + L := by
  induction partners with
  | nil => simp [chordTraversalCost]
  | cons x xs ih =>
      cases xs with
      | nil =>
          have hx := hupper x (by simp)
          rw [List.cons_append, List.nil_append]
          simp only [chordTraversalCost]
          rw [Nat.dist_eq_sub_of_le hx]
          omega
      | cons y ys =>
          have htail : ∀ z ∈ y :: ys, z ≤ L := by
            intro z hz
            exact hupper z (by simp [hz])
          have hih := ih htail
          simpa only [List.cons_append, chordTraversalCost, Nat.add_assoc] using
            Nat.add_le_add_left hih (Nat.dist x y)

/-- Adding both endpoints `0` and `L` costs at most `2L`.  No order of the
interior partners is assumed. -/
theorem chordTraversalCost_with_endpoints_le {partners : List ℕ} {L : ℕ}
    (hupper : ∀ y ∈ partners, y ≤ L) :
    chordTraversalCost (0 :: partners ++ [L]) ≤
      chordTraversalCost partners + 2 * L := by
  cases partners with
  | nil =>
      simp only [List.cons_append, List.nil_append, chordTraversalCost,
        Nat.zero_add]
      rw [Nat.dist_eq_sub_of_le (Nat.zero_le L)]
      omega
  | cons y ys =>
      have hy : y ≤ L := hupper y (by simp)
      have happ := chordTraversalCost_append_endpoint_le hupper
      change Nat.dist 0 y + chordTraversalCost ((y :: ys) ++ [L]) ≤
        chordTraversalCost (y :: ys) + 2 * L
      rw [Nat.dist_eq_sub_of_le (Nat.zero_le y)]
      omega

/-- The two complete half traversals, including both endpoints in each half,
have the quadratic bound used by the concrete path producer. -/
theorem twoHalf_chordTraversal_with_endpoints_le
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {L : ℕ}
    (index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ L) :
    chordTraversalCost (0 :: index.first.partners ++ [L]) +
        chordTraversalCost (0 :: index.second.partners ++ [L]) ≤
      2 * (L * L) + 4 * L := by
  have hfirstUpper : ∀ y ∈ index.first.partners, y ≤ L := by
    intro y hy
    exact le_of_lt (index.first.partner_lt y hy)
  have hsecondUpper : ∀ y ∈ index.second.partners, y ≤ L := by
    intro y hy
    exact le_of_lt (index.second.partner_lt y hy)
  have hfirst := chordTraversalCost_with_endpoints_le hfirstUpper
  have hsecond := chordTraversalCost_with_endpoints_le hsecondUpper
  have hfirstInterior := index.first.traversal
  have hsecondInterior := index.second.traversal
  unfold ChordPartnerQuadraticTraversalBound at hfirstInterior hsecondInterior
  omega

/-! ## Raw surgery intervals on the common chord -/

/-- One raw component-surgery interval attached to the common cutting chord.

The inherited arc and its two possible connectors travel from chord vertex
`chordFinish` to chord vertex `chordStart`; the automatically constructed
oriented chord segment returns from `chordStart` to `chordFinish`.  This
endpoint equation is enough to derive closure, including the cases where the
partner order reverses. -/
structure AuxiliaryIntervalOnChord (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (b : ℕ)
    (chordBase chordEnd : G) (globalChord : List (RelLetter G Λ))
    (globalGeodesic : IsGeodesicWord D chordBase chordEnd globalChord) where
  chordStart : ℕ
  chordFinish : ℕ
  chordStart_le : chordStart ≤ globalChord.length
  chordFinish_le : chordFinish ≤ globalChord.length
  left : List (RelLetter G Λ)
  arc : List (RelLetter G Λ)
  right : List (RelLetter G Λ)
  arcSides : ℕ
  arcCut : ℕ → ℕ
  arcPolygon : IsCutPolygon D (b : ℝ) arcSides
    (vertex chordBase globalChord chordFinish *
      RelLetter.listVal (revWord left)) arc arcCut
  leftLetters : ∀ x ∈ left, D.IsLetter x
  rightLetters : ∀ x ∈ right, D.IsLetter x
  prefix_endpoint :
    vertex chordBase globalChord chordFinish *
        RelLetter.listVal ((revWord left ++ arc) ++ right) =
      vertex chordBase globalChord chordStart
  localTarget : Finset ℕ
  label : ℕ → Λ
  localTarget_lt : ∀ s ∈ localTarget,
    s < left.length + arcSides + right.length +
      (orientedSegment globalChord chordStart chordFinish).length
  localTarget_edge : ∀ s ∈ localTarget,
    auxiliaryCycleCut left arcSides arcCut right (s + 1) =
      auxiliaryCycleCut left arcSides arcCut right s + 1
  components : AuxiliaryCycleComponentConfiguration D
    (vertex chordBase globalChord chordFinish)
    left arc right (orientedSegment globalChord chordStart chordFinish)
    arcSides arcCut
    (localTarget ∪ auxiliaryCycleConnectorTarget left right arcSides) label

namespace AuxiliaryIntervalOnChord

/-- The endpoint equation closes the raw interval cycle. -/
theorem closes
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {b : ℕ} {chordBase chordEnd : G}
    {globalChord : List (RelLetter G Λ)}
    {globalGeodesic : IsGeodesicWord D chordBase chordEnd globalChord}
    (P : AuxiliaryIntervalOnChord D hsymm b chordBase chordEnd
      globalChord globalGeodesic) :
    RelLetter.listVal P.left = RelLetter.listVal P.arc *
      RelLetter.listVal P.right *
        RelLetter.listVal (orientedSegment globalChord
          P.chordStart P.chordFinish) := by
  have hchord := listVal_orientedSegment globalChord chordBase
    (i := P.chordStart) (j := P.chordFinish)
  have hprefix :
      vertex chordBase globalChord P.chordFinish *
          (RelLetter.listVal P.left)⁻¹ * RelLetter.listVal P.arc *
            RelLetter.listVal P.right =
        vertex chordBase globalChord P.chordStart := by
    simpa only [listVal_append, listVal_revWord, mul_assoc] using
      P.prefix_endpoint
  rw [← hprefix] at hchord
  have hproduct :
      (RelLetter.listVal P.left)⁻¹ * RelLetter.listVal P.arc *
          RelLetter.listVal P.right *
            RelLetter.listVal (orientedSegment globalChord
              P.chordStart P.chordFinish) = 1 := by
    apply mul_left_cancel (a := vertex chordBase globalChord P.chordFinish)
    simpa only [mul_assoc, mul_one] using hchord
  calc
    RelLetter.listVal P.left = RelLetter.listVal P.left * 1 := by simp
    _ = RelLetter.listVal P.left *
        ((RelLetter.listVal P.left)⁻¹ * RelLetter.listVal P.arc *
          RelLetter.listVal P.right *
            RelLetter.listVal (orientedSegment globalChord
              P.chordStart P.chordFinish)) := by rw [hproduct]
    _ = RelLetter.listVal P.arc * RelLetter.listVal P.right *
        RelLetter.listVal (orientedSegment globalChord
          P.chordStart P.chordFinish) := by group

/-- Populate a concrete path input from one raw surgery interval.  The chord
word, its endpoint, its geodesicity, and closure are all derived rather than
supplied as additional fields. -/
def toPathInput
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {b : ℕ} {chordBase chordEnd : G}
    {globalChord : List (RelLetter G Λ)}
    {globalGeodesic : IsGeodesicWord D chordBase chordEnd globalChord}
    (P : AuxiliaryIntervalOnChord D hsymm b chordBase chordEnd
      globalChord globalGeodesic) : AuxiliaryCyclePathInput D hsymm b := by
  refine
    { basepoint := vertex chordBase globalChord P.chordFinish
      left := P.left
      arc := P.arc
      right := P.right
      chord := orientedSegment globalChord P.chordStart P.chordFinish
      arcSides := P.arcSides
      arcCut := P.arcCut
      arcPolygon := P.arcPolygon
      chordEndpoint := vertex chordBase globalChord P.chordFinish
      chordGeodesic := ?_
      leftLetters := P.leftLetters
      rightLetters := P.rightLetters
      closes := P.closes
      localTarget := P.localTarget
      label := P.label
      localTarget_lt := P.localTarget_lt
      localTarget_edge := P.localTarget_edge
      components := P.components }
  have hsegment := isGeodesicWord_orientedSegment D hsymm globalGeodesic
    P.chordStart_le P.chordFinish_le
  have hstart :
      vertex chordBase globalChord P.chordFinish *
          RelLetter.listVal ((revWord P.left ++ P.arc) ++ P.right) =
        vertex chordBase globalChord P.chordStart := P.prefix_endpoint
  simpa only [hstart] using hsegment

end AuxiliaryIntervalOnChord

/-- The raw component surgery has produced one interval on the common chord
for every piece of the two independently greedy halves. -/
structure TwoHalfIntervalSurgery (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (b : ℕ)
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    (index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength)
    (chordBase chordEnd : G) (globalChord : List (RelLetter G Λ))
    (globalGeodesic : IsGeodesicWord D chordBase chordEnd globalChord) where
  first : Fin index.first.pieceCount →
    AuxiliaryIntervalOnChord D hsymm b chordBase chordEnd
      globalChord globalGeodesic
  second : Fin index.second.pieceCount →
    AuxiliaryIntervalOnChord D hsymm b chordBase chordEnd
      globalChord globalGeodesic

namespace TwoHalfIntervalSurgery

/-- Populate every concrete child input from the raw intervals. -/
def toPathInput
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {b : ℕ} {I₁ I₂ : Finset ℕ}
    {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ} {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {chordBase chordEnd : G} {globalChord : List (RelLetter G Λ)}
    {globalGeodesic : IsGeodesicWord D chordBase chordEnd globalChord}
    (S : TwoHalfIntervalSurgery D hsymm b index chordBase chordEnd
      globalChord globalGeodesic) : TwoHalfPathInput D hsymm b index where
  first := fun j => (S.first j).toPathInput
  second := fun j => (S.second j).toPathInput

/-- Side-count facts proved by the raw interval decomposition.

The common chord has the same length as the chord-coordinate interval used by
the greedy family.  Together with the endpoint bounds stored in each interval,
this controls every oriented chord segment directly; no monotonic ordering of
the partner coordinates is required. -/
structure SideBounds
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {b : ℕ} {I₁ I₂ : Finset ℕ}
    {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ} {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {chordBase chordEnd : G} {globalChord : List (RelLetter G Λ)}
    {globalGeodesic : IsGeodesicWord D chordBase chordEnd globalChord}
    (S : TwoHalfIntervalSurgery D hsymm b index chordBase chordEnd
      globalChord globalGeodesic) (n : ℕ) where
  arc_partition :
    (∑ j, (S.first j).arcSides) + ∑ j, (S.second j).arcSides = n
  first_connectors : ∀ j,
    (S.first j).left.length + (S.first j).right.length ≤ 2
  second_connectors : ∀ j,
    (S.second j).left.length + (S.second j).right.length ≤ 2
  chord_length : globalChord.length = chordLength
  first_small : ∀ j,
    5 * ((S.toPathInput).first j).sideCount ≤ 4 * n
  second_small : ∀ j,
    5 * ((S.toPathInput).second j).sideCount ≤ 4 * n

/-- Raw interval side bounds populate the exact path-length accounting used by
the final producer. -/
theorem toPathLengthBounds
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {b : ℕ} {I₁ I₂ : Finset ℕ}
    {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ} {chordLength n : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {chordBase chordEnd : G} {globalChord : List (RelLetter G Λ)}
    {globalGeodesic : IsGeodesicWord D chordBase chordEnd globalChord}
    {S : TwoHalfIntervalSurgery D hsymm b index chordBase chordEnd
      globalChord globalGeodesic}
    (H : SideBounds S n) :
    TwoHalfSideAccounting.PathLengthBounds S.toPathInput n := by
  have hfirstLength :
      (∑ j, ((S.toPathInput).first j).chord.length) =
        ∑ j, Nat.dist (S.first j).chordStart (S.first j).chordFinish := by
    apply Finset.sum_congr rfl
    intro j _
    exact length_orientedSegment globalChord
      (S.first j).chordStart_le (S.first j).chordFinish_le
  have hsecondLength :
      (∑ j, ((S.toPathInput).second j).chord.length) =
        ∑ j, Nat.dist (S.second j).chordStart (S.second j).chordFinish := by
    apply Finset.sum_congr rfl
    intro j _
    exact length_orientedSegment globalChord
      (S.second j).chordStart_le (S.second j).chordFinish_le
  have hfirstDist : ∀ j : Fin index.first.pieceCount,
      Nat.dist (S.first j).chordStart (S.first j).chordFinish ≤ chordLength := by
    intro j
    have hstart : (S.first j).chordStart ≤ chordLength := by
      simpa [H.chord_length] using (S.first j).chordStart_le
    have hfinish : (S.first j).chordFinish ≤ chordLength := by
      simpa [H.chord_length] using (S.first j).chordFinish_le
    unfold Nat.dist
    omega
  have hsecondDist : ∀ j : Fin index.second.pieceCount,
      Nat.dist (S.second j).chordStart (S.second j).chordFinish ≤ chordLength := by
    intro j
    have hstart : (S.second j).chordStart ≤ chordLength := by
      simpa [H.chord_length] using (S.second j).chordStart_le
    have hfinish : (S.second j).chordFinish ≤ chordLength := by
      simpa [H.chord_length] using (S.second j).chordFinish_le
    unfold Nat.dist
    omega
  have hfirstSum :
      (∑ j, Nat.dist (S.first j).chordStart (S.first j).chordFinish) ≤
        index.first.pieceCount * chordLength := by
    calc
      _ ≤ ∑ _j : Fin index.first.pieceCount, chordLength :=
        Finset.sum_le_sum fun j _ => hfirstDist j
      _ = index.first.pieceCount * chordLength := by simp
  have hsecondSum :
      (∑ j, Nat.dist (S.second j).chordStart (S.second j).chordFinish) ≤
        index.second.pieceCount * chordLength := by
    calc
      _ ≤ ∑ _j : Fin index.second.pieceCount, chordLength :=
        Finset.sum_le_sum fun j _ => hsecondDist j
      _ = index.second.pieceCount * chordLength := by simp
  have hfirstPieces :
      index.first.pieceCount * chordLength ≤
        (chordLength + 1) * chordLength :=
    Nat.mul_le_mul_right chordLength index.first.pieceCount_le
  have hsecondPieces :
      index.second.pieceCount * chordLength ≤
        (chordLength + 1) * chordLength :=
    Nat.mul_le_mul_right chordLength index.second.pieceCount_le
  refine
    { arc_partition := ?_
      first_connectors := ?_
      second_connectors := ?_
      chord_total := ?_
      first_small := H.first_small
      second_small := H.second_small }
  · exact H.arc_partition
  · exact H.first_connectors
  · exact H.second_connectors
  · rw [hfirstLength, hsecondLength]
    calc
      _ ≤ index.first.pieceCount * chordLength +
          index.second.pieceCount * chordLength :=
        Nat.add_le_add hfirstSum hsecondSum
      _ ≤ (chordLength + 1) * chordLength +
          (chordLength + 1) * chordLength :=
        Nat.add_le_add hfirstPieces hsecondPieces
      _ ≤ 2 * (chordLength * chordLength) + 4 * chordLength := by
        nlinarith

/-- Feed raw intervals on the common chord directly into the exact
Proposition 4.14 family certificate. -/
noncomputable def auxiliaryCycleFamilyCertificate_of_intervalSurgery
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    (index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength)
    (chordBase chordEnd : G) (globalChord : List (RelLetter G Λ))
    (globalGeodesic : IsGeodesicWord D chordBase chordEnd globalChord)
    (S : TwoHalfIntervalSurgery D hsymm b index chordBase chordEnd
      globalChord globalGeodesic)
    (n : ℕ) (v : G) (word : List (RelLetter G Λ)) (cut : ℕ → ℕ)
    (I : Finset ℕ) (lam : ℕ → Λ)
    (owner : ℕ → Sum (Fin index.first.pieceCount)
      (Fin index.second.pieceCount))
    (targetIndex : Sum (Fin index.first.pieceCount)
      (Fin index.second.pieceCount) → ℕ → ℕ)
    (htarget : ∀ s ∈ I,
      match owner s with
      | Sum.inl j => targetIndex (Sum.inl j) s ∈
          ((S.toPathInput.family).firstChildren j).target
      | Sum.inr j => targetIndex (Sum.inr j) s ∈
          ((S.toPathInput.family).secondChildren j).target)
    (hlabel : ∀ s ∈ I,
      match owner s with
      | Sum.inl j => ((S.toPathInput.family).firstChildren j).label
          (targetIndex (Sum.inl j) s) = lam s
      | Sum.inr j => ((S.toPathInput.family).secondChildren j).label
          (targetIndex (Sum.inr j) s) = lam s)
    (hspan : ∀ s ∈ I,
      match owner s with
      | Sum.inl j =>
          (vertex v word (cut s))⁻¹ * vertex v word (cut (s + 1)) =
            ((S.toPathInput.family).firstChildren j).sideSpan
              (targetIndex (Sum.inl j) s)
      | Sum.inr j =>
          (vertex v word (cut s))⁻¹ * vertex v word (cut (s + 1)) =
            ((S.toPathInput.family).secondChildren j).sideSpan
              (targetIndex (Sum.inr j) s))
    (hinj : ∀ q, Set.InjOn (targetIndex q)
      (↑(I.filter fun s => owner s = q) : Set ℕ))
    (bounds : SideBounds S n) :
    AuxiliaryCycleFamilyCertificate D hsymm b hδ n v word cut I lam :=
  auxiliaryCycleFamilyCertificate_of_pathLengths D hsymm b hδ index
    S.toPathInput n v word cut I lam owner targetIndex htarget hlabel hspan
    hinj (toPathLengthBounds bounds)

end TwoHalfIntervalSurgery

end DGOProposition414
end GGT
end GroupApproximation
