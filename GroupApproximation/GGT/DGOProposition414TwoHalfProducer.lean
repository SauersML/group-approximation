import GroupApproximation.GGT.DGOProposition414TwoHalfFlatten

/-!
# Producing the two-half Proposition 4.14 certificate

This file turns the local geometric output of the component surgery into the
two structures consumed by `auxiliaryCycleFamilyCertificate_of_twoHalf`.

There are three layers.

* `AuxiliaryCyclePathInput` stores the four *actual paths* of one interval,
  their inherited cut, and the complete component configuration.  Its
  `certificate` is therefore a concrete `AuxiliaryCycleCertificate`, rather
  than a bare existence hypothesis.
* `TwoHalfPathInput` stores one such input at every interval selected by the
  two greedy enumerations and constructs `TwoHalfAuxiliaryCycleFamily`.
* `twoHalfChargingConfiguration_of_targetEmbedding` proves all charging sums
  from the geometric datum that each original component is assigned
  injectively to an actual target of its owning child.  In particular callers
  no longer repeat a finite-sum argument for each half.

The final `auxiliaryCycleFamilyCertificate_of_pathInput` combines those
constructions with explicit side accounting.  The remaining input is purely
geometric: the four paths and their component files, the target assignment,
and the side-count inequalities proved from their lengths.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## One concrete connector interval -/

/-- The four-path input which constructs one auxiliary cycle.

The component configuration is stored for the union of the locally selected
arc/chord targets and the canonical connector targets.  Thus arbitrary
connector letters are never incorrectly treated as quasigeodesic sides. -/
structure AuxiliaryCyclePathInput (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (b : ℕ) where
  basepoint : G
  left : List (RelLetter G Λ)
  arc : List (RelLetter G Λ)
  right : List (RelLetter G Λ)
  chord : List (RelLetter G Λ)
  arcSides : ℕ
  arcCut : ℕ → ℕ
  arcPolygon : IsCutPolygon D (b : ℝ) arcSides
    (basepoint * RelLetter.listVal (revWord left)) arc arcCut
  chordEndpoint : G
  chordGeodesic : IsGeodesicWord D
    (basepoint * RelLetter.listVal ((revWord left ++ arc) ++ right))
    chordEndpoint chord
  leftLetters : ∀ x ∈ left, D.IsLetter x
  rightLetters : ∀ x ∈ right, D.IsLetter x
  closes : RelLetter.listVal left = RelLetter.listVal arc *
    RelLetter.listVal right * RelLetter.listVal chord
  localTarget : Finset ℕ
  label : ℕ → Λ
  localTarget_lt : ∀ s ∈ localTarget,
    s < left.length + arcSides + right.length + chord.length
  localTarget_edge : ∀ s ∈ localTarget,
    auxiliaryCycleCut left arcSides arcCut right (s + 1) =
      auxiliaryCycleCut left arcSides arcCut right s + 1
  components : AuxiliaryCycleComponentConfiguration D basepoint
    left arc right chord arcSides arcCut
    (localTarget ∪ auxiliaryCycleConnectorTarget left right arcSides) label

namespace AuxiliaryCyclePathInput

/-- The number of sides of the concrete four-path cycle. -/
def sideCount {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {b : ℕ} (P : AuxiliaryCyclePathInput D hsymm b) : ℕ :=
  P.left.length + P.arcSides + P.right.length + P.chord.length

/-- Construct the fully certified child attached to one greedy interval. -/
def certificate {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {b : ℕ}
    (P : AuxiliaryCyclePathInput D hsymm b) :
    AuxiliaryCycleCertificate D (b : ℝ) P.sideCount :=
  auxiliaryCycleCertificate_of_paths_withComponentConfiguration
    D hsymm (Nat.cast_nonneg b) P.basepoint P.left P.arc P.right P.chord
    P.arcPolygon P.chordGeodesic P.leftLetters P.rightLetters P.closes
    P.localTarget P.label P.localTarget_lt P.localTarget_edge P.components

end AuxiliaryCyclePathInput

/-! ## Every interval in the two greedy halves -/

/-- Concrete four-path data at every interval of both greedy half-families. -/
structure TwoHalfPathInput (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (b : ℕ)
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    (index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength) where
  first : Fin index.first.pieceCount → AuxiliaryCyclePathInput D hsymm b
  second : Fin index.second.pieceCount → AuxiliaryCyclePathInput D hsymm b

namespace TwoHalfPathInput

/-- The concrete interval inputs assemble definitionally into the two child
families consumed by the charging construction. -/
def family {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {b : ℕ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (P : TwoHalfPathInput D hsymm b index) :
    TwoHalfAuxiliaryCycleFamily D (b : ℝ) index where
  firstSides := fun j => (P.first j).sideCount
  firstChildren := fun j => (P.first j).certificate
  secondSides := fun j => (P.second j).sideCount
  secondChildren := fun j => (P.second j).certificate

end TwoHalfPathInput

/-! ## Charging by an injective target assignment -/

/-- An injective map from an ownership fibre into the target set cannot charge
more than the total radius of that target set. -/
theorem sum_ownerFiber_targetRadius_le
    {κ : Type*} [DecidableEq κ] (I : Finset ℕ) (owner : ℕ → κ)
    (target : κ → Finset ℕ) (targetIndex : κ → ℕ → ℕ)
    (radius : κ → ℕ → ℕ)
    (hmem : ∀ q s, s ∈ I → owner s = q → targetIndex q s ∈ target q)
    (hinj : ∀ q, Set.InjOn (targetIndex q)
      (↑(I.filter fun s => owner s = q) : Set ℕ)) (q : κ) :
    ∑ s ∈ I, (if owner s = q then radius q (targetIndex q s) else 0) ≤
      ∑ t ∈ target q, radius q t := by
  classical
  let F := I.filter fun s => owner s = q
  have hsum :
      (∑ s ∈ I,
        (if owner s = q then radius q (targetIndex q s) else 0)) =
        ∑ s ∈ F, radius q (targetIndex q s) := by
    simp [F, Finset.sum_filter]
  rw [hsum]
  calc
    (∑ s ∈ F, radius q (targetIndex q s)) =
        ∑ t ∈ F.image (targetIndex q), radius q t := by
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact hinj q (by simpa [F] using ha) (by simpa [F] using hb) hab
    _ ≤ ∑ t ∈ target q, radius q t := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro t ht
        obtain ⟨s, hsF, rfl⟩ := Finset.mem_image.mp ht
        have hsI : s ∈ I := (Finset.mem_filter.mp hsF).1
        have howner : owner s = q := (Finset.mem_filter.mp hsF).2
        exact hmem q s hsI howner
      · intro _ _ _
        omega

/-- Construct all two-half charging data from an actual embedding of each
original distinguished side into a target of its owning child.

The equality `hspan` is the survivor-or-quadrilateral geometric conclusion.
Once it is known, membership follows from the child `SumBound` witness, and
fibrewise injectivity proves both charging inequalities. -/
noncomputable def twoHalfChargingConfiguration_of_targetEmbedding
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (A : TwoHalfAuxiliaryCycleFamily D (b : ℝ) index)
    (I : Finset ℕ) (lam : ℕ → Λ) (span : ℕ → G)
    (owner : ℕ → Sum (Fin index.first.pieceCount)
      (Fin index.second.pieceCount))
    (targetIndex : Sum (Fin index.first.pieceCount)
      (Fin index.second.pieceCount) → ℕ → ℕ)
    (htarget : ∀ s ∈ I,
      match owner s with
      | Sum.inl j => targetIndex (Sum.inl j) s ∈ (A.firstChildren j).target
      | Sum.inr j => targetIndex (Sum.inr j) s ∈ (A.secondChildren j).target)
    (hlabel : ∀ s ∈ I,
      match owner s with
      | Sum.inl j => (A.firstChildren j).label
          (targetIndex (Sum.inl j) s) = lam s
      | Sum.inr j => (A.secondChildren j).label
          (targetIndex (Sum.inr j) s) = lam s)
    (hspan : ∀ s ∈ I,
      match owner s with
      | Sum.inl j => span s = (A.firstChildren j).sideSpan
          (targetIndex (Sum.inl j) s)
      | Sum.inr j => span s = (A.secondChildren j).sideSpan
          (targetIndex (Sum.inr j) s))
    (hinj : ∀ q, Set.InjOn (targetIndex q)
      (↑(I.filter fun s => owner s = q) : Set ℕ)) :
    TwoHalfChargingConfiguration D hsymm b hδ A I lam span := by
  let childRadius : Sum (Fin index.first.pieceCount)
      (Fin index.second.pieceCount) → ℕ → ℕ := fun q s =>
    match q with
    | Sum.inl j => (A.firstChildren j).radius D hsymm b hδ
        s
    | Sum.inr j => (A.secondChildren j).radius D hsymm b hδ
        s
  let radius : Sum (Fin index.first.pieceCount)
      (Fin index.second.pieceCount) → ℕ → ℕ := fun q s =>
    childRadius q (targetIndex q s)
  refine
    { owner := owner
      radius := radius
      original_mem := ?_
      firstCharge := ?_
      secondCharge := ?_ }
  · intro s hs
    have ht := htarget s hs
    have hl := hlabel s hs
    have he := hspan s hs
    generalize hq : owner s = q at ht hl he ⊢
    cases q with
    | inl j =>
        change span s ∈ D.relBall (lam s)
          ((A.firstChildren j).radius D hsymm b hδ
            (targetIndex (Sum.inl j) s))
        rw [he, ← hl]
        exact AuxiliaryCycleCertificate.sideSpan_mem_radius
          D hsymm b hδ (A.firstChildren j) _ ht
    | inr j =>
        change span s ∈ D.relBall (lam s)
          ((A.secondChildren j).radius D hsymm b hδ
            (targetIndex (Sum.inr j) s))
        rw [he, ← hl]
        exact AuxiliaryCycleCertificate.sideSpan_mem_radius
          D hsymm b hδ (A.secondChildren j) _ ht
  · intro j
    have hcharge := sum_ownerFiber_targetRadius_le I owner
      (fun q => match q with
        | Sum.inl i => (A.firstChildren i).target
        | Sum.inr i => (A.secondChildren i).target)
      targetIndex childRadius
      (fun q s hs hq => by
        subst q
        cases howner : owner s <;> simpa [howner] using htarget s hs)
      hinj (Sum.inl j)
    simpa [radius, childRadius] using hcharge
  · intro j
    have hcharge := sum_ownerFiber_targetRadius_le I owner
      (fun q => match q with
        | Sum.inl i => (A.firstChildren i).target
        | Sum.inr i => (A.secondChildren i).target)
      targetIndex childRadius
      (fun q s hs hq => by
        subst q
        cases howner : owner s <;> simpa [howner] using htarget s hs)
      hinj (Sum.inr j)
    simpa [radius, childRadius] using hcharge

/-! ## Side accounting and the final producer -/

/-- Exact side accounting for the concrete two-half path family.

`baseSides` counts inherited polygon sides and `extraSides` counts connectors
and chord segments.  The pointwise equations retain the actual path lengths;
the two global inequalities are precisely the partition and quadratic
traversal estimates proved by the component-surgery geometry. -/
structure TwoHalfSideAccounting
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {b : ℕ} {I₁ I₂ : Finset ℕ}
    {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ} {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (P : TwoHalfPathInput D hsymm b index) (n : ℕ) where
  firstBaseSides : Fin index.first.pieceCount → ℕ
  firstExtraSides : Fin index.first.pieceCount → ℕ
  secondBaseSides : Fin index.second.pieceCount → ℕ
  secondExtraSides : Fin index.second.pieceCount → ℕ
  first_count : ∀ j, (P.first j).sideCount =
    firstBaseSides j + firstExtraSides j
  second_count : ∀ j, (P.second j).sideCount =
    secondBaseSides j + secondExtraSides j
  base_partition :
    (∑ j, firstBaseSides j) + ∑ j, secondBaseSides j = n
  extra_upper :
    (∑ j, firstExtraSides j) + ∑ j, secondExtraSides j ≤
      6 * ((2 * chordLength + 1) * (2 * chordLength + 1))
  first_small : ∀ j, 5 * (P.first j).sideCount ≤ 4 * n
  second_small : ∀ j, 5 * (P.second j).sideCount ≤ 4 * n

namespace TwoHalfSideAccounting

/-- Path-length hypotheses in the form directly proved by the greedy surgery.

Each interval has at most two connector edges.  The chord paths consist of the
successive partner intervals together with the two end intervals in each
half, giving the displayed quadratic total. -/
structure PathLengthBounds
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {b : ℕ} {I₁ I₂ : Finset ℕ}
    {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ} {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (P : TwoHalfPathInput D hsymm b index) (n : ℕ) where
  arc_partition :
    (∑ j, (P.first j).arcSides) + ∑ j, (P.second j).arcSides = n
  first_connectors : ∀ j,
    (P.first j).left.length + (P.first j).right.length ≤ 2
  second_connectors : ∀ j,
    (P.second j).left.length + (P.second j).right.length ≤ 2
  chord_total :
    (∑ j, (P.first j).chord.length) +
        ∑ j, (P.second j).chord.length ≤
      2 * (chordLength * chordLength) + 4 * chordLength
  first_small : ∀ j, 5 * (P.first j).sideCount ≤ 4 * n
  second_small : ∀ j, 5 * (P.second j).sideCount ≤ 4 * n

/-- Actual path lengths give the abstract side-accounting certificate. -/
def ofPathLengthBounds
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {b : ℕ} {I₁ I₂ : Finset ℕ}
    {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ} {chordLength n : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {P : TwoHalfPathInput D hsymm b index}
    (H : PathLengthBounds P n) : TwoHalfSideAccounting P n := by
  let firstExtra : Fin index.first.pieceCount → ℕ := fun j =>
    (P.first j).left.length + (P.first j).right.length +
      (P.first j).chord.length
  let secondExtra : Fin index.second.pieceCount → ℕ := fun j =>
    (P.second j).left.length + (P.second j).right.length +
      (P.second j).chord.length
  have hfirstConnector :
      (∑ j, ((P.first j).left.length + (P.first j).right.length)) ≤
        2 * index.first.pieceCount := by
    calc
      (∑ j, ((P.first j).left.length + (P.first j).right.length)) ≤
          ∑ _j : Fin index.first.pieceCount, 2 :=
        Finset.sum_le_sum fun j _ => H.first_connectors j
      _ = 2 * index.first.pieceCount := by simp [mul_comm]
  have hsecondConnector :
      (∑ j, ((P.second j).left.length + (P.second j).right.length)) ≤
        2 * index.second.pieceCount := by
    calc
      (∑ j, ((P.second j).left.length + (P.second j).right.length)) ≤
          ∑ _j : Fin index.second.pieceCount, 2 :=
        Finset.sum_le_sum fun j _ => H.second_connectors j
      _ = 2 * index.second.pieceCount := by simp [mul_comm]
  have hpiece := index.pieceCount_le
  have hpieces : index.first.pieceCount + index.second.pieceCount ≤
      2 * chordLength + 2 := by
    simpa [TwoHalfGreedyFamilyIndex.pieceCount] using hpiece
  have hconnectors :
      (∑ j, ((P.first j).left.length + (P.first j).right.length)) +
          ∑ j, ((P.second j).left.length + (P.second j).right.length) ≤
        4 * chordLength + 4 := by
    omega
  simp_rw [Finset.sum_add_distrib] at hconnectors
  have hextra :
      (∑ j, firstExtra j) + ∑ j, secondExtra j ≤
        6 * ((2 * chordLength + 1) * (2 * chordLength + 1)) := by
    simp_rw [firstExtra, secondExtra, Finset.sum_add_distrib]
    nlinarith [H.chord_total, hconnectors]
  exact
    { firstBaseSides := fun j => (P.first j).arcSides
      firstExtraSides := firstExtra
      secondBaseSides := fun j => (P.second j).arcSides
      secondExtraSides := secondExtra
      first_count := by
        intro j
        simp [AuxiliaryCyclePathInput.sideCount, firstExtra]
        omega
      second_count := by
        intro j
        simp [AuxiliaryCyclePathInput.sideCount, secondExtra]
        omega
      base_partition := H.arc_partition
      extra_upper := hextra
      first_small := H.first_small
      second_small := H.second_small }

theorem count_lower
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {b : ℕ} {I₁ I₂ : Finset ℕ}
    {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ} {chordLength n : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {P : TwoHalfPathInput D hsymm b index}
    (C : TwoHalfSideAccounting P n) :
    n ≤ (∑ j, (P.first j).sideCount) +
      ∑ j, (P.second j).sideCount := by
  have htotal :
      (∑ j, (P.first j).sideCount) + ∑ j, (P.second j).sideCount =
        ((∑ j, C.firstBaseSides j) + ∑ j, C.secondBaseSides j) +
        ((∑ j, C.firstExtraSides j) + ∑ j, C.secondExtraSides j) := by
    simp_rw [C.first_count, C.second_count, Finset.sum_add_distrib]
    omega
  calc
    n ≤ n + ((∑ j, C.firstExtraSides j) +
        ∑ j, C.secondExtraSides j) := Nat.le_add_right _ _
    _ = ((∑ j, C.firstBaseSides j) + ∑ j, C.secondBaseSides j) +
        ((∑ j, C.firstExtraSides j) +
          ∑ j, C.secondExtraSides j) := by rw [C.base_partition]
    _ = (∑ j, (P.first j).sideCount) +
        ∑ j, (P.second j).sideCount := htotal.symm

theorem count_upper
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {b : ℕ} {I₁ I₂ : Finset ℕ}
    {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ} {chordLength n : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {P : TwoHalfPathInput D hsymm b index}
    (C : TwoHalfSideAccounting P n) :
    (∑ j, (P.first j).sideCount) +
        ∑ j, (P.second j).sideCount ≤
      n + 6 * ((2 * chordLength + 1) * (2 * chordLength + 1)) := by
  have htotal :
      (∑ j, (P.first j).sideCount) + ∑ j, (P.second j).sideCount =
        ((∑ j, C.firstBaseSides j) + ∑ j, C.secondBaseSides j) +
        ((∑ j, C.firstExtraSides j) + ∑ j, C.secondExtraSides j) := by
    simp_rw [C.first_count, C.second_count, Finset.sum_add_distrib]
    omega
  calc
    (∑ j, (P.first j).sideCount) +
        ∑ j, (P.second j).sideCount =
        ((∑ j, C.firstBaseSides j) + ∑ j, C.secondBaseSides j) +
          ((∑ j, C.firstExtraSides j) +
            ∑ j, C.secondExtraSides j) := htotal
    _ = n + ((∑ j, C.firstExtraSides j) +
          ∑ j, C.secondExtraSides j) := by rw [C.base_partition]
    _ ≤ n + 6 * ((2 * chordLength + 1) *
          (2 * chordLength + 1)) := Nat.add_le_add_left C.extra_upper n

end TwoHalfSideAccounting

/-- The complete two-half producer from concrete interval paths, an injective
target assignment, and exact path-length accounting. -/
noncomputable def auxiliaryCycleFamilyCertificate_of_pathInput
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    (index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength)
    (P : TwoHalfPathInput D hsymm b index)
    (n : ℕ) (v : G) (word : List (RelLetter G Λ)) (cut : ℕ → ℕ)
    (I : Finset ℕ) (lam : ℕ → Λ)
    (owner : ℕ → Sum (Fin index.first.pieceCount)
      (Fin index.second.pieceCount))
    (targetIndex : Sum (Fin index.first.pieceCount)
      (Fin index.second.pieceCount) → ℕ → ℕ)
    (htarget : ∀ s ∈ I,
      match owner s with
      | Sum.inl j => targetIndex (Sum.inl j) s ∈
          ((P.family).firstChildren j).target
      | Sum.inr j => targetIndex (Sum.inr j) s ∈
          ((P.family).secondChildren j).target)
    (hlabel : ∀ s ∈ I,
      match owner s with
      | Sum.inl j => ((P.family).firstChildren j).label
          (targetIndex (Sum.inl j) s) = lam s
      | Sum.inr j => ((P.family).secondChildren j).label
          (targetIndex (Sum.inr j) s) = lam s)
    (hspan : ∀ s ∈ I,
      match owner s with
      | Sum.inl j =>
          (vertex v word (cut s))⁻¹ * vertex v word (cut (s + 1)) =
            ((P.family).firstChildren j).sideSpan
              (targetIndex (Sum.inl j) s)
      | Sum.inr j =>
          (vertex v word (cut s))⁻¹ * vertex v word (cut (s + 1)) =
            ((P.family).secondChildren j).sideSpan
              (targetIndex (Sum.inr j) s))
    (hinj : ∀ q, Set.InjOn (targetIndex q)
      (↑(I.filter fun s => owner s = q) : Set ℕ))
    (counts : TwoHalfSideAccounting P n) :
    AuxiliaryCycleFamilyCertificate D hsymm b hδ n v word cut I lam := by
  let A := P.family
  let C : TwoHalfChargingConfiguration D hsymm b hδ A I lam
      (fun s => (vertex v word (cut s))⁻¹ * vertex v word (cut (s + 1))) :=
    twoHalfChargingConfiguration_of_targetEmbedding D hsymm b hδ A I lam
      (fun s => (vertex v word (cut s))⁻¹ * vertex v word (cut (s + 1)))
      owner targetIndex htarget hlabel hspan hinj
  apply auxiliaryCycleFamilyCertificate_of_twoHalf D hsymm b hδ index A
    n v word cut I lam C
  · exact counts.count_lower
  · exact counts.count_upper
  · exact counts.first_small
  · exact counts.second_small

/-- The complete producer with side accounting read directly from the stored
four paths. -/
noncomputable def auxiliaryCycleFamilyCertificate_of_pathLengths
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    (index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength)
    (P : TwoHalfPathInput D hsymm b index)
    (n : ℕ) (v : G) (word : List (RelLetter G Λ)) (cut : ℕ → ℕ)
    (I : Finset ℕ) (lam : ℕ → Λ)
    (owner : ℕ → Sum (Fin index.first.pieceCount)
      (Fin index.second.pieceCount))
    (targetIndex : Sum (Fin index.first.pieceCount)
      (Fin index.second.pieceCount) → ℕ → ℕ)
    (htarget : ∀ s ∈ I,
      match owner s with
      | Sum.inl j => targetIndex (Sum.inl j) s ∈
          ((P.family).firstChildren j).target
      | Sum.inr j => targetIndex (Sum.inr j) s ∈
          ((P.family).secondChildren j).target)
    (hlabel : ∀ s ∈ I,
      match owner s with
      | Sum.inl j => ((P.family).firstChildren j).label
          (targetIndex (Sum.inl j) s) = lam s
      | Sum.inr j => ((P.family).secondChildren j).label
          (targetIndex (Sum.inr j) s) = lam s)
    (hspan : ∀ s ∈ I,
      match owner s with
      | Sum.inl j =>
          (vertex v word (cut s))⁻¹ * vertex v word (cut (s + 1)) =
            ((P.family).firstChildren j).sideSpan
              (targetIndex (Sum.inl j) s)
      | Sum.inr j =>
          (vertex v word (cut s))⁻¹ * vertex v word (cut (s + 1)) =
            ((P.family).secondChildren j).sideSpan
              (targetIndex (Sum.inr j) s))
    (hinj : ∀ q, Set.InjOn (targetIndex q)
      (↑(I.filter fun s => owner s = q) : Set ℕ))
    (lengths : TwoHalfSideAccounting.PathLengthBounds P n) :
    AuxiliaryCycleFamilyCertificate D hsymm b hδ n v word cut I lam :=
  auxiliaryCycleFamilyCertificate_of_pathInput D hsymm b hδ index P
    n v word cut I lam owner targetIndex htarget hlabel hspan hinj
    (TwoHalfSideAccounting.ofPathLengthBounds lengths)

end DGOProposition414
end GGT
end GroupApproximation
