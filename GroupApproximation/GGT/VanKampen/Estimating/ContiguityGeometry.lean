import GroupApproximation.GGT.VanKampen.Estimating.ContiguityFinite

/-!
# Contiguity geometry before distinct-cell and O52 restrictions

The geometric record retains the actual region boundary, both arcs and
sides, metric bounds and shelling. A relator target may equal the source.
The historical Contiguity embeds into this geometry; its distinct-cell O52
certificate is separate data, supplied only when that piece lemma applies.
No geometric loop-exclusion theorem is encoded in candidate admissibility.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded

open WordMetric HullSC
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

structure ContiguityGeometry (D : RelGenSet G Lambda) (eps : ℕ)
    (Delta : DiscDiagram.{u, w, v} W) (faces : Finset Delta.toCombMap.Face) where
  boundary : FaceSetBoundary Delta faces
  source : Fin Delta.rCellCount
  target : Option (Fin Delta.rCellCount)
  sourceArc : CyclicArc (cellDarts Delta source)
  targetArc : CyclicArc (targetDarts Delta target)
  rightSide : List Delta.toCombMap.Dart
  leftSide : List Delta.toCombMap.Dart
  boundary_decomposition : boundary.cycle =
    sourceArc.reverseDarts ++ rightSide ++
      targetBoundaryDarts Delta target targetArc ++ leftSide
  rightSide_length_le : rightSide.length ≤ eps
  leftSide_length_le : leftSide.length ≤ eps
  rightSide_norm_le : wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord Delta rightSide)) ≤ eps
  leftSide_norm_le : wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord Delta leftSide)) ≤ eps
  pasting : ∃ l : List Delta.toCombMap.Face, FaceShelling Delta faces l boundary.cycle

variable {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {faces : Finset Delta.toCombMap.Face}

def Contiguity.toGeometry (H : Contiguity D eps Delta faces) :
    ContiguityGeometry D eps Delta faces where
  boundary := H.boundary
  source := H.source
  target := H.target
  sourceArc := H.sourceArc
  targetArc := H.targetArc
  rightSide := H.rightSide
  leftSide := H.leftSide
  boundary_decomposition := H.boundary_decomposition
  rightSide_length_le := H.rightSide_length_le
  leftSide_length_le := H.leftSide_length_le
  rightSide_norm_le := H.rightSide_norm_le
  leftSide_norm_le := H.leftSide_norm_le
  pasting := H.pasting

namespace ContiguityGeometry

theorem eq_of_data {H K : ContiguityGeometry D eps Delta faces}
    (hb : H.boundary.cycle = K.boundary.cycle)
    (hs : H.source = K.source) (ht : H.target = K.target)
    (hss : H.sourceArc.start.val = K.sourceArc.start.val)
    (hsl : H.sourceArc.length = K.sourceArc.length)
    (hts : H.targetArc.start.val = K.targetArc.start.val)
    (htl : H.targetArc.length = K.targetArc.length)
    (hr : H.rightSide = K.rightSide) (hl : H.leftSide = K.leftSide) : H = K := by
  cases H
  cases K
  cases hs
  cases ht
  have hboundary := FaceSetBoundary.eq_of_cycle_eq hb
  have hsource := CyclicArc.eq_of_start_length hss hsl
  have htarget := CyclicArc.eq_of_start_length hts htl
  cases hboundary
  cases hsource
  cases htarget
  cases hr
  cases hl
  rfl

theorem rightSide_nodup (H : ContiguityGeometry D eps Delta faces) : H.rightSide.Nodup := by
  have h := H.boundary.cycle_nodup
  rw [H.boundary_decomposition] at h
  have habc := (List.nodup_append.mp h).1
  have hab := (List.nodup_append.mp habc).1
  exact (List.nodup_append.mp hab).2.1

theorem leftSide_nodup (H : ContiguityGeometry D eps Delta faces) : H.leftSide.Nodup := by
  have h := H.boundary.cycle_nodup
  rw [H.boundary_decomposition] at h
  exact (List.nodup_append.mp h).2.1

def FiniteCode (Delta : DiscDiagram.{u, w, v} W) :=
  { l : List Delta.toCombMap.Dart // l.Nodup } ×
    (Σ i : Fin Delta.rCellCount,
      Fin ((cellDarts Delta i).length + 1) × Fin ((cellDarts Delta i).length + 1)) ×
    (Σ i : Option (Fin Delta.rCellCount),
      Fin ((targetDarts Delta i).length + 1) × Fin ((targetDarts Delta i).length + 1)) ×
    { l : List Delta.toCombMap.Dart // l.Nodup } ×
    { l : List Delta.toCombMap.Dart // l.Nodup }

noncomputable instance finiteCodeFintype : Fintype (FiniteCode Delta) := by
  classical
  unfold FiniteCode
  infer_instance

def finiteCode (H : ContiguityGeometry D eps Delta faces) : FiniteCode Delta :=
  ⟨⟨H.boundary.cycle, H.boundary.cycle_nodup⟩,
    ⟨H.source, H.sourceArc.start, ⟨H.sourceArc.length, Nat.lt_succ_iff.mpr H.sourceArc.length_le⟩⟩,
    ⟨H.target, H.targetArc.start, ⟨H.targetArc.length, Nat.lt_succ_iff.mpr H.targetArc.length_le⟩⟩,
    ⟨H.rightSide, H.rightSide_nodup⟩, ⟨H.leftSide, H.leftSide_nodup⟩⟩

theorem finiteCode_injective : Function.Injective (finiteCode : ContiguityGeometry D eps Delta faces → _) := by
  intro H K h
  have hb : H.boundary.cycle = K.boundary.cycle := congrArg (fun x => x.1.val) h
  have hs : H.source = K.source := congrArg (fun x => x.2.1.1) h
  have ht : H.target = K.target := congrArg (fun x => x.2.2.1.1) h
  have hss : H.sourceArc.start.val = K.sourceArc.start.val :=
    congrArg (fun x => x.2.1.2.1.val) h
  have hsl : H.sourceArc.length = K.sourceArc.length :=
    congrArg (fun x => x.2.1.2.2.val) h
  have hts : H.targetArc.start.val = K.targetArc.start.val :=
    congrArg (fun x => x.2.2.1.2.1.val) h
  have htl : H.targetArc.length = K.targetArc.length :=
    congrArg (fun x => x.2.2.1.2.2.val) h
  have hr : H.rightSide = K.rightSide := congrArg (fun x => x.2.2.2.1.val) h
  have hl : H.leftSide = K.leftSide := congrArg (fun x => x.2.2.2.2.val) h
  exact eq_of_data hb hs ht hss hsl hts htl hr hl

noncomputable instance contiguityFintype : Fintype (ContiguityGeometry D eps Delta faces) := by
  classical
  exact Fintype.ofInjective finiteCode finiteCode_injective

/-- Crossing a dart of the source cell arc enters a face of the embedded
G-cell region. -/
theorem faceOf_alpha_mem_of_mem_sourceArc
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : ContiguityGeometry D eps Delta faces)
    (d : Delta.toCombMap.Dart) (hd : d ∈ Gamma.sourceArc.darts) :
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∈ faces := by
  have hreverse : Delta.toCombMap.alpha d ∈ Gamma.sourceArc.reverseDarts := by
    simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse]
    exact ⟨d, hd, rfl⟩
  have hcycle : Delta.toCombMap.alpha d ∈ Gamma.boundary.cycle := by
    rw [Gamma.boundary_decomposition]
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl hreverse))
  exact (Gamma.boundary.cycle_mem_iff (Delta.toCombMap.alpha d)).mp hcycle |>.1

/-- When the target is a relator cell, crossing a dart of its target arc also
enters a face of the embedded G-cell region. -/
theorem faceOf_alpha_mem_of_mem_targetArc
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : ContiguityGeometry D eps Delta faces)
    (target : Fin Delta.rCellCount) (htarget : Gamma.target = some target)
    (d : Delta.toCombMap.Dart) (hd : d ∈ Gamma.targetArc.darts) :
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∈ faces := by
  have hreverse : Delta.toCombMap.alpha d ∈ Gamma.targetArc.reverseDarts := by
    simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse]
    exact ⟨d, hd, rfl⟩
  have htargetBoundary : Delta.toCombMap.alpha d ∈
      targetBoundaryDarts Delta Gamma.target Gamma.targetArc := by
    apply mem_targetBoundaryDarts_of_ne_none Delta Gamma.target
      Gamma.targetArc
    · rw [htarget]
      simp
    · exact hreverse
  have hcycle : Delta.toCombMap.alpha d ∈ Gamma.boundary.cycle := by
    rw [Gamma.boundary_decomposition]
    simp only [List.mem_append]
    exact Or.inl (Or.inr htargetBoundary)
  exact (Gamma.boundary.cycle_mem_iff (Delta.toCombMap.alpha d)).mp hcycle |>.1

/-- The region's simple boundary separates its two cell arcs even when
both arcs lie on the same relator cell. -/
theorem source_target_darts_disjoint (H : ContiguityGeometry D eps Delta faces)
    (i : Fin Delta.rCellCount) (ht : H.target = some i) :
    List.Disjoint H.sourceArc.darts H.targetArc.darts := by
  intro d hs htarc
  have hsrev : Delta.toCombMap.alpha d ∈ H.sourceArc.reverseDarts := by
    simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse]
    exact ⟨d, hs, rfl⟩
  have htrev : Delta.toCombMap.alpha d ∈ H.targetArc.reverseDarts := by
    simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse]
    exact ⟨d, htarc, rfl⟩
  have htb : Delta.toCombMap.alpha d ∈
      targetBoundaryDarts Delta H.target H.targetArc := by
    apply mem_targetBoundaryDarts_of_ne_none Delta H.target H.targetArc
    · rw [ht]
      simp
    · exact htrev
  have hnd := H.boundary.cycle_nodup
  rw [H.boundary_decomposition] at hnd
  have hdisj := (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.2
  exact hdisj _ (List.mem_append_left _ hsrev) _ htb rfl

/-- The distinct-cell hypotheses used by the historical O52 consumer. They
are not part of the geometric candidate definition. -/
structure O52Data (H : ContiguityGeometry D eps Delta faces) : Prop where
  target_ne_source : ∀ i, H.target = some i → H.source ≠ i
  certificate : ∀ i, H.target = some i →
    ∃ pre between suf : List (RelatorCell Delta.toCombMap Delta.outerFace W),
      Delta.relatorCells =
          pre ++ cell Delta H.source :: (between ++ cell Delta i :: suf) ∧
        (cell Delta H.source).reversed = false ∧
        (cell Delta i).reversed = false ∧
        RelLetter.listVal (dartWord Delta H.sourceArc.rotated) =
          RelLetter.listVal (cell Delta H.source).word ∧
        RelLetter.listVal (dartWord Delta H.targetArc.rotated) =
          RelLetter.listVal (cell Delta i).word ∧
        RelLetter.listVal (dartWord Delta H.targetArc.darts) *
            (RelLetter.listVal (dartWord Delta H.rightSide))⁻¹ =
          ((cell Delta H.source).conjugator⁻¹ *
            (between.map RelatorCell.value).prod *
            (cell Delta i).conjugator)⁻¹

def withO52 (H : ContiguityGeometry D eps Delta faces) (C : H.O52Data) :
    Contiguity D eps Delta faces where
  boundary := H.boundary
  source := H.source
  target := H.target
  sourceArc := H.sourceArc
  targetArc := H.targetArc
  rightSide := H.rightSide
  leftSide := H.leftSide
  boundary_decomposition := H.boundary_decomposition
  rightSide_length_le := H.rightSide_length_le
  leftSide_length_le := H.leftSide_length_le
  rightSide_norm_le := H.rightSide_norm_le
  leftSide_norm_le := H.leftSide_norm_le
  target_ne_source := C.target_ne_source
  o52Certificate := C.certificate
  pasting := H.pasting

theorem withO52_toGeometry (H : ContiguityGeometry D eps Delta faces) (C : H.O52Data) :
    (H.withO52 C).toGeometry = H := by
  apply eq_of_data <;> rfl

end ContiguityGeometry

theorem Contiguity.o52Data (H : Contiguity D eps Delta faces) : H.toGeometry.O52Data :=
  ⟨H.target_ne_source, H.o52Certificate⟩

theorem Contiguity.toGeometry_withO52 (H : Contiguity D eps Delta faces) :
    H.toGeometry.withO52 H.o52Data = H := by
  apply Contiguity.eq_of_data <;> rfl

theorem Contiguity.toGeometry_injective :
    Function.Injective (toGeometry : Contiguity D eps Delta faces → _) := by
  intro H K h
  apply Contiguity.eq_of_data
  · exact congrArg (fun J => J.boundary.cycle) h
  · exact congrArg (fun J => J.source) h
  · exact congrArg (fun J => J.target) h
  · exact congrArg (fun J => J.sourceArc.start.val) h
  · exact congrArg (fun J => J.sourceArc.length) h
  · exact congrArg (fun J => J.targetArc.start.val) h
  · exact congrArg (fun J => J.targetArc.length) h
  · exact congrArg (fun J => J.rightSide) h
  · exact congrArg (fun J => J.leftSide) h

end GroupApproximation.GGT.VanKampen.Embedded

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.ContiguityGeometry.finiteCode_injective
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.ContiguityGeometry.contiguityFintype
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.ContiguityGeometry.withO52_toGeometry
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.Contiguity.toGeometry_withO52
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.Contiguity.toGeometry_injective
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.ContiguityGeometry.source_target_darts_disjoint
