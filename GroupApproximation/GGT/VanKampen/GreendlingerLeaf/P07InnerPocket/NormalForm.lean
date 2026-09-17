import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.EnclosedRotate
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.Proof
import GroupApproximation.GGT.VanKampen.FaceSetBoundaryWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: the normal form of the enclosed pocket reading

Infrastructure for `P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`
(`GreendlingerLeaf/P07LakeExclusion/InnerTwoArcLong.lean`), Osin, arXiv:math/0411039v3, §9, proof of
Lemma 9.7(b) (lane gl-p07-14).  The earlier lanes produce an `EnclosedFaceSetSucc X F L` that holds
a relator cell `C`.  Its inverse walk reads `R₁ Ā₁ R₂ Ā₂`, where `A_t` is a cyclic arc of the cell
`Π_{k_t}`, that cell is off `F` whenever `A_t` is nonempty, and `|R_t| ≤ ε`.  This module turns
that data into the exact existential tuple of the residual, including the normalisation
`A₁.length = 0 ∨ 0 < A₂.length`.

## Truth check (on paper)

The statement is true; nothing beyond list identities is used.
* Every arc `A` of `cellDarts X k` has `|A.darts| = A.length` (`CyclicArc.darts_length`).  So an
  arc of length `0` reads no darts, and it can be replaced by the empty arc of any cell.
* The only extra hypothesis is a cell `Π_{k₀}` off `F`.  It is needed only when both arcs are
  empty.  Then some cell outside `F` must be named, and the tuple gives no other source for one.

## The mathematical proof

*Case `A₁.length = 0 ∨ 0 < A₂.length`.*  Keep `F`, `L`, `R₁`, `R₂`.  For `t = 1, 2`: if `A_t` is
nonempty, keep `(k_t, A_t)`, since `Π_{k_t} ∉ F` by hypothesis.  Otherwise use `(k₀, ∅)`, where
`∅ = P07LakeExclusion.emptyArc (cellDarts X k₀)`.  The inverse readings and the lengths are
unchanged (`exists_offArc_of_arc`), so the decomposition and the disjunction carry over.

*Case `0 < A₁.length` and `A₂.length = 0`.*  Here `invDarts X L = (R₁ ++ Ā₁) ++ R₂`, so
`|L| = |R₁| + |A₁| + |R₂|` and `|R₂| < |L|`.  Rotate the walk by `n = |R₂|`.
* `EnclosedFaceSetSucc.rotate` (lane gl-p07-13) keeps it enclosed with successor turns.
* `invDarts_rotate` gives `invDarts X (L.rotate n) = (invDarts X L).rotate (|L| - n % |L|)`, and
  `|L| - n % |L| = |R₁ ++ Ā₁|`.
* By `List.rotate_append_length_eq`, this equals `R₂ ++ (R₁ ++ Ā₁) = R₂ ++ ∅ ++ R₁ ++ Ā₁`.

So take `s₁ = R₂`, `s₂ = R₁`, first arc `∅` of `Π_{k₁}`, and second arc `A₁`.  This swaps the two
arcs.  Both cells are `Π_{k₁} ∉ F` (`k₁ = k₂` is allowed), and the first disjunct holds.

* `invDarts_darts_eq_nil_of_length_eq_zero`: an arc of length zero reads nothing.
* `exists_offArc_of_arc`: the normalisation of one arc.
* `EnclosedNormalFormStatement`, `enclosedNormalForm`: the lane statement and its proof.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

open Embedded HullSC WordMetric SimpleClosedWalkSides

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- An arc of length zero reads no inverse darts. -/
theorem invDarts_darts_eq_nil_of_length_eq_zero {X : DiscDiagram.{u, w, v} W}
    {k : Fin X.rCellCount} (A : CyclicArc (cellDarts X k)) (h : A.length = 0) :
    invDarts X A.darts = [] := by
  have hnil : A.darts = [] := List.eq_nil_of_length_eq_zero (by rw [CyclicArc.darts_length, h])
  rw [hnil]
  rfl

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.invDarts_darts_eq_nil_of_length_eq_zero

/-- **Normalising one arc.**  An arc that is nonempty only on a cell off `F` may be replaced by
an arc on a cell off `F`, with the same inverse reading and the same length. -/
theorem exists_offArc_of_arc (X : DiscDiagram.{u, w, v} W) (F : Finset X.toCombMap.Face)
    (k₀ k : Fin X.rCellCount) (hk₀ : (cell X k₀).face ∉ F) (A : CyclicArc (cellDarts X k))
    (hA : 0 < A.length → (cell X k).face ∉ F) :
    ∃ (k' : Fin X.rCellCount) (A' : CyclicArc (cellDarts X k')),
      (cell X k').face ∉ F ∧ invDarts X A'.darts = invDarts X A.darts ∧ A'.length = A.length := by
  by_cases h : 0 < A.length
  · exact ⟨k, A, hA h, rfl, rfl⟩
  · have h0 : A.length = 0 := by omega
    refine ⟨k₀, P07LakeExclusion.emptyArc (cellDarts X k₀), hk₀, ?_, ?_⟩
    · rw [invDarts_darts_eq_nil_of_length_eq_zero A h0]
      exact P07LakeExclusion.invDarts_emptyArc k₀
    · rw [h0]
      rfl

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.exists_offArc_of_arc

/-- **Lane gl-p07-14, statement.**  An enclosed face set with successor turns holds a relator
cell.  Suppose its inverse walk reads `R₁ Ā₁ R₂ Ā₂`, where each nonempty arc lies on a cell off
the set, some cell `Π_{k₀}` is off the set, and `|R_t| ≤ ε`.  Then it has the exact normal form
required by `P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`. -/
def EnclosedNormalFormStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (F : Finset X.toCombMap.Face)
    (L : List X.toCombMap.Dart), EnclosedFaceSetSucc X F L →
    ∀ C ∈ X.relatorCells, C.face ∈ F →
    ∀ (k₀ k₁ k₂ : Fin X.rCellCount) (A₁ : CyclicArc (cellDarts X k₁))
      (A₂ : CyclicArc (cellDarts X k₂)) (R₁ R₂ : List X.toCombMap.Dart),
      invDarts X L = R₁ ++ invDarts X A₁.darts ++ R₂ ++ invDarts X A₂.darts →
      (0 < A₁.length → (cell X k₁).face ∉ F) → (0 < A₂.length → (cell X k₂).face ∉ F) →
      (cell X k₀).face ∉ F → R₁.length ≤ eps → R₂.length ≤ eps →
        ∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart)
          (k₁' k₂' : Fin X.rCellCount) (A₁' : CyclicArc (cellDarts X k₁'))
          (A₂' : CyclicArc (cellDarts X k₂')) (s₁ s₂ : List X.toCombMap.Dart),
          EnclosedFaceSetSucc X faces outerWalk ∧
            (∃ C' ∈ X.relatorCells, C'.face ∈ faces) ∧
            (cell X k₁').face ∉ faces ∧ (cell X k₂').face ∉ faces ∧
            invDarts X outerWalk = s₁ ++ invDarts X A₁'.darts ++ s₂ ++ invDarts X A₂'.darts ∧
            s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ (A₁'.length = 0 ∨ 0 < A₂'.length)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.EnclosedNormalFormStatement

/-- **Lane gl-p07-14, proof.**  Normalise empty arcs to empty arcs of off cells.  When only the
second arc is empty, rotate the walk by `|R₂|` and swap the arcs. -/
theorem enclosedNormalForm : EnclosedNormalFormStatement.{u, w, v} := by
  intro G _ Lambda W eps X F L E C hC hCF k₀ k₁ k₂ A₁ A₂ R₁ R₂ hdec hk₁ hk₂ hk₀ hR₁ hR₂
  by_cases hcase : A₁.length = 0 ∨ 0 < A₂.length
  · obtain ⟨k₁', A₁', hk₁', hinv₁, hlen₁⟩ := exists_offArc_of_arc X F k₀ k₁ hk₀ A₁ hk₁
    obtain ⟨k₂', A₂', hk₂', hinv₂, hlen₂⟩ := exists_offArc_of_arc X F k₀ k₂ hk₀ A₂ hk₂
    refine ⟨F, L, k₁', k₂', A₁', A₂', R₁, R₂, E, ⟨C, hC, hCF⟩, hk₁', hk₂', ?_, hR₁, hR₂, ?_⟩
    · rw [hinv₁, hinv₂]
      exact hdec
    · rw [hlen₁, hlen₂]
      exact hcase
  · obtain ⟨hne₁, hnpos₂⟩ := not_or.mp hcase
    have hA₁ : 0 < A₁.length := by omega
    have hA₂ : A₂.length = 0 := by omega
    have hdec' : invDarts X L = (R₁ ++ invDarts X A₁.darts) ++ R₂ := by
      rw [hdec, invDarts_darts_eq_nil_of_length_eq_zero A₂ hA₂, List.append_nil]
    have hinvlen : (invDarts X A₁.darts).length = A₁.length := by
      rw [Embedded.invDarts_length, CyclicArc.darts_length]
    have hlenL : L.length = R₁.length + A₁.length + R₂.length := by
      have h := congrArg List.length hdec'
      rw [Embedded.invDarts_length, List.length_append, List.length_append, hinvlen] at h
      exact h
    have hlt : R₂.length < L.length := by omega
    have hmod : L.length - R₂.length % L.length = (R₁ ++ invDarts X A₁.darts).length := by
      rw [Nat.mod_eq_of_lt hlt, List.length_append, hinvlen]
      omega
    refine ⟨F, L.rotate R₂.length, k₁, k₁, P07LakeExclusion.emptyArc (cellDarts X k₁), A₁, R₂, R₁,
      EnclosedFaceSetSucc.rotate E R₂.length, ⟨C, hC, hCF⟩, hk₁ hA₁, hk₁ hA₁, ?_, hR₂, hR₁,
      Or.inl rfl⟩
    rw [invDarts_rotate, hmod, hdec', List.rotate_append_length_eq,
      P07LakeExclusion.invDarts_emptyArc]
    simp only [List.append_nil, List.append_assoc]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.enclosedNormalForm

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
