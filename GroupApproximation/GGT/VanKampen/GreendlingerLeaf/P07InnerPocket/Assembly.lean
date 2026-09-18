import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.AssemblyStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.AssemblyCellOff
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.NormalForm
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket assembly: the enclosed inner pocket from four pieces

Lane gl-p07-15.  The target is `P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`
(`InnerTwoArcLong.lean:55`), Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  It is reduced
to the residual `PocketFourPieceOffStatement` (`AssemblyStatement.lean`; the docstring there
explains why that residual is true and strictly smaller).

* `innerPocketEnclosed_of_pieces`: from lane 11's statement, lane 14's statement and the residual.
* `innerPocketEnclosed_of_fourPieceOff`: the same, with lanes 11 and 14 discharged by
  `pocketSideBound` and `enclosedNormalForm`.

There is no unconditional `innerPocketEnclosed`, because the residual is open.

## Proof route

Introduce the hypotheses and take the residual's face set `faces ∋ C` and outside walk.  A rotation
by `n` reads `R₁ ++ Ā₁ ++ R₂ ++ Ā₂`.
1. *Off cells.*  If `A₁` is nonempty, its darts are read on the walk, so `Π_i ∉ faces`
   (`Assembly.cell_face_not_mem_of_arc_on_walk`); likewise `Π_j` for `A₂`.  If both are empty,
   the residual names a cell `Π_{k₀} ∉ faces`.  In every case some `Π_{k₀} ∉ faces`.
2. *Bounds.*  Lane 11 turns the far-side labels into a rotation by `m` that reads
   `S₁ ++ V₁ ++ S₂ ++ V₂` with `|S_t| ≤ ε`, and either `V_t = Ā_t`, or `A₂` empty with `V₁ = []`
   and `V₂ = Ā₁`.
3. *Normal form.*  Lane 14 takes the rotated walk (`EnclosedFaceSetSucc.rotate`) and returns the
   target tuple.  In the first case its arcs are `A₁` and `A₂`.  In the second they are the empty
   arc of `Π_{k₀}` (`P07LakeExclusion.emptyArc`) and `A₁`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The enclosed inner pocket from lane 11, lane 14 and the labelled four-piece reading.** -/
theorem innerPocketEnclosed_of_pieces (h11 : PocketSideBoundStatement.{u, w, v})
    (h14 : EnclosedNormalFormStatement.{u, w, v}) (h : PocketFourPieceOffStatement.{u, w, v}) :
    P07LakeExclusion.InnerPocketEnclosedTwoArcStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff
    hinner houter C hC hCf hCa hCb
  obtain ⟨faces, outerWalk, n, R₁, R₂, A₁, A₂, E, hCF, hdec, hcase, hk₀⟩ :=
    h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff hinner houter C hC hCf
      hCa hCb
  have hoff₁ : 0 < A₁.length → (cell X i).face ∉ faces :=
    Assembly.cell_face_not_mem_of_arc_on_walk E A₁ n (fun x hx => by
      rw [hdec]
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
        (List.mem_append.mpr (Or.inr hx))))))
  have hoff₂ : 0 < A₂.length → (cell X j).face ∉ faces :=
    Assembly.cell_face_not_mem_of_arc_on_walk E A₂ n (fun x hx => by
      rw [hdec]
      exact List.mem_append.mpr (Or.inr hx))
  have hcell : ∃ k₀ : Fin X.rCellCount, (cell X k₀).face ∉ faces := by
    by_cases hp₁ : 0 < A₁.length
    · exact ⟨i, hoff₁ hp₁⟩
    · by_cases hp₂ : 0 < A₂.length
      · exact ⟨j, hoff₂ hp₂⟩
      · exact hk₀ (by omega) (by omega)
  obtain ⟨k₀, hk₀'⟩ := hcell
  obtain ⟨m, S₁, V₁, S₂, V₂, hdec', hS₁, hS₂, hV⟩ :=
    h11 D eps X i j a b outerWalk n R₁ (invDarts X A₁.darts) R₂ (invDarts X A₂.darts) E.nodup hdec
      (by
        rcases hcase with hc | ⟨hfar, hA⟩
        · exact Or.inl hc
        · exact Or.inr ⟨hfar, hA.imp (sideBound_invDarts_eq_nil_iff A₁).mpr
            (sideBound_invDarts_eq_nil_iff A₂).mpr⟩)
  rcases hV with ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩
  · exact h14 eps X faces (outerWalk.rotate m) (EnclosedFaceSetSucc.rotate E m) C hC hCF k₀ i j
      A₁ A₂ S₁ S₂ hdec' hoff₁ hoff₂ hk₀' hS₁ hS₂
  · exact h14 eps X faces (outerWalk.rotate m) (EnclosedFaceSetSucc.rotate E m) C hC hCF k₀ k₀ i
      (P07LakeExclusion.emptyArc (cellDarts X k₀)) A₁ S₁ S₂
      (by rw [P07LakeExclusion.invDarts_emptyArc]; exact hdec') (fun _ => hk₀') hoff₁ hk₀' hS₁ hS₂

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.innerPocketEnclosed_of_pieces

/-- **The enclosed inner pocket from the labelled four-piece reading**, with lanes 11 and 14
proved. -/
theorem innerPocketEnclosed_of_fourPieceOff (h : PocketFourPieceOffStatement.{u, w, v}) :
    P07LakeExclusion.InnerPocketEnclosedTwoArcStatement.{u, w, v} :=
  innerPocketEnclosed_of_pieces pocketSideBound enclosedNormalForm h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.innerPocketEnclosed_of_fourPieceOff

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
