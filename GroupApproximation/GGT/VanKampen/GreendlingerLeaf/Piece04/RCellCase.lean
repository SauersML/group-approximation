import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassSameCell
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassPairTransfer
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04: the relator-cell branch of GapSpan, side-vertex pairs refuted

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.4, Case 1, for a backwards class-word pair whose
source and target classes lie across one relator cell `Π = j`, with no endpoint strictly inside a gap
and not single-side (`OsinLemma94ClassCaseOneRCellStatement`, module
`Estimating.OsinLemma94ClassSameCell`).

## The reduction proved here

Only the four endpoint *vertices* of a connector pair enter its fields: `source_long`, `target_long`,
`start_geodesic` and `end_geodesic` mention the positions `a, a', b', b` only through
`vertex (corner i) (word i) x`, and the connectors are kept.  So a class pair `C` is *side-vertex*
(`SideVertexPair`) if there are sides `s` of the source class and `t` of the target class, at
offsets `off` and `off'`, and positions `x₀ < x₁ ≤ |w_s|`, `y₀ < y₁ ≤ |w_t|` with

  `vertex(off + x₀) = vertex(a)`, `vertex(off + x₁) = vertex(a')`,
  `vertex(off' + y₀) = vertex(b')`, `vertex(off' + y₁) = vertex(b)`

on the class words.  By `OsinLemma94ClassPolygons.vertex_eq_of_sideAt`, a class vertex at `off + x`
is `h · vertex_s(x)` for the common factor `h = (corner (classBase k % k_i))⁻¹`, since the gaps
have value one; the word metric is left invariant.  So the same connectors give a side-level pair
`C'` on the side words with `C'.source = s`, `C'.target = t`, `C'.a = x₀`, `C'.a' = x₁`,
`C'.b' = y₀ < y₁ = C'.b` (`exists_pair_of_vertices`).  Its sides are `.cell j` by `kind_eq`, so
`s` is an (A1) side, `t` is long and not cutting, `s ≠ t` since different classes share no side,
and `P.kind s = P.kind t`.  The side-level Case 1 of one cell, `osinLemma94CaseOneSameCell`, refutes
`C'` (`false_of_sideVertexPair`).  Hence `OsinLemma94ClassCaseOneRCellStatement` follows from the
same statement restricted to pairs that are not side-vertex (`ClassRCellSpanStatement`,
`rCell_of_span`).

Every single-side pair is side-vertex (`x₀ = a - off`, and so on), and a side-vertex pair need not be
single-side: an endpoint `a` at the end `off + |w_s|` of a side followed by a nonempty gap has the
vertex of the first position of the next side (`Piece04.exists_forward_side`), and symmetrically
for `a'`, `b'`, `b` (`exists_backward_side`).  These are the pairs whose segments reach a gap only at
an endpoint; they are refuted here.

## The residual `ClassRCellSpanStatement` (OPEN), planned

Let `C` be a residual pair.

1. *Normalization.*  Move `a` and `b'` forward, and `a'` and `b` backward, to side positions with
   the same vertices (`exists_forward_side`, `exists_backward_side`).  Since `C` is not side-vertex,
   the normalized source segment or the normalized target segment meets two different sides
   `s < s'` of one class: its window contains the whole gap `γ = g_s` after `s`, with side letters
   on both sides of it.
2. *The gap is a loop on `∂Π` at a pinch vertex.*  The class darts are the reversed arc `p` of `∂Π`
   (`cell_arc`), the sides are consecutive on the face walk of the polygon face `Γ`, and `γ` is a
   closed walk along `∂Π` from the end vertex `z` of `s` back to `z`.  If `γ` were empty, `s` and
   `s'` would be consecutive sides of one kind along one arc of `Π`, against `P.Maximal`; so `γ` is
   nonempty and `z` is a cut vertex of the face walk of `Γ ∪ Π`.
3. *The enclosed subdiagram of `γ`.*  The loop `γ` bounds a disc subdiagram `Σ_γ` on the side
   away from `Π`; `Γ` and `Σ_γ` share no edge (`OsinLemma94ClassGapCollapseModel`).  Its relator
   cells are relator cells of `Δ` other than `Π`, so `rCellCount Σ_γ < rCellCount Δ`.
4. *Pocket surgery on class words.*  The face walk reads `X T Y S` (`exists_sameCellWalk`) and `∂Π`
   reads `q B p A`, with `X B` and `Y A` of value `≠ 1` (the hypothesis of the residual).  The
   pocket loop `X B⁻¹` passes through `z` only along `∂Π`, never along `γ`, so it is a closed walk
   of `Δ`; its enclosed subdiagram contains a relator cell.  This is the step of
   `osinLemma94CaseOneSameCell` (the enclosed subdiagram `closedWalkEnclosedSubdiagramSucc`, the spur
   enclosure, the unpinch and the loop cut `OsinLoopCut.false_of_below`), which needs its arcs on
   the face walk (`htrav`).  The class version replaces `p` by the run `S` of `p` without its gaps,
   which is literally on the face walk, and needs the pocket statements of
   `OsinLemma94SameCellPocketPinch` with `p` and `q` read with their gaps: the gap loops of `p`
   lie inside `Σ_γ`, off the pocket, so the enclosed face set of the pocket is unchanged.
5. *Overlap.*  Without a rotation `q B p A` from the face walk, the windows `p` and `q` may share a
   dart through a gap; step 4 needs the rotation first, from the disjointness of the class sides
   (`classSides_disjoint`) and the planarity of `Σ_γ`.

Step 4 is the class-word generalization of the enclosure chain of `osinLemma94CaseOneSameCell`.  The
direct splits at `z` fail: splitting a long source segment at `z` needs a connector of length at most
`ε` to `z`, bounded only by `ε + const` (`OsinLemma94ClassGapSpanModel`).

## Contents

* `exists_pair_of_vertices`: a connector pair moves to other words with the same four endpoint
  vertices up to a common left factor, recording its source and target.
* `SideVertexPair`, `false_of_sideVertexPair`.
* `ClassRCellSpanStatement` (the residual), `rCell_of_span`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

universe u w v

open GroupApproximation.WordMetric
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

section Shift

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **A connector pair moves to words with the same endpoint vertices.**  If the four endpoint
vertices of `C` are `h` times vertices of `word' s` at `x₀ < x₁` and of `word' t` at `y₀ < y₁`, the same
connectors give a backwards pair on the new words, from `s` to `t`. -/
theorem exists_pair_of_vertices {D : RelGenSet G Lambda} {v v' : ℕ → G}
    {word word' : ℕ → List (RelLetter G Lambda)} {n n' eps : ℕ} {A B A' B' : Set ℕ}
    (C : WordConnectorPair D v word n A B eps) (h : G) {s t x0 x1 y0 y1 : ℕ}
    (hs : s < n') (ht : t < n') (hsA : s ∈ A') (htB : t ∈ B') (hst : s ≠ t)
    (hsadm : HullSC.RelWord.IsAdmissible D (word' s))
    (htadm : HullSC.RelWord.IsAdmissible D (word' t))
    (hx : x0 < x1) (hx1 : x1 ≤ (word' s).length) (hy : y0 < y1) (hy1 : y1 ≤ (word' t).length)
    (eA : OsinComponents.vertex (v C.source) (word C.source) C.a =
      h * OsinComponents.vertex (v' s) (word' s) x0)
    (eA' : OsinComponents.vertex (v C.source) (word C.source) C.a' =
      h * OsinComponents.vertex (v' s) (word' s) x1)
    (eB : OsinComponents.vertex (v C.target) (word C.target) C.b =
      h * OsinComponents.vertex (v' t) (word' t) y1)
    (eB' : OsinComponents.vertex (v C.target) (word C.target) C.b' =
      h * OsinComponents.vertex (v' t) (word' t) y0) :
    ∃ C' : WordConnectorPair D v' word' n' A' B' eps,
      C'.source = s ∧ C'.target = t ∧ C'.b' < C'.b := by
  obtain ⟨hletS, hmulS, hlenS⟩ := C.start_geodesic
  obtain ⟨hletE, hmulE, hlenE⟩ := C.end_geodesic
  have hlong := C.source_long
  have hlongT := C.target_long
  rw [eA, eA', wordDist_left_invariant] at hlong
  rw [eB, eB', wordDist_left_invariant] at hlongT
  rw [eB, eA, mul_assoc] at hmulS
  rw [eB, eA, wordDist_left_invariant] at hlenS
  rw [eA', eB', mul_assoc] at hmulE
  rw [eA', eB', wordDist_left_invariant] at hlenE
  let C' : WordConnectorPair D v' word' n' A' B' eps :=
    { source := s
      target := t
      source_lt := hs
      target_lt := ht
      source_mem := hsA
      target_mem := htB
      distinct := hst
      source_admissible := hsadm
      target_admissible := htadm
      a := x0
      a' := x1
      b := y1
      b' := y0
      a_le := by omega
      a'_le := hx1
      b_le := hy1
      b'_le := by omega
      source_forward := hx
      source_long := hlong
      target_long := hlongT
      startConnector := C.startConnector
      endConnector := C.endConnector
      start_geodesic := ⟨hletS, mul_left_cancel hmulS, hlenS⟩
      end_geodesic := ⟨hletE, mul_left_cancel hmulE, hlenE⟩
      start_short := C.start_short
      end_short := C.end_short }
  exact ⟨C', rfl, rfl, hy⟩

end Shift

section SideVertex

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- **A side-vertex pair.**  The four endpoint vertices of the class pair `C` are vertices of the
class words at positions `off + x₀ < off + x₁` inside the word of a source side `s` and
`off' + y₀ < off' + y₁` inside the word of a target side `t`. -/
def SideVertexPair (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k) (Q.word k) (Q.classCount k)
      (Q.relatorClasses k) (Q.longClasses k) eps) : Prop :=
  ∃ s off x0 x1 t off' y0 y1 : ℕ,
    Q.SideAt k C.source s off ∧ x0 < x1 ∧ x1 ≤ (P.word k s).length ∧
      OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) (off + x0) =
        OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) C.a ∧
      OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) (off + x1) =
        OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) C.a' ∧
      Q.SideAt k C.target t off' ∧ y0 < y1 ∧ y1 ≤ (P.word k t).length ∧
      OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) (off' + y0) =
        OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) C.b' ∧
      OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) (off' + y1) =
        OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) C.b

/-- The class vertex at `off + x` inside side `s` is the side vertex at `x`, up to the common factor
`(corner (classBase k % k_i))⁻¹`. -/
theorem vertex_add_eq_of_sideAt (Q : OsinLemma94ClassPolygons P) {k : Fin P.count} {i s off x : ℕ}
    (hi : i < Q.classCount k) (hat : Q.SideAt k i s off) (hx : x ≤ (P.word k s).length) :
    OsinComponents.vertex (Q.corner k i) (Q.word k i) (off + x) =
      (P.corner k (Q.classBase k % P.sideCount k))⁻¹ *
        OsinComponents.vertex (P.corner k s) (P.word k s) x := by
  rw [Q.vertex_eq_of_sideAt hi hat (Nat.le_add_right off x) (by omega), Nat.add_sub_cancel_left]

/-- **Side-vertex pairs across one cell are refuted by the side-level Case 1.**  The hypothesis
`hside` is the conclusion of `osinLemma94CaseOneSameCell` for the polygon `k`. -/
theorem false_of_sideVertexPair (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k) (Q.word k) (Q.classCount k)
      (Q.relatorClasses k) (Q.longClasses k) eps)
    (hsv : SideVertexPair Q k C) {j : Fin S.diagram.rCellCount}
    (hks : Q.classKind k C.source = .cell j) (hkt : Q.classKind k C.target = .cell j)
    (hside : ∀ C' : WordConnectorPair (symmetricLabelAlphabet D) (P.corner k) (P.word k)
      (P.sideCount k) (P.relatorSides k) (P.longSides k) eps,
      C'.b' < C'.b → P.kind k C'.target ≠ .cutting → P.kind k C'.source = P.kind k C'.target →
        False) :
    False := by
  obtain ⟨s, off, x0, x1, t, off', y0, y1, hsAt, hx, hx1, eA, eA', htAt, hy, hy1, eB', eB⟩ := hsv
  have hsmem := Q.mem_of_sideAt hsAt
  have htmem := Q.mem_of_sideAt htAt
  have hps : P.kind k s = .cell j := (Q.kind_eq k C.source C.source_lt s hsmem).trans hks
  have hpt : P.kind k t = .cell j := (Q.kind_eq k C.target C.target_lt t htmem).trans hkt
  have hadm : ∀ {i x : ℕ}, x ∈ Q.classSides k i →
      HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) (Q.word k i) →
        HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) (P.word k x) := by
    intro i x hxi hw letter hletter
    refine hw letter ?_
    rw [Q.word_eq]
    exact List.mem_flatMap.mpr ⟨x, hxi, List.mem_append_left _ hletter⟩
  have hsrel : s ∈ P.relatorSides k := ⟨j, hps⟩
  have htlong : t ∈ P.longSides k := by
    show P.kind k t ≠ .short
    rw [hpt]
    intro hbad
    cases hbad
  have hst : s ≠ t := fun he =>
    Q.classSides_disjoint k C.source_lt C.target_lt C.distinct hsmem (he ▸ htmem)
  obtain ⟨C', hCs, hCt, hback'⟩ := exists_pair_of_vertices (v' := P.corner k) (word' := P.word k)
    (n' := P.sideCount k) (A' := P.relatorSides k) (B' := P.longSides k) C
    (P.corner k (Q.classBase k % P.sideCount k))⁻¹
    (Q.lt_sideCount_of_mem k _ C.source_lt s hsmem) (Q.lt_sideCount_of_mem k _ C.target_lt t htmem)
    hsrel htlong hst (hadm hsmem C.source_admissible) (hadm htmem C.target_admissible) hx hx1 hy hy1
    (eA.symm.trans (vertex_add_eq_of_sideAt Q C.source_lt hsAt (by omega)))
    (eA'.symm.trans (vertex_add_eq_of_sideAt Q C.source_lt hsAt hx1))
    (eB.symm.trans (vertex_add_eq_of_sideAt Q C.target_lt htAt hy1))
    (eB'.symm.trans (vertex_add_eq_of_sideAt Q C.target_lt htAt (by omega)))
  refine hside C' hback' ?_ ?_
  · rw [hCt, hpt]
    intro hbad
    cases hbad
  · rw [hCs, hCt, hps, hpt]

end SideVertex

/-- **The relator-cell branch of GapSpan, spanning pairs** (residual, OPEN).
`OsinLemma94ClassCaseOneRCellStatement` for the pairs that are moreover not side-vertex
(`SideVertexPair`): after moving the endpoints to side positions with the same vertices, the source
or the target segment meets two sides of its class, across a whole gap. -/
def ClassRCellSpanStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              (∀ (Xi : DiscDiagram.{u, w, v} W)
                  (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
                Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
                  ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi,
                    OsinLemma97bConclusion mu T) →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∀ P : OsinLemma94RealizedPolygons S, P.Maximal →
                    ∀ (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
                      (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k) (Q.word k)
                        (Q.classCount k) (Q.relatorClasses k) (Q.longClasses k) eps),
                      C.b' < C.b → ¬ Q.GapEndpoint k C → ¬ Q.SingleSidePair k C →
                      ¬ SideVertexPair Q k C →
                      ∀ (j : Fin S.diagram.rCellCount)
                        (sourceArc targetArc : CyclicArc (cellDarts S.diagram j))
                        (X Y : List S.diagram.toCombMap.Dart) (r : ℕ),
                        Q.classKind k C.source = .cell j → Q.classKind k C.target = .cell j →
                        (S.diagram.faceBoundary (P.face k)).darts.rotate r =
                          X ++ Q.runWindow k C.target C.b' C.b ++ Y ++
                            Q.runWindow k C.source C.a C.a' →
                        sourceArc.reverseDarts = Q.classWindow k C.source C.a C.a' →
                        targetArc.reverseDarts = Q.classWindow k C.target C.b' C.b →
                        OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) C.a' *
                            RelLetter.listVal (dartWord S.diagram X) =
                          OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) C.b' →
                        OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) C.b *
                            RelLetter.listVal (dartWord S.diagram Y) =
                          OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) C.a →
                        (∀ (n : ℕ) (B A : List S.diagram.toCombMap.Dart),
                          (cellDarts S.diagram j).rotate n =
                              targetArc.darts ++ B ++ sourceArc.darts ++ A →
                            RelLetter.listVal (dartWord S.diagram (X ++ B)) ≠ 1 ∧
                              RelLetter.listVal (dartWord S.diagram (Y ++ A)) ≠ 1) →
                        False

/-- **The relator-cell branch of GapSpan from its spanning pairs.**  Side-vertex pairs are refuted
by `false_of_sideVertexPair` and `osinLemma94CaseOneSameCell`; the others are the residual. -/
theorem rCell_of_span (hspan : ClassRCellSpanStatement.{u, w, v}) :
    OsinLemma94ClassCaseOneRCellStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨e1, hside1⟩ :=
    osinLemma94CaseOneSameCell.{u, w, v} D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨e2, hspan1⟩ := hspan D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨max e1 e2, fun eps heps => ?_⟩
  obtain ⟨r1, hr1, hside2⟩ := hside1 eps (le_of_max_le_left heps)
  obtain ⟨r2, _, hspan2⟩ := hspan1 eps (le_of_max_le_right heps)
  refine ⟨max r1 r2, lt_of_lt_of_le hr1 (le_max_left _ _), fun rho hrho => ?_⟩
  intro W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax Q k C hback hnogap hnotsingle j
    sourceArc targetArc X Y r hks hkt htrav hsource htarget hX hY hval
  by_cases hsv : SideVertexPair Q k C
  · exact false_of_sideVertexPair Q k C hsv hks hkt
      (hside2 rho (le_of_max_le_left hrho) W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax
        k)
  · exact hspan2 rho (le_of_max_le_right hrho) W hW Delta cuts hleast hpos hbelow S hcard hmin P
      hmax Q k C hback hnogap hnotsingle hsv j sourceArc targetArc X Y r hks hkt htrav hsource
      htarget hX hY hval

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.exists_pair_of_vertices
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.false_of_sideVertexPair
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.rCell_of_span
