import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.InPlace
import GroupApproximation.Meta.AxiomGuard

/-!
# In-place rose steps by filtering the boundary cycle

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  This module reduces the in-place rose step
(`RoseInPlaceStepStatement`, module `P10Rose/Proof`) to one existence claim about sub-lists of the
boundary cycle, `RoseFilterStepStatement`, and proves the reduction.

## The filter step (proved)

Write `c = K.boundary.cycle = s₁ ++ t₁⁻¹ ++ s₂ ++ t₂` and let `p` be a Boolean predicate on darts,
true on the arcs `t₁⁻¹` and `t₂`.  Filtering commutes with `++`, and `p` keeps every arc dart, so

  `c.filter p = s₁.filter p ++ t₁⁻¹ ++ s₂.filter p ++ t₂`   (`filter_cycle_eq`).

Suppose a face set `F'` avoids the exterior face and the source cell, contains some relator cell,
and its boundary darts are exactly the darts of `c` on which `p` holds.  Then the list above is a
duplicate-free listing of `∂F'` with sides `sᵢ.filter p`, no longer than `sᵢ`, hence no longer than
`ε`, and with the old arcs, which are proper and between `lo` and `hi`.  Moreover
`c ~ c.filter p ++ c.filter (¬p)` (`List.filter_append_perm`).  If `c.filter p` is a closed walk and
some kept dart `x` shares its vertex with a removed dart `y`, `step_of_faces` gives a pocket face
set in walk order with proper arcs and strictly fewer repeated visits (`step_of_filter`).

## The remaining claim (`RoseFilterStepStatement`)

Under the hypotheses of the rose step, such a pair `(F', p)` exists.  The intended witness is a
*region-union move*.  Call the classes of `FaceClassStep (walkKeep c)` regions; each is an
`F`-region or a non-`F` region, the exterior region `E` contains the exterior face and `L_s`
contains the source cell.  For a set `Ns` of non-`F` regions other than `E` and `L_s` and a set
`Fs` of `F`-regions not containing the kept cell, put `F' = (F \ Fs) ∪ Ns`.

1. *Boundary.*  A dart off `c` whose reverse is off `c` joins two faces of one region, so it is
   interior or exterior to `F'` together with its reverse.  A dart `d ∈ c` has `face d` in an
   `F`-region `A` and `face (α d)` in a non-`F` region `N`; it stays on `∂F'` iff `A ∉ Fs` and
   `N ∉ Ns`, and its reverse is never a boundary dart of `F'` unless `A ∈ Fs` and `N ∈ Ns`, which a
   move chooses to avoid.  So `∂F' = c.filter p` with `p d = (A ∉ Fs ∧ N ∉ Ns)`.
2. *Arcs.*  A dart of `t₂` faces the exterior face, in `E ∉ Ns`; a dart of `t₁⁻¹` faces the source
   cell, in `L_s ∉ Ns`.  Both are kept by `p` as long as `Fs` avoids their `F`-regions, which the
   move also chooses.
3. *Walk order.*  `c.filter p` is a closed walk iff every maximal run of removed darts (cyclically)
   is a sub-walk from a vertex back to itself.  The shared vertex is then automatic: the first dart
   of a run starts where the next kept dart starts.
4. *Existence.*  At a vertex visited `k` times the rotation reads
   `o_1 S_1 ī_1 T_1 … o_k S_k ī_k T_k` and a passage is `ī_a → o_{π a}`; the rose hypotheses say
   every passage with `π a ≠ a` is crossed, which excludes `π a = a + 1`.  With `¬Unpinched` some vertex
   has `k ≥ 2`; with `¬FirstTurns` some passage has `π a ≠ a`.  Euler's formula for the planar map gives
   `repeatedVisits = #regions - 2`, so a region other than `E`, `L_s` and the region of the kept
   cell exists, and the claim is that some region-union move satisfies 1–3.  Neither "fill all
   lakes" nor "one lobe" suffices on its own (see the two-hole example in `P10Rose/InPlace`), and
   straddled lakes can force `Ns` and `Fs` to be chosen together.

The claim is supported by an exhaustive search over rotation systems of the walk graph with at most
six walk darts and at most four visits per vertex, with genus `0` and the rose hypotheses
(1 219 350 configurations, arcs of every admissible position and length): a region-union move
satisfying 1–3 exists in every case.  The planarity argument for arbitrary length (non-interleaving
of regions around a vertex, forcing some region to meet the walk in closed runs) is not formalised.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides

section InPlaceFilter

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **Filtering the boundary cycle** by a predicate true on both arcs filters the two sides and
keeps the arcs. -/
theorem filter_cycle_eq (K : PocketFaceSet D eps X lo hi) (p : X.toCombMap.Dart → Bool)
    (ht₁ : ∀ d ∈ invDarts X K.sourceArc.darts, p d = true)
    (ht₂ : ∀ d ∈ K.targetArc.darts, p d = true) :
    K.boundary.cycle.filter p = K.firstSide.filter p ++ invDarts X K.sourceArc.darts ++
      K.secondSide.filter p ++ K.targetArc.darts := by
  rw [K.decomposition, List.filter_append, List.filter_append, List.filter_append,
    List.filter_eq_self.mpr ht₁, List.filter_eq_self.mpr ht₂]

/-- **The step from a filtered cycle.**  A face set away from the exterior face and the source
cell, containing a relator cell, whose boundary darts are the darts of the old cycle kept by a
predicate true on both arcs, gives a step when the kept darts form a closed walk and some kept dart
shares its vertex with a removed one. -/
theorem step_of_filter (K : PocketFaceSet D eps X lo hi)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (hsrc : K.sourceArc.length < (cellDarts X K.source).length)
    (htgt : K.targetArc.length < (outerDarts X).length)
    {faces : Finset X.toCombMap.Face} (hout : X.outerFace ∉ faces)
    (hsource : (cell X K.source).face ∉ faces) {kept : Fin X.rCellCount}
    (hkept : (cell X kept).face ∈ faces) (p : X.toCombMap.Dart → Bool)
    (hbd : ∀ d, IsBoundaryDart X.toCombMap faces d ↔ d ∈ K.boundary.cycle ∧ p d = true)
    (ht₁ : ∀ d ∈ invDarts X K.sourceArc.darts, p d = true)
    (ht₂ : ∀ d ∈ K.targetArc.darts, p d = true)
    (hwalk : IsClosedDartWalk X.toCombMap (K.boundary.cycle.filter p))
    {x y : X.toCombMap.Dart} (hx : x ∈ K.boundary.cycle) (hpx : p x = true)
    (hy : y ∈ K.boundary.cycle) (hpy : p y = false)
    (hxy : X.toCombMap.vertexOf x = X.toCombMap.vertexOf y) :
    ∃ K' : PocketFaceSet D eps X lo hi, K'.ClosedWalk ∧
      K'.sourceArc.length < (cellDarts X K'.source).length ∧
      K'.targetArc.length < (outerDarts X).length ∧ K'.repeatedVisits < K.repeatedVisits := by
  have hfilt := filter_cycle_eq K p ht₁ ht₂
  have hwalk' : IsClosedDartWalk X.toCombMap (K.firstSide.filter p ++
      invDarts X K.sourceArc.darts ++ K.secondSide.filter p ++ K.targetArc.darts) := by
    rw [← hfilt]
    exact hwalk
  have hmem : ∀ d, d ∈ K.firstSide.filter p ++ invDarts X K.sourceArc.darts ++
      K.secondSide.filter p ++ K.targetArc.darts ↔ IsBoundaryDart X.toCombMap faces d := by
    intro d
    rw [← hfilt, List.mem_filter, hbd]
  have hperm : List.Perm K.boundary.cycle ((K.firstSide.filter p ++
      invDarts X K.sourceArc.darts ++ K.secondSide.filter p ++ K.targetArc.darts) ++
      K.boundary.cycle.filter (fun d => !p d)) := by
    rw [← hfilt]
    exact (List.filter_append_perm p K.boundary.cycle).symm
  have hx' : x ∈ K.firstSide.filter p ++ invDarts X K.sourceArc.darts ++
      K.secondSide.filter p ++ K.targetArc.darts := by
    rw [← hfilt]
    exact List.mem_filter.mpr ⟨hx, hpx⟩
  have hy' : y ∈ K.boundary.cycle.filter (fun d => !p d) :=
    List.mem_filter.mpr ⟨hy, by simp [hpy]⟩
  exact step_of_faces K hlabel hout hsource hkept hmem
    ((List.length_filter_le p _).trans K.firstSide_length_le)
    ((List.length_filter_le p _).trans K.secondSide_length_le) K.lo_le K.le_hi hsrc htgt hwalk'
    hperm hx' hy' hxy

end InPlaceFilter

/-- **The rose step by filtering** (the isolated remaining claim of `P10Rose`).  Under the
hypotheses of `RoseInPlaceStepStatement`, some face set `F'` away from the exterior face and the
source cell, containing a relator cell, has as boundary darts exactly the darts of the old cycle
kept by a predicate `p` that keeps both arcs; the kept darts, in the order of the old cycle, form a
closed walk, and some kept dart shares its vertex with a removed one.  The intended witness is a
region-union move `F' = (F \ Fs) ∪ Ns` (module docstring).

**FALSE; do not use as a gap.**  Counterexample (three-petal flower): vertices `w, a₁, a₂, a₃`;
petals `P_j = {p_j, q_j}` (`p_j : w → a_j`, `q_j : a_j → w`), source cell `S = {q̄₃, r}`
(`r : a₃ → w`), rotation at `w` equal to `(q̄₁ p₁ q̄₂ p₂ r̄ q̄₃ p₃)`; `G = Multiplicative ℤ`, relator
cells `P₁` and `S` labelled `[g, g]`, `F = {P₁, P₂, P₃}` with kept cell `P₁` and cycle
`[p₃] ++ [q₃] ++ [p₁, q₁, p₂] ++ [q₂]`.  Keeping `q₂` and `q₃` forces `P₂, P₃ ∈ F'`, so `F' = F` and
no dart is removed.  The open gap of `P10Rose` is `RoseInPlaceStepStatement` (which this example
does not refute: `F' = {P₁, P₃}` with `t₂` dropped). -/
def RoseFilterStepStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ (faces : Finset X.toCombMap.Face) (kept : Fin X.rCellCount)
          (p : X.toCombMap.Dart → Bool),
          X.outerFace ∉ faces ∧ (cell X K.source).face ∉ faces ∧ (cell X kept).face ∈ faces ∧
          (∀ d, IsBoundaryDart X.toCombMap faces d ↔ d ∈ K.boundary.cycle ∧ p d = true) ∧
          (∀ d ∈ invDarts X K.sourceArc.darts, p d = true) ∧
          (∀ d ∈ K.targetArc.darts, p d = true) ∧
          IsClosedDartWalk X.toCombMap (K.boundary.cycle.filter p) ∧
          ∃ x ∈ K.boundary.cycle, ∃ y ∈ K.boundary.cycle, p x = true ∧ p y = false ∧
            X.toCombMap.vertexOf x = X.toCombMap.vertexOf y

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.filter_cycle_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.step_of_filter
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.RoseFilterStepStatement
