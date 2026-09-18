import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindSix
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhi
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: the passing predicate, and the source and target arcs

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-66.

Route.  `gfaceWindSix_Choice K` asks for a nonempty excision sequence (`TransGen` of
`gfaceWind_Step`) from the start state `(∂K, 1_K)` to a state `(c, g)` satisfying a list of
clauses.  This file names that list and discharges part of it from the arcs of `K`.

* `gfaceWindNine_Pass K c g` (definition): the clauses of `gfaceWindSix_Choice` after the
  sequence, literally; `gfaceWindNine_choice_iff` (proved, `Iff.rfl`).
* `gfaceWindNine_PStep` (definition): a step whose new face function is `≥ 0`;
  `gfaceWindNine_Reach K`: a passing state reached along a nonempty `PStep` path;
  `gfaceWindNine_choice_of_reach`, `gfaceWindNine_reach_of_head` (proved).
* `gfaceWindNine_pass_of_facts` (proved): at a `0/1` cobounded state `(c, g)` whose walk
  contains the inverse source arc and the target arc, clauses 8 and 9 hold (the filters are the
  whole arcs) and, when the source arc is nonempty, clause 4 holds (the source face is across a
  dart of `c`).
* `gfaceWindNine_pass_start` (proved): **LOUD, the start state itself passes.**  So the
  reachability must be along a NONEMPTY path; `gfaceWindNine_refl_trivial` (proved) shows the
  `ReflTransGen` form is trivially true, hence useless.  Only `F' ≠ K`, which the `TransGen`
  gives through the length decrease, separates a choice from the start.

## Truth check

Scratchpad `gl-p10-66/nine.py` (models of `gl-p10-49/gface.py`, `gl-p10-55/wind.py`,
`gl-p10-61/six.py`): the start state satisfies every clause except `F' ≠ K` in all no-loop
cases (13616, 19540, 5861 with kept `F' ≠ ∅`; 11334, 23376, 9201 with one kept cell), and the
arc discharge of clauses 4, 8, 9 has 0 failures on every reached `0/1` state containing both arcs.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

/-- **A sign-keeping step**: a step of `gfaceWind_Step` whose new face function is `≥ 0`. -/
def gfaceWindNine_PStep (M : CombMap.{v}) (o : M.Face) (s t : List M.Dart × (M.Face → ℤ)) :
    Prop :=
  gfaceWind_Step M o s t ∧ ∀ f, 0 ≤ t.2 f

/-- A sign-keeping sequence is an excision sequence. -/
theorem gfaceWindNine_mono {M : CombMap.{v}} {o : M.Face} {s t : List M.Dart × (M.Face → ℤ)}
    (h : Relation.TransGen (gfaceWindNine_PStep M o) s t) :
    Relation.TransGen (gfaceWind_Step M o) s t := by
  induction h with
  | single hst => exact Relation.TransGen.single hst.1
  | tail _ hst ih => exact ih.tail hst.1

/-- **Boundary darts of a `0/1` state are its walk darts.** -/
theorem gfaceWindNine_bd {M : CombMap.{v}} {c : List M.Dart} {g : M.Face → ℤ}
    (hcob : ∀ d, g (M.faceOf d) - g (M.faceOf (M.alpha d)) =
      gfaceWind_lind c d - gfaceWind_lind c (M.alpha d))
    (h01 : ∀ f, g f = 0 ∨ g f = 1) (hne : ∀ x, x ∈ c → M.alpha x ∉ c) (x : M.Dart) :
    extremalGFaceProve_bd M (gfaceWind_faces g) x = true ↔ x ∈ c := by
  rw [extremalGFaceProve_bd_eq_true_iff, gfaceWind_mem_faces, gfaceWind_mem_faces]
  exact gfaceWind_bd_iff (hcob x) (h01 _) (h01 _) (hne x)

section Nine

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **Clause 4 of a winding choice** (region form). -/
def gfaceWindNine_C4 (K : PocketFaceSet D eps X lo hi) (c : List X.toCombMap.Dart)
    (g : X.toCombMap.Face → ℤ) : Prop :=
  (∃ f, (f = X.outerFace ∨ ∃ x ∈ c, X.toCombMap.faceOf (X.toCombMap.alpha x) = f) ∧
      Relation.ReflTransGen (gfaceWindClause_Adj X.toCombMap c) f (cell X K.source).face) ∨
    (cell X K.source).face ∉ gfaceWind_faces g

/-- **Clause 5 of a winding choice** (region form). -/
def gfaceWindNine_C5 (_K : PocketFaceSet D eps X lo hi) (c : List X.toCombMap.Dart)
    (g : X.toCombMap.Face → ℤ) : Prop :=
  (∃ x ∈ c, ∃ kept : Fin X.rCellCount,
      Relation.ReflTransGen (gfaceWindClause_Adj X.toCombMap c) (X.toCombMap.faceOf x)
        (cell X kept).face) ∨
    ∃ kept : Fin X.rCellCount, (cell X kept).face ∈ gfaceWind_faces g

/-- **The passing predicate**: the clauses of `gfaceWindSix_Choice K` at the reached state
`(c, g)`, literally (`0/1` or vertex-simple `g ≥ 0`; clauses 4, 5, 8, 9). -/
def gfaceWindNine_Pass (K : PocketFaceSet D eps X lo hi) (c : List X.toCombMap.Dart)
    (g : X.toCombMap.Face → ℤ) : Prop :=
  ((∀ f, g f = 0 ∨ g f = 1) ∨ ((c.map X.toCombMap.vertexOf).Nodup ∧ ∀ f, 0 ≤ g f)) ∧
    ((∃ f, (f = X.outerFace ∨ ∃ x ∈ c, X.toCombMap.faceOf (X.toCombMap.alpha x) = f) ∧
        Relation.ReflTransGen (gfaceWindClause_Adj X.toCombMap c) f (cell X K.source).face) ∨
      (cell X K.source).face ∉ gfaceWind_faces g) ∧
    ((∃ x ∈ c, ∃ kept : Fin X.rCellCount,
        Relation.ReflTransGen (gfaceWindClause_Adj X.toCombMap c) (X.toCombMap.faceOf x)
          (cell X kept).face) ∨
      ∃ kept : Fin X.rCellCount, (cell X kept).face ∈ gfaceWind_faces g) ∧
    (gfaceWindClause_SrcGap K ∨
      ∃ pre mid post : List X.toCombMap.Dart, K.sourceArc.darts = pre ++ mid ++ post ∧
        K.sourceArc.darts.filter (fun d =>
          extremalGFaceProve_bd X.toCombMap (gfaceWind_faces g) (X.toCombMap.alpha d)) = mid) ∧
    (gfaceWindClause_TgtGap K ∨
      ∃ pre mid post : List X.toCombMap.Dart, K.targetArc.darts = pre ++ mid ++ post ∧
        K.targetArc.darts.filter (extremalGFaceProve_bd X.toCombMap (gfaceWind_faces g)) = mid)

/-- **`gfaceWindSix_Choice` is a passing state reached by a nonempty excision sequence.** -/
theorem gfaceWindNine_choice_iff (K : PocketFaceSet D eps X lo hi) :
    gfaceWindSix_Choice K ↔ ∃ (c : List X.toCombMap.Dart) (g : X.toCombMap.Face → ℤ),
      Relation.TransGen (gfaceWind_Step X.toCombMap X.outerFace)
        (K.boundary.cycle, gfaceWind_ind K.faces) (c, g) ∧ gfaceWindNine_Pass K c g :=
  Iff.rfl

/-- **A passing state reached along a nonempty sign-keeping path.** -/
def gfaceWindNine_Reach (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∃ (c : List X.toCombMap.Dart) (g : X.toCombMap.Face → ℤ),
    Relation.TransGen (gfaceWindNine_PStep X.toCombMap X.outerFace)
      (K.boundary.cycle, gfaceWind_ind K.faces) (c, g) ∧ gfaceWindNine_Pass K c g

/-- **The winding choice from a sign-keeping reach.** -/
theorem gfaceWindNine_choice_of_reach (K : PocketFaceSet D eps X lo hi)
    (h : gfaceWindNine_Reach K) : gfaceWindSix_Choice K := by
  obtain ⟨c, g, hr, hp⟩ := h
  exact (gfaceWindNine_choice_iff K).mpr ⟨c, g, gfaceWindNine_mono hr, hp⟩

/-- **A first sign-keeping step followed by a possibly empty sign-keeping path.** -/
theorem gfaceWindNine_reach_of_head (K : PocketFaceSet D eps X lo hi)
    {t : List X.toCombMap.Dart × (X.toCombMap.Face → ℤ)} {c : List X.toCombMap.Dart}
    {g : X.toCombMap.Face → ℤ}
    (h1 : gfaceWindNine_PStep X.toCombMap X.outerFace (K.boundary.cycle, gfaceWind_ind K.faces) t)
    (h2 : Relation.ReflTransGen (gfaceWindNine_PStep X.toCombMap X.outerFace) t (c, g))
    (hp : gfaceWindNine_Pass K c g) : gfaceWindNine_Reach K :=
  ⟨c, g, Relation.TransGen.head' h1 h2, hp⟩

/-- A dart of the source arc has its reverse on the inverse source arc. -/
theorem gfaceWindNine_mem_src (K : PocketFaceSet D eps X lo hi) {d : X.toCombMap.Dart}
    (hd : d ∈ K.sourceArc.darts) : X.toCombMap.alpha d ∈ invDarts X K.sourceArc.darts := by
  show X.toCombMap.alpha d ∈ K.sourceArc.darts.reverse.map X.toCombMap.alpha
  exact List.mem_map.mpr ⟨d, List.mem_reverse.mpr hd, rfl⟩

/-- **Clauses 8 and 9 from the arcs**: when the walk of a `0/1` state contains the inverse
source arc and the target arc, both filters are the whole arcs. -/
theorem gfaceWindNine_arcs (K : PocketFaceSet D eps X lo hi) {c : List X.toCombMap.Dart}
    {g : X.toCombMap.Face → ℤ}
    (hbd : ∀ x, extremalGFaceProve_bd X.toCombMap (gfaceWind_faces g) x = true ↔ x ∈ c)
    (hs : ∀ d ∈ invDarts X K.sourceArc.darts, d ∈ c) (ht : ∀ d ∈ K.targetArc.darts, d ∈ c) :
    (gfaceWindClause_SrcGap K ∨
      ∃ pre mid post : List X.toCombMap.Dart, K.sourceArc.darts = pre ++ mid ++ post ∧
        K.sourceArc.darts.filter (fun d =>
          extremalGFaceProve_bd X.toCombMap (gfaceWind_faces g) (X.toCombMap.alpha d)) = mid) ∧
    (gfaceWindClause_TgtGap K ∨
      ∃ pre mid post : List X.toCombMap.Dart, K.targetArc.darts = pre ++ mid ++ post ∧
        K.targetArc.darts.filter
          (extremalGFaceProve_bd X.toCombMap (gfaceWind_faces g)) = mid) := by
  refine ⟨Or.inr ⟨[], K.sourceArc.darts, [], by simp, ?_⟩,
    Or.inr ⟨[], K.targetArc.darts, [], by simp, ?_⟩⟩
  · exact List.filter_eq_self.mpr fun d hd =>
      (hbd (X.toCombMap.alpha d)).mpr (hs _ (gfaceWindNine_mem_src K hd))
  · exact List.filter_eq_self.mpr fun d hd => (hbd d).mpr (ht d hd)

/-- **Passing from the arcs**: a `0/1` cobounded state whose walk contains the inverse source
arc and the target arc passes, given clause 5 and, for an empty source arc, clause 4. -/
theorem gfaceWindNine_pass_of_facts (K : PocketFaceSet D eps X lo hi)
    {c : List X.toCombMap.Dart} {g : X.toCombMap.Face → ℤ}
    (hcob : ∀ d, g (X.toCombMap.faceOf d) - g (X.toCombMap.faceOf (X.toCombMap.alpha d)) =
      gfaceWind_lind c d - gfaceWind_lind c (X.toCombMap.alpha d))
    (h01 : ∀ f, g f = 0 ∨ g f = 1) (hne : ∀ x, x ∈ c → X.toCombMap.alpha x ∉ c)
    (hs : ∀ d ∈ invDarts X K.sourceArc.darts, d ∈ c) (ht : ∀ d ∈ K.targetArc.darts, d ∈ c)
    (h4 : K.sourceArc.darts ≠ [] ∨ gfaceWindNine_C4 K c g) (h5 : gfaceWindNine_C5 K c g) :
    gfaceWindNine_Pass K c g := by
  obtain ⟨h8, h9⟩ := gfaceWindNine_arcs K (gfaceWindNine_bd hcob h01 hne) hs ht
  refine ⟨Or.inl h01, ?_, h5, h8, h9⟩
  rcases h4 with h4 | h4
  · obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ h4
    refine Or.inl ⟨(cell X K.source).face,
      Or.inr ⟨X.toCombMap.alpha d, hs _ (gfaceWindNine_mem_src K hd), ?_⟩,
      Relation.ReflTransGen.refl⟩
    rw [X.toCombMap.alpha_involutive d]
    exact faceOf_of_mem_cellDarts (K.sourceArc.mem_cycle_of_mem_darts hd)
  · exact h4

/-- **LOUD: the start state passes.**  The pocket face set itself satisfies every clause of a
winding choice; only `F' ≠ K` (from a nonempty sequence) excludes it. -/
theorem gfaceWindNine_pass_start (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk) :
    gfaceWindNine_Pass K K.boundary.cycle (gfaceWind_ind K.faces) := by
  have hc := K.boundary.cycle_mem_iff
  have h0 : gfaceWind_Inv X.toCombMap K.boundary.cycle X.outerFace K.boundary.cycle
      (gfaceWind_ind K.faces) :=
    gfaceWind_inv_start (fun d => (hc d).symm) hK.1 K.outerFace_not_mem
  obtain ⟨-, -, hcob, -⟩ := h0
  have hne : ∀ x, x ∈ K.boundary.cycle → X.toCombMap.alpha x ∉ K.boundary.cycle :=
    fun x hx hax => ((hc x).mp hx).2 ((hc _).mp hax).1
  refine gfaceWindNine_pass_of_facts K hcob (gfaceWindSix_ind01 K.faces) hne ?_ ?_
    (Or.inr (Or.inr ?_)) (Or.inr ⟨K.kept, ?_⟩)
  · intro d hd
    rw [K.decomposition]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hd))
  · intro d hd
    rw [K.decomposition]
    exact List.mem_append_right _ hd
  · rw [gfaceWind_mem_faces, gfaceWind_ind_neg K.source_not_mem]
    norm_num
  · rw [gfaceWind_mem_faces]
    exact gfaceWind_ind_pos K.kept_mem

/-- **LOUD: the reflexive form is trivial**: a passing state is reached along a possibly empty
sign-keeping path, namely the start.  The reachability residual must be nonempty. -/
theorem gfaceWindNine_refl_trivial (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk) :
    ∃ (c : List X.toCombMap.Dart) (g : X.toCombMap.Face → ℤ),
      Relation.ReflTransGen (gfaceWindNine_PStep X.toCombMap X.outerFace)
        (K.boundary.cycle, gfaceWind_ind K.faces) (c, g) ∧ gfaceWindNine_Pass K c g :=
  ⟨_, _, Relation.ReflTransGen.refl, gfaceWindNine_pass_start K hK⟩

end Nine

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindNine_PStep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindNine_mono
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindNine_bd
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindNine_C4
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindNine_C5
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindNine_Pass
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindNine_choice_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindNine_Reach
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindNine_choice_of_reach
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindNine_reach_of_head
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindNine_mem_src
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindNine_arcs
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindNine_pass_of_facts
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindNine_pass_start
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindNine_refl_trivial
