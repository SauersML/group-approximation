import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ValueFailures.Window
import GroupApproximation.GGT.VanKampen.ClosedWalkFirstTurnEnclosure
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSubdiagramSuccAssembly
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionSimpleWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# The lobe of a value failure dart

For a value failure dart `e` (`IsValueFailure`), the gap `gap X e` of outer darts strictly between
`e` and `facePerm e` reverses to a closed walk `walk X e` in the interior side: its successive
darts are face steps, and it closes up at `e` by a first turn past `alpha e` and `facePerm e`.
The faces it encloses are the lobe `lobe X e`.

* `enclosedFaceSetSucc_lobe`: the lobe is an enclosed face set over the walk.
* `exists_cell_mem_lobe`: the lobe holds a relator cell, since the walk reads a nontrivial value.
* `faceOf_mem_lobe_of_mem_gap`, `mem_gap_of_faceOf_mem_lobe`: the outer darts off the outer face
  whose face is in the lobe are exactly the gap darts off the outer face.
* `lobe_disjoint`: the lobes of two value failures with disjoint gaps are disjoint.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ValueFailures

open Equiv GroupApproximation.GGT.VanKampen.Embedded SimpleClosedWalkSides FirstTurnEnclosure
open scoped Classical

universe u w v

/-- Three rotation steps from the reversal, past two darts off the edges of `c`, are a first
turn. -/
theorem firstTurn_three {M : CombMap.{v}} {c : List M.Dart} {x y z₁ z₂ : M.Dart}
    (h₁ : M.sigma (M.alpha x) = z₁) (h₂ : M.sigma z₁ = z₂) (h₃ : M.sigma z₂ = y)
    (hz₁ : ¬ walkKeep M c z₁) (hz₂ : ¬ walkKeep M c z₂) : FirstTurn M c x y := by
  refine ⟨2 + 1, by omega, ?_, fun t ht htk => ?_⟩
  · rw [pow_succ, Perm.mul_apply, pow_two, Perm.mul_apply, h₁, h₂, h₃]
  · obtain rfl | rfl : t = 1 ∨ t = 2 := by omega
    · rw [pow_one, h₁]
      exact hz₁
    · rw [pow_two, Perm.mul_apply, h₁, h₂]
      exact hz₂

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **The walk of a gap**: the reversed gap, read by reversals of its darts. -/
noncomputable def walk (X : DiscDiagram.{u, w, v} W) (e : X.toCombMap.Dart) :
    List X.toCombMap.Dart :=
  (gap X e).reverse.map X.toCombMap.alpha

/-- **The lobe of a dart**: the faces enclosed by the walk of its gap. -/
noncomputable abbrev lobe (X : DiscDiagram.{u, w, v} W) (e : X.toCombMap.Dart) :
    Finset X.toCombMap.Face :=
  enclosedFaces X.toCombMap (walk X e)

theorem mem_walk_iff (X : DiscDiagram.{u, w, v} W) (e d : X.toCombMap.Dart) :
    d ∈ walk X e ↔ X.toCombMap.alpha d ∈ gap X e := by
  unfold walk
  exact FirstTurnWalk.mem_reverse_map_alpha_iff

theorem walkKeep_iff (X : DiscDiagram.{u, w, v} W) (e d : X.toCombMap.Dart) :
    walkKeep X.toCombMap (walk X e) d ↔ X.toCombMap.alpha d ∈ gap X e ∨ d ∈ gap X e := by
  show d ∈ walk X e ∨ X.toCombMap.alpha d ∈ walk X e ↔ _
  rw [mem_walk_iff X e d, mem_walk_iff X e (X.toCombMap.alpha d),
    X.toCombMap.alpha_involutive d]

theorem not_walkKeep (X : DiscDiagram.{u, w, v} W) {e d : X.toCombMap.Dart}
    (hd : d ∉ gap X e) (hface : X.toCombMap.faceOf d ≠ X.outerFace) :
    ¬ walkKeep X.toCombMap (walk X e) d := by
  rw [walkKeep_iff]
  rintro (h | h)
  · have h' := faceOf_alpha_of_mem_gap X h
    rw [X.toCombMap.alpha_involutive d] at h'
    exact hface h'
  · exact hd h

theorem not_walkKeep_of_faces (X : DiscDiagram.{u, w, v} W) (e : X.toCombMap.Dart)
    {z : X.toCombMap.Dart} (hz : X.toCombMap.faceOf z ≠ X.outerFace)
    (hαz : X.toCombMap.faceOf (X.toCombMap.alpha z) ≠ X.outerFace) :
    ¬ walkKeep X.toCombMap (walk X e) z :=
  not_walkKeep X (e := e) (fun h => hαz (faceOf_alpha_of_mem_gap X h)) hz

theorem faceOf_of_mem_walk (X : DiscDiagram.{u, w, v} W) {e d : X.toCombMap.Dart}
    (hd : d ∈ walk X e) : X.toCombMap.faceOf d = X.outerFace := by
  have h := faceOf_alpha_of_mem_gap X ((mem_walk_iff X e d).mp hd)
  rwa [X.toCombMap.alpha_involutive d] at h

theorem walk_ne_nil (X : DiscDiagram.{u, w, v} W) {e : X.toCombMap.Dart}
    (hval : RelLetter.listVal (dartWord X (gap X e)) ≠ 1) : walk X e ≠ [] := by
  intro h
  rw [walk, List.map_eq_nil_iff, List.reverse_eq_nil_iff] at h
  exact gap_ne_nil X hval h

theorem walk_nodup (X : DiscDiagram.{u, w, v} W) (e : X.toCombMap.Dart) : (walk X e).Nodup := by
  unfold walk
  refine List.Nodup.map X.toCombMap.alpha_involutive.injective (List.nodup_reverse.mpr ?_)
  rw [gap_eq]
  exact (outerDarts_nodup X).sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))

theorem walk_isChain (X : DiscDiagram.{u, w, v} W) (e : X.toCombMap.Dart) :
    (walk X e).IsChain fun d d' => X.toCombMap.facePerm d = d' := by
  unfold walk
  rw [List.isChain_map, List.isChain_reverse, gap_eq]
  exact ((outerDarts_isChain X).drop _).take _

theorem walk_getLast (X : DiscDiagram.{u, w, v} W) {e : X.toCombMap.Dart}
    (hG : IsValueFailure X e) {x₁ : X.toCombMap.Dart}
    (hx₁ : (outerDarts X)[idx X e + 1]? = some x₁) :
    (walk X e).getLast (walk_ne_nil X hG.2.2.2.1) = X.toCombMap.alpha x₁ := by
  have hab := idx_add_one_lt X hG.2.2.2.1
  rw [List.getLast_eq_iff_getLast?_eq_some, walk, List.getLast?_map, List.getLast?_reverse,
    List.head?_eq_getElem?, gap_getElem? X e 0 (by omega), Nat.add_zero, hx₁, Option.map_some]

theorem walk_head (X : DiscDiagram.{u, w, v} W) {e : X.toCombMap.Dart}
    (hG : IsValueFailure X e) {x₂ : X.toCombMap.Dart}
    (hx₂ : (outerDarts X)[idx X (X.toCombMap.facePerm e) - 1]? = some x₂) :
    (walk X e).head (walk_ne_nil X hG.2.2.2.1) = X.toCombMap.alpha x₂ := by
  have hab := idx_add_one_lt X hG.2.2.2.1
  have hb := idx_lt_length X hG.2.1
  have hidx : idx X e + 1 + (idx X (X.toCombMap.facePerm e) - (idx X e + 1) - 1) =
      idx X (X.toCombMap.facePerm e) - 1 := by omega
  rw [List.head_eq_iff_head?_eq_some, walk, List.head?_map, List.head?_reverse,
    List.getLast?_eq_getElem?, gap_length X e hb.le,
    gap_getElem? X e (idx X (X.toCombMap.facePerm e) - (idx X e + 1) - 1) (by omega), hidx, hx₂,
    Option.map_some]

/-- **The walk closes up at `e`**: from the reversal of its last dart, rotating past `alpha e` and
`facePerm e` reaches its first dart. -/
theorem firstTurn_close (X : DiscDiagram.{u, w, v} W) {e : X.toCombMap.Dart}
    (hG : IsValueFailure X e) :
    FirstTurn X.toCombMap (walk X e) ((walk X e).getLast (walk_ne_nil X hG.2.2.2.1))
      ((walk X e).head (walk_ne_nil X hG.2.2.2.1)) := by
  have hab := idx_add_one_lt X hG.2.2.2.1
  have hb := idx_lt_length X hG.2.1
  obtain ⟨x₁, hx₁⟩ : ∃ x, (outerDarts X)[idx X e + 1]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨x₂, hx₂⟩ : ∃ x, (outerDarts X)[idx X (X.toCombMap.facePerm e) - 1]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  rw [walk_getLast X hG hx₁, walk_head X hG hx₂]
  have he := getElem?_idx X hG.1
  have hstep : (outerDarts X)[idx X (X.toCombMap.facePerm e) - 1 + 1]? =
      some (X.toCombMap.facePerm e) := by
    rw [show idx X (X.toCombMap.facePerm e) - 1 + 1 = idx X (X.toCombMap.facePerm e) by omega]
    exact getElem?_idx X hG.2.1
  refine firstTurn_three (z₁ := X.toCombMap.alpha e) (z₂ := X.toCombMap.facePerm e) ?_ rfl ?_ ?_ ?_
  · rw [X.toCombMap.alpha_involutive x₁, ← facePerm_alpha X x₁]
    exact outerDarts_step X he hx₁
  · rw [← facePerm_alpha X]
    exact outerDarts_step X hx₂ hstep
  · intro h
    exact not_walkKeep X (e := e) (d := e)
      (fun hm => lt_irrefl _ ((mem_gap_iff X e e).mp hm).2.1) hG.2.2.1
      ((walkKeep_alpha _ _ e).mp h)
  · refine not_walkKeep X (e := e) (d := X.toCombMap.facePerm e)
      (fun hm => lt_irrefl _ ((mem_gap_iff X e _).mp hm).2.2) ?_
    rw [X.toCombMap.faceOf_facePerm]
    exact hG.2.2.1

theorem walk_firstTurnChain (X : DiscDiagram.{u, w, v} W) (e : X.toCombMap.Dart) :
    (walk X e).IsChain (FirstTurn X.toCombMap (walk X e)) :=
  (walk_isChain X e).imp fun _ _ h => FirstTurn.of_facePerm h

theorem walk_vertexChain (X : DiscDiagram.{u, w, v} W) (e : X.toCombMap.Dart) :
    (walk X e).IsChain fun d d' =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf d' :=
  (walk_firstTurnChain X e).imp fun _ _ h => h.vertexOf_eq

theorem turnMem_walk (X : DiscDiagram.{u, w, v} W) {e : X.toCombMap.Dart}
    (hG : IsValueFailure X e) : TurnMem X.toCombMap (walk X e) :=
  turnMem_of_firstTurn (walk_ne_nil X hG.2.2.2.1) (walk_firstTurnChain X e) (firstTurn_close X hG)

theorem outer_not_mem_lobe (X : DiscDiagram.{u, w, v} W) {e : X.toCombMap.Dart}
    (hG : IsValueFailure X e) : X.outerFace ∉ lobe X e := by
  obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ (gap_ne_nil X hG.2.2.2.1)
  have hmem : X.toCombMap.alpha y ∈ walk X e := by
    rw [mem_walk_iff, X.toCombMap.alpha_involutive y]
    exact hy
  have h := faceOf_not_mem_enclosedFaces X.planar (walk_ne_nil X hG.2.2.2.1)
    (walk_vertexChain X e) (turnMem_walk X hG) hmem
  rwa [faceOf_alpha_of_mem_gap X hy] at h

/-- **The lobe is an enclosed face set** over the walk of the gap. -/
theorem enclosedFaceSetSucc_lobe (X : DiscDiagram.{u, w, v} W) {e : X.toCombMap.Dart}
    (hG : IsValueFailure X e) : EnclosedFaceSetSucc X (lobe X e) (walk X e) := by
  have hc := walk_ne_nil X hG.2.2.2.1
  have hfchain := walk_firstTurnChain X e
  have hclose := firstTurn_close X hG
  have hchain := walk_vertexChain X e
  have hturn := turnMem_walk X hG
  exact
    { outerFace_not_mem := outer_not_mem_lobe X hG
      ne_nil := hc
      nodup := walk_nodup X e
      chain := hchain
      closes := hclose.vertexOf_eq
      mem_iff := mem_iff_enclosedFaces X.planar hc hchain hturn
      turn_mem := hturn
      turn_next := fun _ hi _ hm hkeep hfirst =>
        eq_of_firstTurn (firstTurn_getElem_succ hc hfchain hclose hi (Nat.mod_lt _ (by omega)))
          (List.getElem_mem _) hm hkeep hfirst }

/-- **The lobe holds a relator cell**: otherwise the enclosed subdiagram has no relator cells and
reads the value `1` along the gap. -/
theorem exists_cell_mem_lobe (X : DiscDiagram.{u, w, v} W) {e : X.toCombMap.Dart}
    (hG : IsValueFailure X e) : ∃ C ∈ X.relatorCells, C.face ∈ lobe X e := by
  by_contra hno
  obtain ⟨Xi, hbw, hcount, -⟩ :=
    closedWalkEnclosedSubdiagramSucc X (lobe X e) (walk X e) (enclosedFaceSetSucc_lobe X hG)
  have hle : Xi.rCellCount ≤ 0 := by
    refine hcount.trans (le_of_eq (List.length_eq_zero_iff.mpr (List.filter_eq_nil_iff.mpr ?_)))
    intro C hC h
    simp only [decide_eq_true_eq] at h
    exact hno ⟨C, hC, h⟩
  have h1 := DiscDiagram.boundaryValue_eq_one_of_no_rCells Xi
    (List.length_eq_zero_iff.mp (Nat.le_zero.mp hle))
  rw [DiscDiagram.boundaryValue, hbw, walk, PocketRegion.invDarts_reverse_map_alpha] at h1
  exact hG.2.2.2.1 h1

theorem faceOf_mem_lobe_of_mem_gap (X : DiscDiagram.{u, w, v} W) {e y : X.toCombMap.Dart}
    (hy : y ∈ gap X e) (hface : X.toCombMap.faceOf y ≠ X.outerFace) :
    X.toCombMap.faceOf y ∈ lobe X e := by
  refine (mem_enclosedFaces_iff X.toCombMap (walk X e) y).mpr
    ⟨X.toCombMap.alpha y, ?_, ?_, ?_⟩
  · rw [mem_walk_iff, X.toCombMap.alpha_involutive y]
    exact hy
  · rw [X.toCombMap.alpha_involutive y, mem_walk_iff]
    intro h
    have h' := faceOf_alpha_of_mem_gap X h
    rw [X.toCombMap.alpha_involutive y] at h'
    exact hface h'
  · rw [X.toCombMap.alpha_involutive y]
    exact .refl _

theorem mem_gap_of_faceOf_mem_lobe (X : DiscDiagram.{u, w, v} W) {e y : X.toCombMap.Dart}
    (hG : IsValueFailure X e) (hy : X.toCombMap.faceOf y ∈ lobe X e)
    (hB : y ∈ outerDarts X) (hface : X.toCombMap.faceOf y ≠ X.outerFace) : y ∈ gap X e := by
  by_contra hno
  have h := faceOf_alpha_mem_enclosedFaces (not_walkKeep X hno hface) hy
  rw [(mem_outerDarts_iff X y).mp hB] at h
  exact outer_not_mem_lobe X hG h

theorem facePerm_mem_gap (X : DiscDiagram.{u, w, v} W) {e e₂ : X.toCombMap.Dart}
    (hG : IsValueFailure X e) (hG₂ : IsValueFailure X e₂) (he₂ : e₂ ∈ gap X e) :
    X.toCombMap.facePerm e₂ ∈ gap X e := by
  have hface : X.toCombMap.faceOf (X.toCombMap.facePerm e₂) ≠ X.outerFace := by
    rw [X.toCombMap.faceOf_facePerm]
    exact hG₂.2.2.1
  refine mem_gap_of_faceOf_mem_lobe X hG ?_ hG₂.2.1 hface
  rw [X.toCombMap.faceOf_facePerm]
  exact faceOf_mem_lobe_of_mem_gap X he₂ hG₂.2.2.1

/-- **Transport of face classes between walks.**  A face class path of the first walk starting in
its lobe stays in the lobe, and is a face class path of any walk along outer darts. -/
theorem eqvGen_transport (X : DiscDiagram.{u, w, v} W) {e₁ e₂ : X.toCombMap.Dart}
    (hout : X.outerFace ∉ lobe X e₁) {z z' : X.toCombMap.Dart}
    (h : Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
      (walkKeep X.toCombMap (walk X e₁))) z z') :
    (X.toCombMap.faceOf z ∈ lobe X e₁ ↔ X.toCombMap.faceOf z' ∈ lobe X e₁) ∧
      (X.toCombMap.faceOf z ∈ lobe X e₁ → Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
        (walkKeep X.toCombMap (walk X e₂))) z z') := by
  induction h with
  | rel x y hxy =>
      rcases hxy with rfl | ⟨hk, rfl⟩
      · rw [X.toCombMap.faceOf_facePerm]
        exact ⟨Iff.rfl, fun _ => .rel _ _ (Or.inl rfl)⟩
      · have hk' : ¬ walkKeep X.toCombMap (walk X e₁) (X.toCombMap.alpha x) := by
          rwa [walkKeep_alpha]
        refine ⟨⟨fun hx => faceOf_alpha_mem_enclosedFaces hk hx, fun hx => ?_⟩,
          fun hx => .rel _ _ (Or.inr ⟨?_, rfl⟩)⟩
        · have h' := faceOf_alpha_mem_enclosedFaces hk' hx
          rwa [X.toCombMap.alpha_involutive x] at h'
        · have hαx := faceOf_alpha_mem_enclosedFaces hk hx
          exact not_walkKeep_of_faces X e₂ (fun h0 => hout (by rw [← h0]; exact hx))
            (fun h0 => hout (by rw [← h0]; exact hαx))
  | refl x => exact ⟨Iff.rfl, fun _ => .refl _⟩
  | symm x y _ ih => exact ⟨ih.1.symm, fun hy => .symm _ _ (ih.2 (ih.1.mpr hy))⟩
  | trans x y z _ _ ih₁ ih₂ =>
      exact ⟨ih₁.1.trans ih₂.1, fun hx => .trans _ _ _ (ih₁.2 hx) (ih₂.2 (ih₁.1.mp hx))⟩

/-- Two value failures, neither in the gap of the other, have disjoint gaps. -/
theorem gap_disjoint (X : DiscDiagram.{u, w, v} W) {e₁ e₂ : X.toCombMap.Dart}
    (hG₁ : IsValueFailure X e₁) (hG₂ : IsValueFailure X e₂) (hne : e₁ ≠ e₂)
    (h₁ : e₂ ∉ gap X e₁) (h₂ : e₁ ∉ gap X e₂) : ∀ y, y ∈ gap X e₁ → y ∉ gap X e₂ := by
  intro y hy₁ hy₂
  have hidx : idx X e₁ ≠ idx X e₂ := fun h => hne (eq_of_idx_eq X hG₁.1 h)
  obtain ⟨-, a₁, b₁⟩ := (mem_gap_iff X e₁ y).mp hy₁
  obtain ⟨-, a₂, b₂⟩ := (mem_gap_iff X e₂ y).mp hy₂
  rcases Nat.lt_or_ge (idx X e₁) (idx X e₂) with h | h
  · by_cases hc : idx X e₂ < idx X (X.toCombMap.facePerm e₁)
    · exact h₁ ((mem_gap_iff X e₁ e₂).mpr ⟨hG₂.1, h, hc⟩)
    · omega
  · by_cases hc : idx X e₁ < idx X (X.toCombMap.facePerm e₂)
    · exact h₂ ((mem_gap_iff X e₂ e₁).mpr ⟨hG₁.1, by omega, hc⟩)
    · omega

/-- **Disjoint gaps give disjoint lobes.** -/
theorem lobe_disjoint (X : DiscDiagram.{u, w, v} W) {e₁ e₂ : X.toCombMap.Dart}
    (hG₁ : IsValueFailure X e₁) (hG₂ : IsValueFailure X e₂)
    (hdisj : ∀ y, y ∈ gap X e₁ → y ∉ gap X e₂) {f : X.toCombMap.Face}
    (hf₁ : f ∈ lobe X e₁) (hf₂ : f ∈ lobe X e₂) : False := by
  obtain ⟨x, rfl⟩ : ∃ x, X.toCombMap.faceOf x = f := Quotient.exists_rep f
  obtain ⟨a₁, ha₁, hna₁, hp₁⟩ := (mem_enclosedFaces_iff X.toCombMap (walk X e₁) x).mp hf₁
  obtain ⟨a₂, ha₂, hna₂, hp₂⟩ := (mem_enclosedFaces_iff X.toCombMap (walk X e₂) x).mp hf₂
  have hout := outer_not_mem_lobe X hG₁
  have hαa₁ : X.toCombMap.alpha a₁ ∈ gap X e₁ := (mem_walk_iff X e₁ a₁).mp ha₁
  have hface₁ : X.toCombMap.faceOf (X.toCombMap.alpha a₁) ∈ lobe X e₁ :=
    (mem_enclosedFaces_iff X.toCombMap (walk X e₁) _).mpr ⟨a₁, ha₁, hna₁, .refl _⟩
  have hpath := (eqvGen_transport X (e₂ := e₂) hout hp₁).2 hface₁
  have hk : ¬ walkKeep X.toCombMap (walk X e₂) a₁ := by
    rw [walkKeep_iff]
    rintro (h | h)
    · exact hdisj _ hαa₁ h
    · apply hout
      rw [← faceOf_alpha_of_mem_gap X h]
      exact hface₁
  have hcross : Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
      (walkKeep X.toCombMap (walk X e₂))) a₁ (X.toCombMap.alpha a₁) :=
    .rel _ _ (Or.inr ⟨hk, rfl⟩)
  have hface_a₁ : X.toCombMap.faceOf a₁ = X.outerFace := faceOf_of_mem_walk X ha₁
  have hsame := eqvGen_faceClass_of_sameCycle X.toCombMap (walkKeep X.toCombMap (walk X e₂))
    ((X.toCombMap.faceOf_eq_iff a₂ a₁).mp ((faceOf_of_mem_walk X ha₂).trans hface_a₁.symm))
  exact hna₂ (alpha_mem_of_faceClass X.planar (walk_ne_nil X hG₂.2.2.2.1) (walk_vertexChain X e₂)
    (turnMem_walk X hG₂) ha₂ ha₂
    (.trans _ _ _ hsame (.trans _ _ _ hcross (.trans _ _ _ hpath (.symm _ _ hp₂)))))

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ValueFailures
