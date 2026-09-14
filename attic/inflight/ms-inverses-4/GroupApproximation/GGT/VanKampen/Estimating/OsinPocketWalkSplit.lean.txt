import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchSplitWalk
import GroupApproximation.GGT.VanKampen.ClosedWalkPinchSplit
import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# A closed walk across a vertex splitting

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, across one relator cell: the touch-only X-pocket
(`OsinLemma94CaseOneTouchOnlyStatement`).  A pocket walk passes a touch vertex twice.  Splitting that
vertex (`PinchSplit.Input.diagram`) at the reverses `x = alpha in₁` and `y = alpha in₂` of the two
darts entering it keeps every dart, edge reversal and label, and changes vertex rotation only at `x`
and `y`.

A turn of a walk from `d` to `e` is **tight** (`TightTurn`) when vertex rotation carries `e` to
`alpha d` without meeting a dart of the walk or the reverse of one strictly in between.  The turns of
a pocket walk along a face and a relator cell are tight: along a face the corner is `σ e = alpha d`,
and at a junction the rotation passes one dart of the shared arc.  Across the split:

* `tightTurn_diagram` and `isTightClosedWalk_diagram`: every tight turn stays tight, since the
  stretch before its end meets neither `x` nor `y`; so the walk stays a tight closed walk
  (`IsTightClosedWalk.isClosedDartWalk`);
* `vertexOf_diagram_ne` and `repeatedVisits_diagram_lt`: the two passages through the split vertex
  land on different vertices (`PinchSplit.Input.vertexOf_x_ne_y`), so the repeated visits drop;
* `nodup_map_vertexOf_diagram`: vertices refine, so a part that repeats no vertex still repeats none;
* `mem_sideFaces_of_diagram`: the side of the walk projects back.  The face steps change only at
  `alpha x` and `alpha y`, and the two faces they join are faces of walk darts, which lie on the side
  of the walk.  So `outerFace_not_mem_sideFaces_diagram` and `cell_not_mem_sideFaces_diagram` keep the
  exterior and a relator carrier off the side;
* `dartWord_diagram` and `cellDarts_diagram`: words and carriers are unchanged.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, Hull's small cancellation theorem, through Osin's
Lemma 9.4, Case 1).  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

namespace WalkSplit

section Walks

variable (M : CombMap.{v}) (walk : List M.Dart)

/-- **A tight turn** from `d` to `e`: vertex rotation carries `e` to `alpha d`, and no dart strictly
in between is a dart of the walk or the reverse of one. -/
def TightTurn (d e : M.Dart) : Prop :=
  ∃ n : ℕ, (M.sigma ^ n) e = M.alpha d ∧
    ∀ k : ℕ, 0 < k → k < n → ¬ walkKeep M walk ((M.sigma ^ k) e)

/-- **A tight closed walk**: nonempty, every turn tight (the closing one included), and no dart
together with its reverse. -/
structure IsTightClosedWalk : Prop where
  ne_nil : walk ≠ []
  chain : walk.IsChain (TightTurn M walk)
  closes : TightTurn M walk (walk.getLast ne_nil) (walk.head ne_nil)
  alpha_not_mem : ∀ d ∈ walk, M.alpha d ∉ walk

/-- The darts reached from a dart of the walk by face steps and by crossing edges off the walk. -/
def Reach (a : M.Dart) : Prop :=
  ∃ c ∈ walk, Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M walk)) c a

open Classical in
/-- **The repeated visits of a walk**: its darts less the vertices they start at. -/
noncomputable def repeatedVisits : ℕ :=
  walk.length - (walk.map M.vertexOf).toFinset.card

variable {M walk}

theorem TightTurn.vertexOf_eq {d e : M.Dart} (h : TightTurn M walk d e) :
    M.vertexOf (M.alpha d) = M.vertexOf e := by
  obtain ⟨n, hn, -⟩ := h
  rw [M.vertexOf_eq_iff]
  exact (show M.sigma.SameCycle e (M.alpha d) from ⟨n, by rw [zpow_natCast]; exact hn⟩).symm

/-- A tight closed walk is a closed dart walk. -/
theorem IsTightClosedWalk.isClosedDartWalk (hw : IsTightClosedWalk M walk) :
    IsClosedDartWalk M walk :=
  ⟨hw.ne_nil, hw.chain.imp fun _ _ h => h.vertexOf_eq, hw.closes.vertexOf_eq⟩

end Walks

section Split

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} [DecidableEq Delta.toCombMap.Dart]
  (I : PinchSplit.Input Delta)

/-- Vertex rotation of the split agrees with the old one away from the split darts. -/
theorem sigma_diagram_apply {z : Delta.toCombMap.Dart} (hx : z ≠ I.x) (hy : z ≠ I.y) :
    I.diagram.toCombMap.sigma z = Delta.toCombMap.sigma z := by
  change Delta.toCombMap.sigma (Equiv.swap I.x I.y z) = Delta.toCombMap.sigma z
  rw [Equiv.swap_apply_of_ne_of_ne hx hy]

/-- Along a stretch that meets neither split dart before its end, the powers of the two vertex
rotations agree. -/
theorem sigma_pow_diagram_apply {e : Delta.toCombMap.Dart} {n : ℕ}
    (h : ∀ i < n, (Delta.toCombMap.sigma ^ i) e ≠ I.x ∧ (Delta.toCombMap.sigma ^ i) e ≠ I.y) :
    ∀ k ≤ n, (I.diagram.toCombMap.sigma ^ k) e = (Delta.toCombMap.sigma ^ k) e := by
  intro k
  induction k with
  | zero => intro _; simp only [pow_zero, Equiv.Perm.one_apply]
  | succ k ih =>
      intro hk
      rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega), pow_succ', Equiv.Perm.mul_apply]
      exact sigma_diagram_apply I (h k (by omega)).1 (h k (by omega)).2

/-- **A tight turn stays tight across the split**, when both split darts are reverses of walk darts
and the walk has no spur. -/
theorem tightTurn_diagram {walk : List Delta.toCombMap.Dart}
    (hspur : ∀ d ∈ walk, Delta.toCombMap.alpha d ∉ walk)
    (hx : Delta.toCombMap.alpha I.x ∈ walk) (hy : Delta.toCombMap.alpha I.y ∈ walk)
    {d e : Delta.toCombMap.Dart} (he : e ∈ walk) (h : TightTurn Delta.toCombMap walk d e) :
    TightTurn I.diagram.toCombMap walk d e := by
  obtain ⟨n, hn, hnk⟩ := h
  have hxk : walkKeep Delta.toCombMap walk I.x := Or.inr hx
  have hyk : walkKeep Delta.toCombMap walk I.y := Or.inr hy
  have hxw : I.x ∉ walk := by
    have h' := hspur _ hx
    rwa [Delta.toCombMap.alpha_involutive] at h'
  have hyw : I.y ∉ walk := by
    have h' := hspur _ hy
    rwa [Delta.toCombMap.alpha_involutive] at h'
  have havoid : ∀ i < n,
      (Delta.toCombMap.sigma ^ i) e ≠ I.x ∧ (Delta.toCombMap.sigma ^ i) e ≠ I.y := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp only [pow_zero, Equiv.Perm.one_apply]
      exact ⟨fun h' => hxw (by rw [← h']; exact he), fun h' => hyw (by rw [← h']; exact he)⟩
    · have hnot := hnk i hpos hi
      exact ⟨fun h' => hnot (by rw [h']; exact hxk), fun h' => hnot (by rw [h']; exact hyk)⟩
  refine ⟨n, ?_, fun k hk hkn => ?_⟩
  · rw [sigma_pow_diagram_apply I havoid n le_rfl]
    exact hn
  · rw [sigma_pow_diagram_apply I havoid k hkn.le]
    exact hnk k hk hkn

/-- **A tight closed walk stays tight across the split.** -/
theorem isTightClosedWalk_diagram {walk : List Delta.toCombMap.Dart}
    (hw : IsTightClosedWalk Delta.toCombMap walk)
    (hx : Delta.toCombMap.alpha I.x ∈ walk) (hy : Delta.toCombMap.alpha I.y ∈ walk) :
    IsTightClosedWalk I.diagram.toCombMap walk where
  ne_nil := hw.ne_nil
  chain := hw.chain.imp_of_mem_imp fun _ _ _ hb h =>
    tightTurn_diagram I hw.alpha_not_mem hx hy hb h
  closes := tightTurn_diagram I hw.alpha_not_mem hx hy (List.head_mem hw.ne_nil) hw.closes
  alpha_not_mem := hw.alpha_not_mem

/-- **The two passages through the split vertex land on different vertices.** -/
theorem vertexOf_diagram_ne {walk : List Delta.toCombMap.Dart}
    (hw : IsTightClosedWalk Delta.toCombMap walk)
    (hx : Delta.toCombMap.alpha I.x ∈ walk) (hy : Delta.toCombMap.alpha I.y ∈ walk)
    {e₁ e₂ : Delta.toCombMap.Dart} (he₁ : e₁ ∈ walk) (he₂ : e₂ ∈ walk)
    (ht₁ : TightTurn Delta.toCombMap walk (Delta.toCombMap.alpha I.x) e₁)
    (ht₂ : TightTurn Delta.toCombMap walk (Delta.toCombMap.alpha I.y) e₂) :
    I.diagram.toCombMap.vertexOf e₁ ≠ I.diagram.toCombMap.vertexOf e₂ := by
  have h₁ := (tightTurn_diagram I hw.alpha_not_mem hx hy he₁ ht₁).vertexOf_eq
  have h₂ := (tightTurn_diagram I hw.alpha_not_mem hx hy he₂ ht₂).vertexOf_eq
  have hx' : I.diagram.toCombMap.alpha (Delta.toCombMap.alpha I.x) = I.x :=
    Delta.toCombMap.alpha_involutive I.x
  have hy' : I.diagram.toCombMap.alpha (Delta.toCombMap.alpha I.y) = I.y :=
    Delta.toCombMap.alpha_involutive I.y
  rw [hx'] at h₁
  rw [hy'] at h₂
  rw [← h₁, ← h₂]
  exact I.vertexOf_x_ne_y

/-- **Vertices refine**: a list of darts that repeats no vertex repeats none after the split. -/
theorem nodup_map_vertexOf_diagram {l : List Delta.toCombMap.Dart}
    (h : (l.map Delta.toCombMap.vertexOf).Nodup) : (l.map I.diagram.toCombMap.vertexOf).Nodup := by
  have hproj : l.map Delta.toCombMap.vertexOf =
      (l.map I.diagram.toCombMap.vertexOf).map I.vertexProj := by
    rw [List.map_map]
    exact List.map_congr_left fun d _ => (I.vertexProj_vertexOf d).symm
  rw [hproj] at h
  exact h.of_map _

/-- **The repeated visits drop across the split.** -/
theorem repeatedVisits_diagram_lt {walk : List Delta.toCombMap.Dart}
    (hw : IsTightClosedWalk Delta.toCombMap walk)
    (hx : Delta.toCombMap.alpha I.x ∈ walk) (hy : Delta.toCombMap.alpha I.y ∈ walk)
    {e₁ e₂ : Delta.toCombMap.Dart} (he₁ : e₁ ∈ walk) (he₂ : e₂ ∈ walk)
    (ht₁ : TightTurn Delta.toCombMap walk (Delta.toCombMap.alpha I.x) e₁)
    (ht₂ : TightTurn Delta.toCombMap walk (Delta.toCombMap.alpha I.y) e₂) :
    repeatedVisits I.diagram.toCombMap walk < repeatedVisits Delta.toCombMap walk := by
  unfold repeatedVisits
  refine length_sub_card_toFinset_map_lt I.diagram.toCombMap.vertexOf I.vertexProj
    Delta.toCombMap.vertexOf (fun a => I.vertexProj_vertexOf a) he₁ he₂
    (vertexOf_diagram_ne I hw hx hy he₁ he₂ ht₁ ht₂) ?_
  have h₁ := ht₁.vertexOf_eq
  have h₂ := ht₂.vertexOf_eq
  rw [Delta.toCombMap.alpha_involutive] at h₁ h₂
  rw [← h₁, ← h₂]
  exact (Delta.toCombMap.vertexOf_eq_iff I.x I.y).mpr I.same_vertex

/-- **The side of the walk projects back across the split**, when the two merged faces are on the
side of the walk before the split. -/
theorem mem_sideFaces_of_diagram {walk : List Delta.toCombMap.Dart}
    (hleft : I.leftFace ∈ sideFaces Delta.toCombMap walk)
    (hright : I.rightFace ∈ sideFaces Delta.toCombMap walk)
    {z : Delta.toCombMap.Dart}
    (hz : I.diagram.toCombMap.faceOf z ∈ sideFaces I.diagram.toCombMap walk) :
    Delta.toCombMap.faceOf z ∈ sideFaces Delta.toCombMap walk := by
  rw [mem_sideFaces_iff] at hz ⊢
  obtain ⟨d, hd, hdz⟩ := hz
  have hRface : ∀ a, Delta.toCombMap.faceOf a ∈ sideFaces Delta.toCombMap walk →
      Reach Delta.toCombMap walk a :=
    fun a ha => (mem_sideFaces_iff Delta.toCombMap walk a).mp ha
  have hstep : ∀ a b,
      CombMap.FaceClassStep I.diagram.toCombMap (walkKeep I.diagram.toCombMap walk) a b →
        (Reach Delta.toCombMap walk a ↔ Reach Delta.toCombMap walk b) := by
    intro a b hab
    have horig : CombMap.FaceClassStep Delta.toCombMap (walkKeep Delta.toCombMap walk) a b →
        (Reach Delta.toCombMap walk a ↔ Reach Delta.toCombMap walk b) := by
      intro h
      constructor
      · rintro ⟨c, hc, hca⟩
        exact ⟨c, hc, .trans _ _ _ hca (.rel _ _ h)⟩
      · rintro ⟨c, hc, hcb⟩
        exact ⟨c, hc, .trans _ _ _ hcb (.symm _ _ (.rel _ _ h))⟩
    rcases hab with hfp | ⟨hkeep, hal⟩
    · by_cases hax : a = Delta.toCombMap.alpha I.x
      · subst hax
        have hb : b = Delta.toCombMap.facePerm (Delta.toCombMap.alpha I.y) :=
          hfp.trans (PinchSplit.facePerm_apply_alpha_left Delta.toCombMap I.x I.y)
        refine ⟨fun _ => ?_, fun _ => hRface _ hleft⟩
        apply hRface
        rw [hb, Delta.toCombMap.faceOf_facePerm]
        exact hright
      · by_cases hay : a = Delta.toCombMap.alpha I.y
        · subst hay
          have hb : b = Delta.toCombMap.facePerm (Delta.toCombMap.alpha I.x) :=
            hfp.trans (PinchSplit.facePerm_apply_alpha_right Delta.toCombMap I.x I.y)
          refine ⟨fun _ => ?_, fun _ => hRface _ hright⟩
          apply hRface
          rw [hb, Delta.toCombMap.faceOf_facePerm]
          exact hleft
        · exact horig
            (Or.inl (hfp.trans (PinchSplit.facePerm_apply_of_ne Delta.toCombMap I.x I.y hax hay)))
    · exact horig (Or.inr ⟨hkeep, hal⟩)
  have hiff : ∀ a b,
      Relation.EqvGen
          (CombMap.FaceClassStep I.diagram.toCombMap (walkKeep I.diagram.toCombMap walk)) a b →
        (Reach Delta.toCombMap walk a ↔ Reach Delta.toCombMap walk b) := by
    intro a b h
    induction h with
    | rel a b hab => exact hstep a b hab
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (hiff d z hdz).mp ⟨d, hd, .refl _⟩

/-- **The exterior stays off the side of the walk across the split.** -/
theorem outerFace_not_mem_sideFaces_diagram {walk : List Delta.toCombMap.Dart}
    (hleft : I.leftFace ∈ sideFaces Delta.toCombMap walk)
    (hright : I.rightFace ∈ sideFaces Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk) :
    I.diagram.outerFace ∉ sideFaces I.diagram.toCombMap walk := by
  obtain ⟨z, hz⟩ := Quotient.exists_rep Delta.outerFace
  have hzface : Delta.toCombMap.faceOf z = Delta.outerFace := hz
  intro h
  apply hout
  rw [← hzface]
  apply mem_sideFaces_of_diagram I hleft hright
  rw [I.diagram_faceOf, hzface]
  exact h

/-- **A relator carrier stays off the side of the walk across the split.** -/
theorem cell_not_mem_sideFaces_diagram {walk : List Delta.toCombMap.Dart}
    (hleft : I.leftFace ∈ sideFaces Delta.toCombMap walk)
    (hright : I.rightFace ∈ sideFaces Delta.toCombMap walk) {i : Fin Delta.rCellCount}
    (hi : (Embedded.cell Delta i).face ∉ sideFaces Delta.toCombMap walk) :
    (Embedded.cell I.diagram (I.cellMap.indexEquiv i)).face ∉
      sideFaces I.diagram.toCombMap walk := by
  obtain ⟨z, hz⟩ := Quotient.exists_rep (Embedded.cell Delta i).face
  have hzface : Delta.toCombMap.faceOf z = (Embedded.cell Delta i).face := hz
  have hcell : (Embedded.cell I.diagram (I.cellMap.indexEquiv i)).face =
      I.kept (Embedded.cell Delta i).face := by
    rw [I.cellMap.indexed_cell i]
    rfl
  intro h
  apply hi
  rw [← hzface]
  apply mem_sideFaces_of_diagram I hleft hright
  rw [I.diagram_faceOf, hzface, ← hcell]
  exact h

/-- Words of dart lists are unchanged by the split. -/
theorem dartWord_diagram (l : List Delta.toCombMap.Dart) :
    dartWord I.diagram l = dartWord Delta l :=
  rfl

/-- The carrier of a relator cell is unchanged by the split. -/
theorem cellDarts_diagram (i : Fin Delta.rCellCount) :
    cellDarts I.diagram (I.cellMap.indexEquiv i) = cellDarts Delta i := by
  rw [I.cellDarts_eq i, List.map_id]

end Split

end WalkSplit

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.WalkSplit.isTightClosedWalk_diagram
#audit_axioms GroupApproximation.GGT.VanKampen.WalkSplit.repeatedVisits_diagram_lt
#audit_axioms GroupApproximation.GGT.VanKampen.WalkSplit.nodup_map_vertexOf_diagram
#audit_axioms GroupApproximation.GGT.VanKampen.WalkSplit.mem_sideFaces_of_diagram
#audit_axioms GroupApproximation.GGT.VanKampen.WalkSplit.outerFace_not_mem_sideFaces_diagram
#audit_axioms GroupApproximation.GGT.VanKampen.WalkSplit.cell_not_mem_sideFaces_diagram
#audit_axioms GroupApproximation.GGT.VanKampen.WalkSplit.cellDarts_diagram
