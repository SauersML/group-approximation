import GroupApproximation.GGT.VanKampen.SurgeryPinchSplitMap
import GroupApproximation.GGT.VanKampen.CombMapEulerUpperBound
import GroupApproximation.Meta.AxiomGuard

/-!
# Genus-zero splits and successor steps

Pure combinatorial-map lemmas behind the genus-zero first-return lemma
(`WitnessStepGenusFirstReturn`).

* `witnessStepGenus_split_not_connected`: splitting one vertex of a planar map at two
  distinct darts whose reverses lie on one face gives Euler characteristic `4`
  (`V + 1`, `E`, `F + 1`), so the split map is disconnected
  (`CombMap.eulerCharacteristic_le_two`).
* `witnessStepGenus_split_separates`: in that split map the two split darts are not
  connected, since every old elementary move lifts once they are.
* `witnessStepGenus_run_lift`, `witnessStepGenus_face_lift`: vertex runs and face steps
  that avoid the split darts survive the split.
* `WitnessStepGenusSucc` and `witnessStepGenus_step_lift`: a successor step of a list
  (the first kept dart in the vertex run from the reverse) survives the split taken at
  the run of another step.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness

universe u

/-- **Same-vertex same-face split of a planar map is disconnected.** -/
theorem witnessStepGenus_split_not_connected (N : CombMap.{u}) [DecidableEq N.Dart]
    (hN : N.IsPlanar) {x y : N.Dart} (hxy : N.sigma.SameCycle x y) (hne : x ≠ y)
    (hface : N.facePerm.SameCycle (N.alpha x) (N.alpha y)) :
    ¬ (PinchSplit.toCombMap N x y).IsConnected := by
  intro hconn
  have hle := CombMap.eulerCharacteristic_le_two (PinchSplit.toCombMap N x y) hconn
  have h2 := hN.2
  have hv := PinchSplit.vertexCount_eq N x y hxy hne
  have he : (PinchSplit.toCombMap N x y).edgeCount = N.edgeCount :=
    PinchSplit.edgeCount_eq N x y
  have hf : (PinchSplit.toCombMap N x y).faceCount = N.faceCount + 1 :=
    VertexJoin.faceCount_eq N x y (fun h => hne (N.alpha.injective h)) hface
  unfold CombMap.eulerCharacteristic at hle h2
  rw [hv, he, hf] at hle
  push_cast at hle
  omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepGenus_split_not_connected

/-- **The split darts are separated.**  If they were connected, every old move would
lift and the split map would be connected. -/
theorem witnessStepGenus_split_separates (N : CombMap.{u}) [DecidableEq N.Dart]
    (hN : N.IsPlanar) {x y : N.Dart} (hxy : N.sigma.SameCycle x y) (hne : x ≠ y)
    (hface : N.facePerm.SameCycle (N.alpha x) (N.alpha y)) :
    ¬ Relation.EqvGen (PinchSplit.toCombMap N x y).Adjacent x y := by
  intro hjoin
  apply witnessStepGenus_split_not_connected N hN hxy hne hface
  have hstep : ∀ u v : N.Dart, N.Adjacent u v →
      Relation.EqvGen (PinchSplit.toCombMap N x y).Adjacent u v := by
    intro u v huv
    rcases huv with h | h
    · exact Relation.EqvGen.rel _ _ (Or.inl h)
    · rw [← h]
      by_cases hux : u = x
      · rw [hux]
        have h1 : (PinchSplit.toCombMap N x y).sigma y = N.sigma x := by
          change N.sigma (Equiv.swap x y y) = N.sigma x
          rw [Equiv.swap_apply_right]
        exact Relation.EqvGen.trans _ y _ hjoin (Relation.EqvGen.rel _ _ (Or.inr h1))
      · by_cases huy : u = y
        · rw [huy]
          have h2 : (PinchSplit.toCombMap N x y).sigma x = N.sigma y := by
            change N.sigma (Equiv.swap x y x) = N.sigma y
            rw [Equiv.swap_apply_left]
          exact Relation.EqvGen.trans _ x _ (Relation.EqvGen.symm _ _ hjoin)
            (Relation.EqvGen.rel _ _ (Or.inr h2))
        · apply Relation.EqvGen.rel
          right
          change N.sigma (Equiv.swap x y u) = N.sigma u
          rw [Equiv.swap_apply_of_ne_of_ne hux huy]
  intro d e
  have hlift : ∀ u v : N.Dart, Relation.EqvGen N.Adjacent u v →
      Relation.EqvGen (PinchSplit.toCombMap N x y).Adjacent u v := by
    intro u v huv
    induction huv with
    | rel u v h => exact hstep u v h
    | refl u => exact Relation.EqvGen.refl _
    | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans u v w _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  exact hlift d e (hN.1 d e)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepGenus_split_separates

/-- A vertex run avoiding the split darts survives the split. -/
theorem witnessStepGenus_run_lift (N : CombMap.{u}) [DecidableEq N.Dart] (x y u : N.Dart) :
    ∀ k : ℕ, (∀ j, j < k → (N.sigma ^ j) u ≠ x ∧ (N.sigma ^ j) u ≠ y) →
      Relation.EqvGen (PinchSplit.toCombMap N x y).Adjacent u ((N.sigma ^ k) u) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [pow_zero, Equiv.Perm.one_apply]
    exact Relation.EqvGen.refl _
  | succ k ih =>
    intro h
    have hk := h k (Nat.lt_succ_self k)
    refine Relation.EqvGen.trans _ _ _ (ih fun j hj => h j (Nat.lt_succ_of_lt hj)) ?_
    apply Relation.EqvGen.rel
    right
    change N.sigma (Equiv.swap x y ((N.sigma ^ k) u)) = (N.sigma ^ (k + 1)) u
    rw [Equiv.swap_apply_of_ne_of_ne hk.1 hk.2, pow_succ', Equiv.Perm.mul_apply]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepGenus_run_lift

/-- A face step whose reverse avoids the split darts survives the split. -/
theorem witnessStepGenus_face_lift (N : CombMap.{u}) [DecidableEq N.Dart] (x y u : N.Dart)
    (h1 : N.alpha u ≠ x) (h2 : N.alpha u ≠ y) :
    Relation.EqvGen (PinchSplit.toCombMap N x y).Adjacent u (N.facePerm u) := by
  refine Relation.EqvGen.trans _ (N.alpha u) _ (Relation.EqvGen.rel _ _ (Or.inl rfl)) ?_
  apply Relation.EqvGen.rel
  right
  change N.sigma (Equiv.swap x y (N.alpha u)) = N.sigma (N.alpha u)
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepGenus_face_lift

/-- A chain of reachability steps reaches every entry from its head. -/
theorem witnessStepGenus_eqvGen_of_isChain {β : Type*} {S : β → β → Prop} :
    ∀ (L : List β) (a : β), List.IsChain (Relation.EqvGen S) (a :: L) →
      ∀ e ∈ a :: L, Relation.EqvGen S a e
  | [], _, _, _, he => by
    rw [List.mem_singleton.mp he]
    exact Relation.EqvGen.refl _
  | b :: L, _, hc, e, he => by
    rw [List.isChain_cons_cons] at hc
    rcases List.mem_cons.mp he with hea | heb
    · rw [hea]
      exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.trans _ _ _ hc.1 (witnessStepGenus_eqvGen_of_isChain L b hc.2 e heb)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepGenus_eqvGen_of_isChain

/-- Consecutive entries not starting at the last entry `p` are related; then every
entry reaches `p`. -/
theorem witnessStepGenus_eqvGen_to_last {β : Type*} (S : β → β → Prop) (p : β) :
    ∀ L : List β, (L ++ [p]).Nodup →
      (∀ u v e e', L ++ [p] = u ++ e :: e' :: v → e ≠ p → Relation.EqvGen S e e') →
      ∀ e ∈ L ++ [p], Relation.EqvGen S e p
  | [], _, _, _, he => by
    rw [List.nil_append, List.mem_singleton] at he
    rw [he]
    exact Relation.EqvGen.refl _
  | a :: L, hnd, hstep, e, he => by
    rw [List.cons_append] at hnd he
    obtain ⟨hanot, hnd'⟩ := List.nodup_cons.mp hnd
    have hstep' : ∀ u v e e', L ++ [p] = u ++ e :: e' :: v → e ≠ p →
        Relation.EqvGen S e e' := by
      intro u v e e' h hne
      exact hstep (a :: u) v e e' (by rw [List.cons_append, h, List.cons_append]) hne
    have ih := witnessStepGenus_eqvGen_to_last S p L hnd' hstep'
    rcases List.mem_cons.mp he with hea | hel
    · rw [hea]
      obtain ⟨b, r, hbr⟩ := List.exists_cons_of_ne_nil (l := L ++ [p]) (by simp)
      have hap : a ≠ p := fun h =>
        hanot (by rw [h]; exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
      have hab : Relation.EqvGen S a b :=
        hstep [] r a b (by rw [List.cons_append, hbr, List.nil_append]) hap
      have hb : b ∈ L ++ [p] := by
        rw [hbr]
        exact List.mem_cons.mpr (Or.inl rfl)
      exact Relation.EqvGen.trans _ _ _ hab (ih b hb)
    · exact ih e hel

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepGenus_eqvGen_to_last

/-- **Successor step.**  `y` is the first dart of the vertex run after the reverse of
`x` which is kept, that is, lies in `l` or has its reverse in `l`. -/
def WitnessStepGenusSucc (N : CombMap.{u}) (l : List N.Dart) (x y : N.Dart) : Prop :=
  ∃ m : ℕ, 0 < m ∧ (N.sigma ^ m) (N.alpha x) = y ∧
    ∀ k : ℕ, 0 < k → k < m → (N.sigma ^ k) (N.alpha x) ∉ l ∧
      N.alpha ((N.sigma ^ k) (N.alpha x)) ∉ l

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessStepGenusSucc

/-- **A successor step survives the split at another step's run.**  Let the step from `p`
run for `m ≥ 2` vertex rotations through unkept darts.  Split the vertex at `alpha p` and
at the last unkept dart `sigma ^ (m - 1) (alpha p)`.  Then the successor step from any
other kept `z` still connects `z` to its successor. -/
theorem witnessStepGenus_step_lift (N : CombMap.{u}) [DecidableEq N.Dart] {l : List N.Dart}
    {p z z' : N.Dart} {m : ℕ} (hm : 2 ≤ m) (hpl : p ∈ l)
    (hrun : ∀ k : ℕ, 0 < k → k < m → (N.sigma ^ k) (N.alpha p) ∉ l ∧
      N.alpha ((N.sigma ^ k) (N.alpha p)) ∉ l)
    (hz : z ∈ l) (hzp : z ≠ p) (hs : WitnessStepGenusSucc N l z z') :
    Relation.EqvGen
      (PinchSplit.toCombMap N (N.alpha p) ((N.sigma ^ (m - 1)) (N.alpha p))).Adjacent z z' := by
  obtain ⟨mz, _, hz', hzrun⟩ := hs
  refine Relation.EqvGen.trans _ (N.alpha z) _ (Relation.EqvGen.rel _ _ (Or.inl rfl)) ?_
  rw [← hz']
  apply witnessStepGenus_run_lift
  intro j hj
  have hαz : N.alpha (N.alpha z) = z := N.alpha_involutive z
  have hαp : N.alpha (N.alpha p) = p := N.alpha_involutive p
  have hA : ∀ i : ℕ, i < mz → (N.sigma ^ i) (N.alpha z) ≠ N.alpha p := by
    intro i hi heq
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · rw [h0, pow_zero, Equiv.Perm.one_apply] at heq
      exact hzp (N.alpha.injective heq)
    · exact (hzrun i hpos hi).2 (by rw [heq, hαp]; exact hpl)
  refine ⟨hA j hj, ?_⟩
  intro heq
  rcases le_or_gt (m - 1) j with hle | hlt
  · have hcomp : (N.sigma ^ (m - 1)) ((N.sigma ^ (j - (m - 1))) (N.alpha z)) =
        (N.sigma ^ j) (N.alpha z) := by
      rw [← Equiv.Perm.mul_apply (N.sigma ^ (m - 1)), ← pow_add, Nat.add_sub_of_le hle]
    apply hA (j - (m - 1)) (by omega)
    apply (N.sigma ^ (m - 1)).injective
    rw [hcomp]
    exact heq
  · have hcomp : (N.sigma ^ j) ((N.sigma ^ (m - 1 - j)) (N.alpha p)) =
        (N.sigma ^ (m - 1)) (N.alpha p) := by
      rw [← Equiv.Perm.mul_apply (N.sigma ^ j), ← pow_add, Nat.add_sub_of_le hlt.le]
    have hi : (N.sigma ^ (m - 1 - j)) (N.alpha p) = N.alpha z := by
      apply (N.sigma ^ j).injective
      rw [hcomp]
      exact heq.symm
    exact (hrun (m - 1 - j) (by omega) (by omega)).2 (by rw [hi, hαz]; exact hz)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepGenus_step_lift

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness
