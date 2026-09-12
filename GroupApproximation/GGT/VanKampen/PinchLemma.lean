import GroupApproximation.GGT.VanKampen.PlanarVanKampen
import GroupApproximation.GGT.VanKampen.FoldFaceCycles
import GroupApproximation.GGT.VanKampen.CombMapReduction
import GroupApproximation.GGT.VanKampen.CombMapEulerUpperBound
import GroupApproximation.GGT.KazhdanHypGirthEightDiagram
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# A pinched cancelling pair shortens the relator product

Let the exterior traversal of a relator-covered disc diagram contain consecutive darts
`d e` reading a letter and its inverse, with `e ≠ alpha d`, and suppose the two ends of
the pair coincide: the vertex before `d` is the vertex after `e`.  Then the pair cannot
be folded; instead the loop `d e` pinches off a part of the diagram.

Splitting that vertex (`FoldMap.joined`, now with the two corners on one vertex) raises
the Euler characteristic to `4`, so the split map has two components: the part `Δ₁`
reached from `d`, containing `e`, `alpha e` and the face of `alpha e`, and the rest,
containing the remaining exterior darts (`not_reach_p`, `mem_rest_not_reach`).  Every
other face lies in one component.

Relabel every edge of `Δ₁` by the trivial letter.  Its faces become freely trivial, the
exterior value is unchanged because `d e` read a cancelling pair, and the other faces keep
their relator words.  The planar van Kampen lemma then writes the boundary value with one
factor for each relator face outside `Δ₁`, which is fewer than the relator area because
the face of `alpha e` is inside (`exists_isRelatorProduct_lt_of_pinch`).
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv RelatorDefectBudget

universe u w v

namespace PinchLemma

section Map

variable {M : CombMap.{v}}

/-- A face rotation step is reached by elementary moves. -/
theorem eqvGen_facePerm (x : M.Dart) : Relation.EqvGen M.Adjacent x (M.facePerm x) :=
  Relation.EqvGen.trans _ (M.alpha x) _ (Relation.EqvGen.rel _ _ (Or.inl rfl))
    (Relation.EqvGen.rel _ _ (Or.inr rfl))

/-- Darts of one face are reached by elementary moves. -/
theorem eqvGen_of_faceOf_eq {x y : M.Dart} (h : M.faceOf x = M.faceOf y) :
    Relation.EqvGen M.Adjacent x y := by
  obtain ⟨n, hn⟩ := ((M.faceOf_eq_iff x y).mp h).exists_nat_pow_eq
  have hpow : ∀ (m : ℕ) (z : M.Dart), Relation.EqvGen M.Adjacent z ((M.facePerm ^ m) z) := by
    intro m
    induction m with
    | zero => intro z; exact Relation.EqvGen.refl _
    | succ m ih =>
        intro z
        rw [pow_succ, Perm.mul_apply]
        exact Relation.EqvGen.trans _ _ _ (eqvGen_facePerm z) (ih (M.facePerm z))
  simpa only [hn] using hpow n x

variable [DecidableEq M.Dart]

/-- **The split map has Euler characteristic four.** -/
theorem split_euler (hM : M.IsPlanar) {p e : M.Dart} (hpe : p ≠ e)
    (hface : M.faceOf p = M.faceOf e)
    (hpinch : M.sigma.SameCycle (M.alpha p) (M.alpha e)) :
    (FoldMap.joined M p e).eulerCharacteristic = 4 := by
  have hαne : M.alpha p ≠ M.alpha e := fun h => hpe (M.alpha_involutive.injective h)
  have hv : (FoldMap.joined M p e).vertexCount = M.vertexCount + 1 := by
    change Nat.card (CombMap.Orbit (M.sigma * Equiv.swap (M.alpha p) (M.alpha e))) =
      Nat.card (CombMap.Orbit M.sigma) + 1
    rw [PermCycleCoordinates.orbit_card_mul_swap_eq]
    exact PermCycleCoordinates.orbit_card_swap_mul M.sigma (M.alpha p) (M.alpha e) hαne hpinch
  have hf : (FoldMap.joined M p e).faceCount = M.faceCount + 1 := by
    apply VertexJoin.faceCount_eq
    · rw [M.alpha_involutive, M.alpha_involutive]
      exact hpe
    · rw [M.alpha_involutive, M.alpha_involutive]
      exact (M.faceOf_eq_iff p e).mp hface
  have he : (FoldMap.joined M p e).edgeCount = M.edgeCount := rfl
  have h2 := hM.2
  unfold CombMap.eulerCharacteristic at h2 ⊢
  rw [hv, hf, he]
  push_cast
  linarith

variable {p d e : M.Dart}

/-- In the split map a face step of `d` reaches `e`. -/
theorem split_facePerm_d (hnext : M.facePerm d = e) (hde : d ≠ e)
    (hdp : d ≠ p) : (FoldMap.joined M p e).facePerm d = e := by
  rw [FoldMap.joined_facePerm_apply, Equiv.swap_apply_of_ne_of_ne hdp hde, hnext]

/-- **Every dart of the split map is reached from `d` or from `p`.** -/
theorem reach_or_reach (hM : M.IsConnected) (hprev : M.facePerm p = d)
    (hnext : M.facePerm d = e) (hde : d ≠ e) (hdp : d ≠ p) (x : M.Dart) :
    Relation.EqvGen (FoldMap.joined M p e).Adjacent d x ∨
      Relation.EqvGen (FoldMap.joined M p e).Adjacent p x := by
  let J := FoldMap.joined M p e
  let P : M.Dart → Prop := fun y => Relation.EqvGen J.Adjacent d y ∨
    Relation.EqvGen J.Adjacent p y
  have hsame : ∀ y z, Relation.EqvGen J.Adjacent y z → (P y ↔ P z) := by
    intro y z hyz
    constructor
    · rintro (h | h)
      · exact Or.inl (Relation.EqvGen.trans _ _ _ h hyz)
      · exact Or.inr (Relation.EqvGen.trans _ _ _ h hyz)
    · rintro (h | h)
      · exact Or.inl (Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.symm _ _ hyz))
      · exact Or.inr (Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.symm _ _ hyz))
  have hPd : ∀ y, Relation.EqvGen J.Adjacent d y → P y := fun y h => Or.inl h
  have hPp : ∀ y, Relation.EqvGen J.Adjacent p y → P y := fun y h => Or.inr h
  have hde' : Relation.EqvGen J.Adjacent d e := by
    have h := eqvGen_facePerm (M := J) d
    rwa [split_facePerm_d hnext hde hdp] at h
  have hstep : ∀ y z, M.Adjacent y z → (P y ↔ P z) := by
    intro y z hyz
    rcases hyz with h | h
    · exact hsame y z (Relation.EqvGen.rel _ _ (Or.inl h))
    · by_cases hy1 : y = M.alpha p
      · have hz : z = d := by rw [← h, hy1]; exact hprev
        have hPy : P y := hPp y (by
          rw [hy1]
          exact Relation.EqvGen.rel _ _ (Or.inl rfl))
        have hPz : P z := hPd z (by rw [hz]; exact Relation.EqvGen.refl _)
        exact ⟨fun _ => hPz, fun _ => hPy⟩
      · by_cases hy2 : y = M.alpha e
        · have hPy : P y := hPd y (by
            rw [hy2]
            exact Relation.EqvGen.trans _ _ _ hde' (Relation.EqvGen.rel _ _ (Or.inl rfl)))
          have hPz : P z := hPp z (by
            have hq : J.facePerm p = z := by
              rw [FoldMap.joined_facePerm_apply, Equiv.swap_apply_left, ← h, hy2]
              rfl
            rw [← hq]
            exact eqvGen_facePerm (M := J) p)
          exact ⟨fun _ => hPz, fun _ => hPy⟩
        · apply hsame
          apply Relation.EqvGen.rel
          right
          show M.sigma (Equiv.swap (M.alpha p) (M.alpha e) y) = z
          rw [Equiv.swap_apply_of_ne_of_ne hy1 hy2, h]
  have hgen : ∀ y z, Relation.EqvGen M.Adjacent y z → (P y ↔ P z) := by
    intro y z hyz
    induction hyz with
    | rel y z h => exact hstep y z h
    | refl y => exact Iff.rfl
    | symm y z _ ih => exact ih.symm
    | trans y z w _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (hgen d x (hM d x)).mp (Or.inl (Relation.EqvGen.refl _))

/-- **The pinched part does not reach the rest**: `p` is not reached from `d` in the
split map. -/
theorem not_reach_p (hM : M.IsPlanar) (hprev : M.facePerm p = d) (hnext : M.facePerm d = e)
    (hde : d ≠ e) (hdp : d ≠ p) (hpe : p ≠ e) (hface : M.faceOf p = M.faceOf e)
    (hpinch : M.sigma.SameCycle (M.alpha p) (M.alpha e)) :
    ¬ Relation.EqvGen (FoldMap.joined M p e).Adjacent d p := by
  intro hdp'
  have hall : ∀ x, Relation.EqvGen (FoldMap.joined M p e).Adjacent d x := fun x =>
    (reach_or_reach hM.1 hprev hnext hde hdp x).elim id
      (fun h => Relation.EqvGen.trans _ _ _ hdp' h)
  have hconn : (FoldMap.joined M p e).IsConnected := fun x y =>
    Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hall x)) (hall y)
  have hle := (FoldMap.joined M p e).eulerCharacteristic_le_two hconn
  rw [split_euler hM hpe hface hpinch] at hle
  norm_num at hle

/-- The rest of the pair face is a face cycle of the split map. -/
theorem split_isFaceCycle_rest (hprev : M.facePerm p = d) (hpe : p ≠ e) {rest : List M.Dart}
    (hl : M.IsFaceCycle (d :: e :: rest)) : (FoldMap.joined M p e).IsFaceCycle rest := by
  have hnd := hl.nodup
  have hd_notin : d ∉ rest :=
    fun hmem => (List.nodup_cons.mp hnd).1 (List.mem_cons_of_mem e hmem)
  have he_notin : e ∉ rest := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
  have hrest_ne : rest ≠ [] := by
    rintro rfl
    have hc : M.facePerm e = d := hl.closes
    exact hpe (M.facePerm.injective (hprev.trans hc.symm))
  have hlast : (d :: e :: rest).getLast hl.ne_nil = rest.getLast hrest_ne := by
    rw [List.getLast_cons_cons, List.getLast_cons hrest_ne]
  have hp_last : rest.getLast hrest_ne = p := by
    apply M.facePerm.injective
    rw [hprev, ← hlast]
    exact hl.closes
  have hchain := hl.chain
  rw [List.isChain_cons_cons, List.isChain_cons] at hchain
  obtain ⟨_, hhead, hrest_chain⟩ := hchain
  have hstep : ∀ x ∈ rest, ∀ y ∈ rest, M.facePerm x = y → (FoldMap.joined M p e).facePerm x = y := by
    intro x hx y hy hxy
    have hxp : x ≠ p := by
      rintro rfl
      exact hd_notin (by rw [← hprev, hxy]; exact hy)
    have hxe : x ≠ e := fun hxe => he_notin (hxe ▸ hx)
    rw [FoldMap.joined_facePerm_apply, Equiv.swap_apply_of_ne_of_ne hxp hxe, hxy]
  refine ⟨hrest_ne, (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2,
    hrest_chain.imp_of_mem_imp fun x y hx hy hxy => hstep x hx y hy hxy, ?_⟩
  have hhd : M.facePerm e = rest.head hrest_ne := hhead _ (List.head?_eq_some_head hrest_ne)
  exact (congrArg (FoldMap.joined M p e).facePerm hp_last).trans
    ((FoldMap.joined_facePerm_prev (M := M) (p := p) (e := e)).trans hhd)

end Map

section Diagram

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **A pinched cancelling pair shortens the relator product.** -/
theorem exists_isRelatorProduct_lt_of_pinch (Delta : DiscDiagram.{u, w, v} W)
    (hcover : RelatorCellCover Delta) {s t : List Delta.toCombMap.Dart}
    {p d e : Delta.toCombMap.Dart}
    (houter : (Delta.faceBoundary Delta.outerFace).darts = s ++ d :: e :: t)
    (hlabel : Delta.label e = HullSC.RelWord.inv (Delta.label d))
    (hspur : e ≠ Delta.toCombMap.alpha d)
    (hprev : Delta.toCombMap.facePerm p = d) (hpe : p ≠ e)
    (hpinch : Delta.toCombMap.sigma.SameCycle (Delta.toCombMap.alpha p)
      (Delta.toCombMap.alpha e)) :
    ∃ m < Delta.rCellCount, IsRelatorProduct (RelLetter.listVal '' W) m Delta.boundaryValue := by
  classical
  let M := Delta.toCombMap
  let J := FoldMap.joined M p e
  let O := Delta.outerFace
  let FB := Delta.faceBoundary
  have hO := (FB O).isFaceCycle
  have hnd : (s ++ d :: e :: t).Nodup := by rw [← houter]; exact (FB O).nodup
  have hchainO : (s ++ d :: e :: t).IsChain fun x y => M.facePerm x = y := by
    rw [← houter]; exact (FB O).chain
  have hnext : M.facePerm d = e :=
    (List.isChain_cons_cons.mp (List.isChain_append.mp hchainO).2.1).1
  have hde : d ≠ e := by
    intro h'
    exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 (h' ▸ List.mem_cons_self)
  have hdp : d ≠ p := by
    intro h'
    apply hde
    rw [← hnext, h', hprev, ← h']
  have hmemO : ∀ x, x ∈ s ++ d :: e :: t ↔ M.faceOf x = O := by
    intro x
    rw [← houter]
    exact (FB O).mem_iff x
  have hdO : M.faceOf d = O := (hmemO d).mp (by simp)
  have heO : M.faceOf e = O := (hmemO e).mp (by simp)
  have hpO : M.faceOf p = O := by rw [← M.faceOf_facePerm p, hprev]; exact hdO
  have hnot := not_reach_p Delta.planar hprev hnext hde hdp hpe (hpO.trans heO.symm) hpinch
  have hde' : Relation.EqvGen J.Adjacent d e := by
    have h' := eqvGen_facePerm (M := J) d
    rwa [split_facePerm_d hnext hde hdp] at h'
  have hdαe : Relation.EqvGen J.Adjacent d (M.alpha e) :=
    Relation.EqvGen.trans _ _ _ hde' (Relation.EqvGen.rel _ _ (Or.inl rfl))
  -- the remaining exterior darts are not reached from `d`
  have hrest : ∀ x ∈ s ++ t, ¬ Relation.EqvGen J.Adjacent d x := by
    have hrot : M.IsFaceCycle (d :: e :: (t ++ s)) := by
      have h' := hO.rotate s.length
      rw [houter, List.rotate_append_length_eq] at h'
      exact h'
    have hJ := split_isFaceCycle_rest hprev hpe hrot
    have hpmem : p ∈ t ++ s := by
      have hpin : p ∈ s ++ d :: e :: t := (hmemO p).mpr hpO
      rcases List.mem_append.mp hpin with h' | h'
      · exact List.mem_append.mpr (Or.inr h')
      · rcases List.mem_cons.mp h' with h'' | h''
        · exact absurd h''.symm hdp
        · rcases List.mem_cons.mp h'' with h''' | h'''
          · exact absurd h''' hpe
          · exact List.mem_append.mpr (Or.inl h''')
    intro x hx hdx
    have hxmem : x ∈ t ++ s := by
      rcases List.mem_append.mp hx with h' | h'
      · exact List.mem_append.mpr (Or.inr h')
      · exact List.mem_append.mpr (Or.inl h')
    have hface : J.faceOf x = J.faceOf p :=
      ((hJ.mem_iff x).mp hxmem).trans ((hJ.mem_iff p).mp hpmem).symm
    exact hnot (Relation.EqvGen.trans _ _ _ hdx (eqvGen_of_faceOf_eq hface))
  -- other faces lie in one component
  have hinner : ∀ g, g ≠ O → ∀ x ∈ (FB g).darts, ∀ y ∈ (FB g).darts,
      Relation.EqvGen J.Adjacent x y := by
    intro g hg x hx y hy
    have hpg : p ∉ (FB g).darts := fun hm => hg (((FB g).mem_iff p).mp hm ▸ hpO)
    have heg : e ∉ (FB g).darts := fun hm => hg (((FB g).mem_iff e).mp hm ▸ heO)
    have hJg := FoldMap.joined_isFaceCycle_of_avoid (FB g).isFaceCycle hpg heg
    exact eqvGen_of_faceOf_eq (((hJg.mem_iff x).mp hx).trans ((hJg.mem_iff y).mp hy).symm)
  -- the face of `alpha e` is an inner face inside the pinched part
  have hαe_notO : M.faceOf (M.alpha e) ≠ O := by
    intro h'
    have hmem := (hmemO _).mpr h'
    rcases List.mem_append.mp hmem with h'' | h''
    · exact hrest _ (List.mem_append.mpr (Or.inl h'')) hdαe
    · rcases List.mem_cons.mp h'' with h''' | h'''
      · exact hspur (by rw [← h''', M.alpha_involutive])
      · rcases List.mem_cons.mp h''' with h4 | h4
        · exact M.alpha_fixedPointFree e h4
        · exact hrest _ (List.mem_append.mpr (Or.inr h4)) hdαe
  let ge := M.faceOf (M.alpha e)
  have hge_head : Relation.EqvGen J.Adjacent d ((FB ge).darts.head (FB ge).nonempty) :=
    Relation.EqvGen.trans _ _ _ hdαe
      (hinner ge hαe_notO _ (((FB ge).mem_iff _).mpr rfl) _ (List.head_mem _))
  -- relabel the pinched part trivially
  let label' : M.Dart → RelLetter G Lambda := fun x =>
    if Relation.EqvGen J.Adjacent d x then RelLetter.base 1 else Delta.label x
  have hαiff : ∀ x, Relation.EqvGen J.Adjacent d (M.alpha x) ↔ Relation.EqvGen J.Adjacent d x :=
    fun x => ⟨fun h' => Relation.EqvGen.trans _ _ _ h'
        (Relation.EqvGen.rel _ _ (Or.inl (M.alpha_involutive x))),
      fun h' => Relation.EqvGen.trans _ _ _ h' (Relation.EqvGen.rel _ _ (Or.inl rfl))⟩
  have hlabel' : ∀ x, label' (M.alpha x) = HullSC.RelWord.inv (label' x) := by
    intro x
    by_cases hx : Relation.EqvGen J.Adjacent d x
    · show (if Relation.EqvGen J.Adjacent d (M.alpha x) then RelLetter.base 1
        else Delta.label (M.alpha x)) =
        HullSC.RelWord.inv (if Relation.EqvGen J.Adjacent d x then RelLetter.base 1
          else Delta.label x)
      rw [if_pos ((hαiff x).mpr hx), if_pos hx]
      show (RelLetter.base 1 : RelLetter G Lambda) = RelLetter.base 1⁻¹
      rw [inv_one]
    · show (if Relation.EqvGen J.Adjacent d (M.alpha x) then RelLetter.base 1
        else Delta.label (M.alpha x)) =
        HullSC.RelWord.inv (if Relation.EqvGen J.Adjacent d x then RelLetter.base 1
          else Delta.label x)
      rw [if_neg (fun h' => hx ((hαiff x).mp h')), if_neg hx]
      exact Delta.label_alpha x
  let relFaces : Finset M.Face := Finset.univ.filter fun f =>
    f ≠ O ∧ ¬ Relation.EqvGen J.Adjacent d ((FB f).darts.head (FB f).nonempty)
  have hOrel : O ∉ relFaces := by simp [relFaces]
  have hkeep : ∀ f, f ≠ O → ¬ Relation.EqvGen J.Adjacent d ((FB f).darts.head (FB f).nonempty) →
      (FB f).darts.map label' = (FB f).darts.map Delta.label := by
    intro f hf hh
    apply List.map_congr_left
    intro x hx
    have hnx : ¬ Relation.EqvGen J.Adjacent d x := fun hdx =>
      hh (Relation.EqvGen.trans _ _ _ hdx (hinner f hf x hx _ (List.head_mem _)))
    show (if Relation.EqvGen J.Adjacent d x then RelLetter.base 1 else Delta.label x) = _
    rw [if_neg hnx]
  have hrel : ∀ f ∈ relFaces, IsSignedConjugate (RelLetter.listVal '' W)
      (RelLetter.listVal ((FB f).darts.map label')) := by
    intro f hf
    simp only [relFaces, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    rw [hkeep f hf.1 hf.2]
    obtain ⟨C, hC, hCf⟩ := hcover.cell f hf.1
    have hword : C.word = (FB f).darts.map Delta.label := by
      rw [← hCf]
      exact Delta.relatorCell_word C hC
    exact IsSignedConjugate.base ⟨C.word, C.word_mem, by rw [hword]⟩
  have htriv : ∀ f, f ≠ O → f ∉ relFaces →
      RelLetter.listVal ((FB f).darts.map label') = 1 := by
    intro f hf hnrel
    have hh : Relation.EqvGen J.Adjacent d ((FB f).darts.head (FB f).nonempty) := by
      by_contra hh
      exact hnrel (by simp [relFaces, hf, hh])
    apply List.prod_eq_one
    intro z hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have hdx : Relation.EqvGen J.Adjacent d x :=
      Relation.EqvGen.trans _ _ _ hh (hinner f hf _ (List.head_mem _) x hx)
    show (if Relation.EqvGen J.Adjacent d x then RelLetter.base 1 else Delta.label x).val = 1
    rw [if_pos hdx]
    rfl
  have hPVK := planarVanKampen.{u, w, v} (RelLetter.listVal '' W) M Delta.planar label' hlabel' O
    FB relFaces hOrel hrel htriv
  have hOval : RelLetter.listVal ((FB O).darts.map label') =
      RelLetter.listVal (Delta.faceWord O) := by
    have hs : s.map label' = s.map Delta.label := by
      apply List.map_congr_left
      intro x hx
      show (if Relation.EqvGen J.Adjacent d x then RelLetter.base 1 else Delta.label x) = _
      rw [if_neg (hrest x (List.mem_append.mpr (Or.inl hx)))]
    have ht : t.map label' = t.map Delta.label := by
      apply List.map_congr_left
      intro x hx
      show (if Relation.EqvGen J.Adjacent d x then RelLetter.base 1 else Delta.label x) = _
      rw [if_neg (hrest x (List.mem_append.mpr (Or.inr hx)))]
    have hd1 : label' d = RelLetter.base 1 := if_pos (Relation.EqvGen.refl _)
    have he1 : label' e = RelLetter.base 1 := if_pos hde'
    show RelLetter.listVal ((FB O).darts.map label') =
      RelLetter.listVal ((FB O).darts.map Delta.label)
    rw [houter, List.map_append, List.map_append, List.map_cons, List.map_cons, List.map_cons,
      List.map_cons, hs, ht, hd1, he1, HullSC.RelWord.listVal_append,
      HullSC.RelWord.listVal_append, HullSC.RelWord.listVal_cons, HullSC.RelWord.listVal_cons,
      HullSC.RelWord.listVal_cons, HullSC.RelWord.listVal_cons, hlabel, HullSC.RelWord.val_inv,
      mul_inv_cancel_left]
    show RelLetter.listVal (s.map Delta.label) * ((1 : G) * ((1 : G) *
      RelLetter.listVal (t.map Delta.label))) = _
    rw [one_mul, one_mul]
  rw [hOval] at hPVK
  have hbv : Delta.boundaryValue = (RelLetter.listVal (Delta.faceWord O))⁻¹ := by
    rw [DiscDiagram.boundaryValue, DiscDiagram.boundaryWord, HullSC.RelWord.listVal_revInv]
  refine ⟨relFaces.card, ?_, by rw [hbv]; exact hPVK.inv⟩
  have hge_inner : ge ∈ Delta.innerFaces := by
    simp only [DiscDiagram.innerFaces, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    exact hαe_notO
  have hsub : relFaces ⊆ Delta.innerFaces.erase ge := by
    intro f hf
    simp only [relFaces, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    refine Finset.mem_erase.mpr ⟨fun hfe => hf.2 (hfe ▸ hge_head), ?_⟩
    simp only [DiscDiagram.innerFaces, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    exact hf.1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hge_inner] at hcard
  have hpos : 0 < Delta.innerFaces.card := Finset.card_pos.mpr ⟨ge, hge_inner⟩
  rw [hcover.rCellCount_eq_innerFaceCount]
  show relFaces.card < Delta.innerFaces.card
  omega

end Diagram

end PinchLemma

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PinchLemma.split_euler
#audit_axioms GroupApproximation.GGT.VanKampen.PinchLemma.reach_or_reach
#audit_axioms GroupApproximation.GGT.VanKampen.PinchLemma.not_reach_p
#audit_axioms GroupApproximation.GGT.VanKampen.PinchLemma.split_isFaceCycle_rest
#audit_axioms GroupApproximation.GGT.VanKampen.PinchLemma.exists_isRelatorProduct_lt_of_pinch
