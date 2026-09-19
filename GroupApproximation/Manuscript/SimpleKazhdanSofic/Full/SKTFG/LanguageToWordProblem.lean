import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKTFG.ThreeCycleWitness
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKTFG.WordProblemToLanguage
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LanguageReducesToWordProblem
import GroupApproximation.Meta.AxiomGuard

/-!
# The word problem of the derived topological full group computes `L(X)`

SK row `e5932a45f053` (tex l.724–726, Grigorchuk–Medynets, Thm 1.1(3)), the direction "if the word
problem is solvable then `L(X)` is recursive", as a Turing reduction to the word problem in the
generators `genFam` over the cylinders on `[0, N]`, with `N ≥ 2R + 1` for a separation radius `R`.

* `towerPerm_cyl_succ_eq`: the three-cycle `τ` on the tower over `cyl z 0 (c + 1)` is the
  commutator of the witnesses `pick τ` on the towers over `cyl z 0 c` and `cyl (z (1 + ·)) 0 c`
  (`commutator_towerPerm_localize`).
* `shape d τ` is the resulting word of depth `d`, in letters `(j, label)` that stand for the
  generator over the window of length `N + 1` at `j`. Substituted into `z`, it is the three-cycle
  `τ` on the tower over `cyl z 0 (N + d)` (`wordValue_substWord_shape`).
* The three-cycle `(0 1 2)` on the tower over a cylinder is trivial iff the cylinder is empty
  (`towerPerm_eq_one_iff`). So a word `v` of length at least `N + 1` lies in `L(X)` iff its word
  is nontrivial, and a shorter word lies in `L(X)` iff one of its extensions to length `N + 1`
  does. One truth-table query per extension decides `L(X)`.
-/

namespace GroupApproximation.Full.SKTFG

open GroupApproximation.SimpleKazhdanSofic GroupApproximation.CylinderTables
open GroupApproximation.Full.StepanovMatui.Matui
open SymbolicDynamics.FullShift Equiv Encodable
open scoped commutatorElement

/-! ## Tower actions of three-cycles -/

section Tower

variable {X : Type*} {f₀ : Perm X}

/-- A tower action moving level `0` is trivial iff the base is empty, for an aperiodic `f₀`. -/
theorem towerPerm_eq_one_iff (hfree : ∀ j : ℤ, j ≠ 0 → ∀ y : X, (f₀ ^ j) y ≠ y) {B : Set X}
    (hd : TowerDisj f₀ B 4) {σ : Perm (Fin 5)} (hσ : σ 0 ≠ 0) :
    towerPerm f₀ B (towerLevels 4) hd σ = 1 ↔ B = ∅ := by
  constructor
  · intro h
    refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
    have h0 : (f₀ ^ (-towerLevels 4 0)) x ∈ B := by simpa [towerLevels_val] using hx
    have h1 := DFunLike.congr_fun h x
    rw [towerPerm_apply, towerFun_of_mem hd h0, Perm.one_apply] at h1
    have hne : towerLevels 4 (σ 0) - towerLevels 4 0 ≠ 0 := by
      rw [towerLevels_val, towerLevels_val, sub_ne_zero, Ne, Nat.cast_inj]
      exact fun e => hσ (Fin.ext e)
    exact hfree _ hne x h1
  · intro h
    refine Equiv.ext fun x => ?_
    rw [towerPerm_apply, towerFun_of_not, Perm.one_apply]
    rintro ⟨i, hi⟩
    rw [h] at hi
    exact hi

end Tower

section Step

variable {A : Type} [TopologicalSpace A] (S : Subshift A ℤ)

/-- **One step**: the three-cycle `τ` on the tower over `cyl z 0 (c + 1)` is the commutator of the
witnesses of `τ` on the towers over `cyl z 0 c` and `cyl (z (1 + ·)) 0 c`. -/
theorem towerPerm_cyl_succ_eq {R : ℕ} (hR : SepRadius S 5 R) {z : ℤ → A} {c c' : ℤ}
    (hc' : c' = c + 1) (hc : 1 + 2 * (R : ℤ) ≤ c) {t : Fin 125} (ht : LabValid t)
    (hdU : TowerDisj (SimpleKazhdanSofic.subshiftHomeo S).toEquiv (cyl S z 0 c) 4)
    (hdV : TowerDisj (SimpleKazhdanSofic.subshiftHomeo S).toEquiv
      (cyl S (fun n => z (1 + n)) 0 c) 4)
    (hdW : TowerDisj (SimpleKazhdanSofic.subshiftHomeo S).toEquiv (cyl S z 0 c') 4) :
    towerPerm (SimpleKazhdanSofic.subshiftHomeo S).toEquiv (cyl S z 0 c') (towerLevels 4) hdW
        (labPerm t) =
      ⁅towerPerm (SimpleKazhdanSofic.subshiftHomeo S).toEquiv (cyl S z 0 c) (towerLevels 4) hdU
          (labPerm (pick t).1),
        towerPerm (SimpleKazhdanSofic.subshiftHomeo S).toEquiv (cyl S (fun n => z (1 + n)) 0 c)
          (towerLevels 4) hdV (labPerm (pick t).2)⁆ := by
  subst hc'
  obtain ⟨-, -, hcomm⟩ := pick_spec t ht
  have hU5 : SepK (SimpleKazhdanSofic.subshiftHomeo S).toEquiv (cyl S z 0 c) 5 :=
    cyl_sepK S hR (by omega)
  have hV5 : SepK (SimpleKazhdanSofic.subshiftHomeo S).toEquiv
      (cyl S (fun n => z (1 + n)) 0 c) 5 := cyl_sepK S hR (by omega)
  have hW5 : SepK (SimpleKazhdanSofic.subshiftHomeo S).toEquiv (cyl S z 0 (c + 1)) 5 :=
    cyl_sepK S hR (by omega)
  have hUV := cyl_cross S hR le_rfl (z := z) (a := 0) (c := c) (by omega)
  have hWd := mem_cyl_succ_iff S (z := z) (show (0 : ℤ) ≤ c by omega)
  have hWd6 : TowerDisj (SimpleKazhdanSofic.subshiftHomeo S).toEquiv (cyl S z 0 (c + 1)) 5 :=
    towerDisj_of_sepK hW5
  have hE0 : ∀ i : Fin 5, towerLevels 5 i.castSucc = towerLevels 4 i + 0 := fun i => by
    rw [towerLevels_val, towerLevels_val, Fin.val_castSucc, add_zero]
  have hB0 : ∀ x, x ∈ cyl S z 0 (c + 1) ↔
      ((SimpleKazhdanSofic.subshiftHomeo S).toEquiv ^ (0 : ℤ)) x ∈ cyl S z 0 (c + 1) :=
    fun x => by rw [zpow_zero, Equiv.Perm.one_apply]
  rw [towerPerm_eq_of_sub hdW hWd6 Fin.castSucc 0 hE0 hB0 (labPerm t) (labPermC t)
      (labPermC_castSucc t) (labPermC_of_not_castSucc t), ← hcomm,
    ← commutator_towerPerm_localize hU5 hV5 hUV hWd hdU hdV hWd6 (labPerm (pick t).1)
      (labPerm (pick t).2) (labPermC (pick t).1) (labPermS (pick t).2)
      (labPermC_castSucc _) (labPermC_last _) (labPermS_succ _) (labPermS_zero _)]

end Step

/-! ## Shapes -/

section Shape

/-- A letter of a shape: a window start, a label, and a sign. -/
abbrev ShapeLetter : Type := (ℕ × Fin 125) × Bool

/-- The window starts of a shape, moved by one. -/
def shapeShift (w : List ShapeLetter) : List ShapeLetter :=
  w.map fun x => ((x.1.1 + 1, x.1.2), x.2)

/-- One step of the shape table: the commutator of the witnesses. -/
def shapeStep (tab : Fin 125 → List ShapeLetter) (i : Fin 125) : List ShapeLetter :=
  wordComm (tab (pick i).1) (shapeShift (tab (pick i).2))

/-- The shape table of depth `0`: one letter at the window `0`. -/
def shapeInit (i : Fin 125) : List ShapeLetter := [((0, i), true)]

/-- The shape table of depth `d`. -/
def shape (d : ℕ) : Fin 125 → List ShapeLetter := shapeStep^[d] shapeInit

theorem shape_succ (d : ℕ) (i : Fin 125) :
    shape (d + 1) i = wordComm (shape d (pick i).1) (shapeShift (shape d (pick i).2)) := by
  rw [shape, Function.iterate_succ_apply']
  rfl

theorem primrec_shapeShift : Primrec shapeShift :=
  (Primrec.list_map Primrec.id (Primrec.pair (Primrec.pair
    (Primrec.succ.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
    (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
    fun _ => rfl

theorem primrec_shapeStep : Primrec shapeStep := by
  refine Primrec.fin_curry.2 ?_
  show Primrec fun p : (Fin 125 → List ShapeLetter) × Fin 125 => shapeStep p.1 p.2
  exact (LanguageReduction.primrec₂_wordComm.comp
    (Primrec.fin_app.comp Primrec.fst
      ((Primrec.dom_finite fun i : Fin 125 => (pick i).1).comp Primrec.snd))
    (primrec_shapeShift.comp (Primrec.fin_app.comp Primrec.fst
      ((Primrec.dom_finite fun i : Fin 125 => (pick i).2).comp Primrec.snd)))).of_eq
    fun _ => rfl

theorem primrec_shape_rootLab : Primrec fun d : ℕ => shape d rootLab :=
  (Primrec.fin_app.comp (Primrec.nat_iterate Primrec.id (Primrec.const shapeInit)
    (primrec_shapeStep.comp Primrec.snd).to₂) (Primrec.const rootLab)).of_eq fun _ => rfl

end Shape

/-! ## Shapes substituted into windows -/

section Words

variable {A : Type}

/-- The even permutation of a label: its three-cycle if the label is valid, else `1`. -/
def labAlt (t : Fin 125) : alternatingGroup (Fin 5) :=
  if h : LabValid t then ⟨labPerm t, labPerm_mem_alternatingGroup h⟩ else 1

theorem coe_labAlt {t : Fin 125} (h : LabValid t) : (labAlt t : Perm (Fin 5)) = labPerm t := by
  rw [labAlt, dif_pos h]

variable {N k : ℕ} (e : ((Finset.Icc (0 : ℤ) N → A) × alternatingGroup (Fin 5)) ≃ Fin k)

/-- The generator of the window of `z` at `j`, with the label `t`. -/
def letterIdx (z : ℤ → A) (j : ℕ) (t : Fin 125) : Fin k :=
  e (fun n : Finset.Icc (0 : ℤ) N => z ((j : ℤ) + n), labAlt t)

/-- A shape substituted into `z`. -/
def substWord (z : ℤ → A) (w : List ShapeLetter) : List (Fin k × Bool) :=
  w.map fun x => (letterIdx e z x.1.1 x.1.2, x.2)

theorem letterIdx_succ (z : ℤ → A) (j : ℕ) (t : Fin 125) :
    letterIdx e z (j + 1) t = letterIdx e (fun n => z (1 + n)) j t := by
  have h : (fun n : Finset.Icc (0 : ℤ) N => z (((j + 1 : ℕ) : ℤ) + n)) =
      fun n => z (1 + ((j : ℤ) + n)) := funext fun n => by
    exact congrArg z (by push_cast; ring)
  exact congrArg (fun w => e (w, labAlt t)) h

theorem substWord_shapeShift (z : ℤ → A) (w : List ShapeLetter) :
    substWord e z (shapeShift w) = substWord e (fun n => z (1 + n)) w := by
  rw [substWord, substWord, shapeShift, List.map_map]
  exact List.map_congr_left fun x _ => by
    show (letterIdx e z (x.1.1 + 1) x.1.2, x.2) =
      (letterIdx e (fun n => z (1 + n)) x.1.1 x.1.2, x.2)
    rw [letterIdx_succ]

theorem substWord_wordComm (z : ℤ → A) (a b : List ShapeLetter) :
    substWord e z (wordComm a b) = wordComm (substWord e z a) (substWord e z b) := by
  simp [substWord, wordComm, wordInv, Function.comp_def]

variable [TopologicalSpace A] (S : Subshift A ℤ)

theorem genPerm_eq_of_disj (w : Finset.Icc (0 : ℤ) N → A)
    (σ : alternatingGroup (Fin 5))
    (h : TowerDisj (SimpleKazhdanSofic.subshiftHomeo S).toEquiv (cylW S N w) 4) :
    genPerm S N (w, σ) =
      towerPerm (SimpleKazhdanSofic.subshiftHomeo S).toEquiv (cylW S N w) (towerLevels 4) h σ :=
  dif_pos h

/-- **The value of a shape**: the three-cycle of the root label on the tower over the cylinder on
`[0, N + d]`. -/
theorem wordValue_substWord_shape {R : ℕ} (hR : SepRadius S 5 R) (hN : 2 * R + 1 ≤ N)
    (hDG : derivedFullGroupSubshift S = Subgroup.closure (gens S N)) (d : ℕ) :
    ∀ (z : ℤ → A) (t : Fin 125), LabValid t →
      ∀ hd : TowerDisj (SimpleKazhdanSofic.subshiftHomeo S).toEquiv
        (cyl S z 0 ((N : ℤ) + (d : ℤ))) 4,
        wordValue (fun i => (genFam S hDG e i : Perm S.carrier)) (substWord e z (shape d t)) =
          towerPerm (SimpleKazhdanSofic.subshiftHomeo S).toEquiv (cyl S z 0 ((N : ℤ) + (d : ℤ)))
            (towerLevels 4) hd (labPerm t) := by
  induction d with
  | zero =>
    intro z t ht hd
    show wordValue _ [(letterIdx e z 0 t, true)] = _
    rw [LanguageReduction.wordValue_singleton_true]
    show genPerm S N (e.symm (e _)) = _
    rw [Equiv.symm_apply_apply]
    have hW : cylW S N (fun n : Finset.Icc (0 : ℤ) N => z (((0 : ℕ) : ℤ) + n)) =
        cyl S z 0 ((N : ℤ) + ((0 : ℕ) : ℤ)) := by
      rw [Nat.cast_zero, add_zero]
      exact (cylW_eq S N fun m => z ((0 : ℤ) + m)).trans
        (cyl_eq_of_eq S (fun m => congrArg z (zero_add m)) 0 N)
    have hdW : TowerDisj (SimpleKazhdanSofic.subshiftHomeo S).toEquiv
        (cylW S N (fun n : Finset.Icc (0 : ℤ) N => z (((0 : ℕ) : ℤ) + n))) 4 := by
      rw [hW]
      exact hd
    rw [genPerm_eq_of_disj S _ _ hdW, coe_labAlt ht]
    exact towerPerm_congr hdW hd (fun i x => by rw [hW]) (fun _ _ => rfl) _
  | succ d ih =>
    intro z t ht hd
    obtain ⟨hα, hβ, -⟩ := pick_spec t ht
    have hdU : TowerDisj (SimpleKazhdanSofic.subshiftHomeo S).toEquiv
        (cyl S z 0 ((N : ℤ) + (d : ℤ))) 4 :=
      towerDisj_of_sepK ((cyl_sepK S hR (by omega)).mono (by norm_num))
    have hdV : TowerDisj (SimpleKazhdanSofic.subshiftHomeo S).toEquiv
        (cyl S (fun n => z (1 + n)) 0 ((N : ℤ) + (d : ℤ))) 4 :=
      towerDisj_of_sepK ((cyl_sepK S hR (by omega)).mono (by norm_num))
    rw [shape_succ, substWord_wordComm, wordValue_wordComm, substWord_shapeShift,
      ih z _ hα hdU, ih (fun n => z (1 + n)) _ hβ hdV, ← commutatorElement_def]
    exact (towerPerm_cyl_succ_eq S hR (by push_cast; ring) (by omega) ht hdU hdV hd).symm

end Words

/-! ## Words of the language -/

section Language

variable {A : Type} [TopologicalSpace A] (S : Subshift A ℤ)

theorem mem_language_iff_listLanguage {v : List A} :
    v ∈ language S ↔ v ∈ listLanguage S.carrier :=
  mem_listLanguage_iff.symm

/-- The cylinder of `v` on `[0, |v| - 1]` is nonempty iff `v ∈ L(X)`. -/
theorem cyl_nonempty_iff (a₀ : A) (v : List A) {c : ℤ} (hc : (v.length : ℤ) = c + 1) :
    (cyl S (fun n => v.getD n.toNat a₀) 0 c).Nonempty ↔ v ∈ language S := by
  rw [mem_language_iff_listLanguage]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x.1, x.2, fun t => ?_⟩
    have ht := t.isLt
    rw [hx (t : ℕ) (by omega) (by omega)]
    show v.getD ((t : ℕ) : ℤ).toNat a₀ = v.get t
    rw [Int.toNat_natCast, List.getD_eq_getElem _ _ ht, List.get_eq_getElem]
  · rintro ⟨x, hxS, hx⟩
    refine ⟨⟨x, hxS⟩, fun n h0 h1 => ?_⟩
    have hm : n.toNat < v.length := by omega
    have e1 : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg h0
    have h2 : x ((n.toNat : ℕ) : ℤ) = v.get ⟨n.toNat, hm⟩ := hx ⟨n.toNat, hm⟩
    rw [e1] at h2
    show x n = v.getD n.toNat a₀
    rw [h2, List.getD_eq_getElem _ _ hm, List.get_eq_getElem]

omit [TopologicalSpace A] in
/-- A word is in the language iff one of its extensions of length `m` is. -/
theorem mem_listLanguage_iff_exists_append {L : List A} (hL : ∀ a, a ∈ L) {X : Set (ℤ → A)}
    (v : List A) (m : ℕ) :
    v ∈ listLanguage X ↔ ∃ u ∈ allWords L m, v ++ u ∈ listLanguage X := by
  constructor
  · rintro ⟨x, hx, h⟩
    refine ⟨List.ofFn fun i : Fin m => x ((v.length + (i : ℕ) : ℕ) : ℤ),
      (mem_allWords hL).2 (List.length_ofFn), x, hx, fun t => ?_⟩
    by_cases ht : (t : ℕ) < v.length
    · rw [List.get_eq_getElem, List.getElem_append_left ht]
      exact (h ⟨t, ht⟩).trans List.get_eq_getElem
    · have ht' : v.length ≤ (t : ℕ) := Nat.le_of_not_lt ht
      rw [List.get_eq_getElem, List.getElem_append_right ht', List.getElem_ofFn]
      show x ((t : ℕ) : ℤ) = x ((v.length + ((t : ℕ) - v.length) : ℕ) : ℤ)
      exact congrArg x (by omega)
  · rintro ⟨u, -, x, hx, h⟩
    refine ⟨x, hx, fun t => ?_⟩
    have ht : (t : ℕ) < (v ++ u).length := by
      rw [List.length_append]
      have := t.isLt
      omega
    have h2 := h ⟨t, ht⟩
    rw [List.get_eq_getElem, List.getElem_append_left t.isLt] at h2
    rw [List.get_eq_getElem]
    exact h2

theorem mem_language_iff_exists_append {L : List A} (hL : ∀ a, a ∈ L) (v : List A) (m : ℕ) :
    v ∈ language S ↔ ∃ u ∈ allWords L m, v ++ u ∈ language S := by
  simp only [mem_language_iff_listLanguage]
  exact mem_listLanguage_iff_exists_append hL v m

end Language

/-! ## The reduction -/

section Reduction

variable {A : Type} [TopologicalSpace A] [DiscreteTopology A] [Finite A] (S : Subshift A ℤ)
variable {N k : ℕ} (e : ((Finset.Icc (0 : ℤ) N → A) × alternatingGroup (Fin 5)) ≃ Fin k)

/-- A word of length at least `N + 1` lies in `L(X)` iff its shape word is nontrivial. -/
theorem wordValue_substWord_ne_one_iff (hinf : Infinite S.carrier)
    (hmin : SimpleKazhdanSofic.IsMinimal S) {R : ℕ} (hR : SepRadius S 5 R) (hN : 2 * R + 1 ≤ N)
    (hDG : derivedFullGroupSubshift S = Subgroup.closure (gens S N)) (a₀ : A) (v : List A)
    (hv : N + 1 ≤ v.length) :
    ¬ wordValue (genFam S hDG e)
        (substWord e (fun n => v.getD n.toNat a₀) (shape (v.length - (N + 1)) rootLab)) = 1 ↔
      v ∈ language S := by
  have hd : TowerDisj (SimpleKazhdanSofic.subshiftHomeo S).toEquiv
      (cyl S (fun n => v.getD n.toNat a₀) 0 ((N : ℤ) + ((v.length - (N + 1) : ℕ) : ℤ))) 4 :=
    towerDisj_of_sepK ((cyl_sepK S hR (by omega)).mono (by norm_num))
  have h1 : ∀ w : List (Fin k × Bool), wordValue (genFam S hDG e) w = 1 ↔
      wordValue (fun i => (genFam S hDG e i : Perm S.carrier)) w = 1 := fun w => by
    rw [← coe_wordValue]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [h1, wordValue_substWord_shape e S hR hN hDG _ _ rootLab rootLab_valid hd,
    towerPerm_eq_one_iff (fun j hj y => SK05.subshiftHomeo_zpow_apply_ne_self S hinf hmin hj y)
      hd labPerm_rootLab_zero]
  exact Set.nonempty_iff_ne_empty.symm.trans (cyl_nonempty_iff S a₀ v (by omega))

end Reduction

/-! ## Primitive recursive words -/

section Primrec

variable {A : Type} {N k : ℕ} (e : ((Finset.Icc (0 : ℤ) N → A) × alternatingGroup (Fin 5)) ≃ Fin k)

/-- The generator of a window, given as a function on `Fin (N + 1)`, with a label. -/
def winIdx (p : (Fin (N + 1) → A) × Fin 125) : Fin k :=
  e (fun n : Finset.Icc (0 : ℤ) N =>
    p.1 ⟨(n : ℤ).toNat, by have := Finset.mem_Icc.mp n.2; omega⟩, labAlt p.2)

/-- The shape word of the list `v`, read off the list. -/
def bigWordL (a₀ : A) (v : List A) : List (Fin k × Bool) :=
  (shape (v.length - (N + 1)) rootLab).map fun x =>
    (winIdx e (fun i : Fin (N + 1) => v.getD (x.1.1 + i) a₀, x.1.2), x.2)

theorem letterIdx_getD (a₀ : A) (v : List A) (j : ℕ) (t : Fin 125) :
    letterIdx e (fun n => v.getD n.toNat a₀) j t =
      winIdx e (fun i : Fin (N + 1) => v.getD (j + i) a₀, t) := by
  have h : (fun n : Finset.Icc (0 : ℤ) N => v.getD ((j : ℤ) + n).toNat a₀) =
      fun n => v.getD (j + (n : ℤ).toNat) a₀ := funext fun n => by
    have := (Finset.mem_Icc.mp n.2).1
    exact congrArg (fun i => v.getD i a₀) (by omega)
  exact congrArg (fun w => e (w, labAlt t)) h

theorem bigWordL_eq (a₀ : A) (v : List A) :
    bigWordL e a₀ v =
      substWord e (fun n => v.getD n.toNat a₀) (shape (v.length - (N + 1)) rootLab) :=
  List.map_congr_left fun x _ => by
    show (winIdx e (fun i : Fin (N + 1) => v.getD (x.1.1 + i) a₀, x.1.2), x.2) =
      (letterIdx e (fun n => v.getD n.toNat a₀) x.1.1 x.1.2, x.2)
    rw [letterIdx_getD]

theorem primrec_bigWordL [Primcodable A] [Finite A] (a₀ : A) : Primrec (bigWordL e a₀) := by
  have hwin2 : Primrec₂ fun (p : List A × ShapeLetter) (i : Fin (N + 1)) =>
      p.1.getD (p.2.1.1 + i) a₀ :=
    (Primrec.list_getD a₀).comp (Primrec.fst.comp Primrec.fst)
      (Primrec.nat_add.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.fin_val.comp Primrec.snd))
  have hwin : Primrec fun p : List A × ShapeLetter =>
      fun i : Fin (N + 1) => p.1.getD (p.2.1.1 + i) a₀ := Primrec.fin_curry.2 hwin2
  have hidx : Primrec fun p : List A × ShapeLetter =>
      (winIdx e (fun i : Fin (N + 1) => p.1.getD (p.2.1.1 + i) a₀, p.2.1.2), p.2.2) :=
    Primrec.pair ((Primrec.dom_finite (winIdx e)).comp
      (Primrec.pair hwin (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_map (primrec_shape_rootLab.comp
    (Primrec.nat_sub.comp Primrec.list_length (Primrec.const (N + 1)))) hidx.to₂).of_eq
    fun _ => rfl

end Primrec

/-! ## `L(X) ≤_T WP` -/

section Main

variable {A : Type} [TopologicalSpace A] [DiscreteTopology A] (S : Subshift A ℤ)
variable {N k : ℕ} (e : ((Finset.Icc (0 : ℤ) N → A) × alternatingGroup (Fin 5)) ≃ Fin k)

open Classical in
/-- **The word problem of `[[σ]]'` computes `L(X)`**, in the generators `genFam`: a word of length
at least `N + 1` is decided by one query, a shorter one by one query per extension to length
`N + 1`. -/
theorem turingReducible_language_genFam [Fintype A] [Primcodable A] (hinf : Infinite S.carrier)
    (hmin : SimpleKazhdanSofic.IsMinimal S) {R : ℕ} (hR : SepRadius S 5 R) (hN : 2 * R + 1 ≤ N)
    (hDG : derivedFullGroupSubshift S = Subgroup.closure (gens S N)) :
    TuringReducible (languageOracle S) (wordProblemOracle (genFam S hDG e)) := by
  obtain ⟨x₀⟩ : Nonempty S.carrier := by
    haveI := hinf
    infer_instance
  obtain ⟨a₀⟩ : Nonempty A := ⟨x₀.1 0⟩
  obtain ⟨L, hL⟩ : ∃ L : List A, ∀ a, a ∈ L :=
    ⟨Finset.univ.toList, fun a => Finset.mem_toList.2 (Finset.mem_univ a)⟩
  let gt : ℕ → ℕ := fun m =>
    if ∃ w : List (Fin k × Bool), decode m = some w ∧ wordValue (genFam S hDG e) w = 1 then 1
    else 0
  have hgt : ∀ w : List (Fin k × Bool),
      gt (encode w) = if wordValue (genFam S hDG e) w = 1 then 1 else 0 := by
    intro w
    simp [gt, Encodable.encodek]
  have hF : Primrec fun v : List A =>
      (allWords L (N + 1 - v.length)).map fun u => encode (bigWordL e a₀ (v ++ u)) :=
    Primrec.list_map ((primrec_allWords L).comp
      (Primrec.nat_sub.comp (Primrec.const (N + 1)) Primrec.list_length))
      (Primrec.encode.comp ((primrec_bigWordL e a₀).comp
        (Primrec.list_append.comp Primrec.fst Primrec.snd))).to₂
  have hall : Primrec fun l : List ℕ => l.all fun a => decide (a = 1) :=
    (Primrec.list_foldr Primrec.id (Primrec.const true)
      (Primrec.and.comp ((Primrec.eq (α := ℕ)).decide.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.const 1)) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
      fun l => (all_eq_foldr l _).symm
  refine OracleTruthTable.turingReducible_of_truthTable (gt := gt) (fun m => rfl)
    (Q := fun n => ((decode n : Option (List A)).map fun v =>
      (allWords L (N + 1 - v.length)).map fun u => encode (bigWordL e a₀ (v ++ u))).getD [])
    (Primrec.option_getD.comp (Primrec.option_map Primrec.decode (hF.comp Primrec.snd).to₂)
      (Primrec.const []))
    (D := fun _ answers => bif answers.all (fun a => decide (a = 1)) then 0 else 1)
    (Primrec.cond (hall.comp Primrec.snd) (Primrec.const 0) (Primrec.const 1)) fun n => ?_
  show Part.some (if ∃ v : List A, decode n = some v ∧ v ∈ language S then 1 else 0) = _
  congr 1
  cases hd : (decode n : Option (List A)) with
  | none => simp
  | some v =>
    show (if ∃ v' : List A, some v = some v' ∧ v' ∈ language S then 1 else 0) =
      (bif (((allWords L (N + 1 - v.length)).map fun u => encode (bigWordL e a₀ (v ++ u))).map
        gt).all (fun a => decide (a = 1)) then 0 else 1)
    have hex : (∃ v' : List A, some v = some v' ∧ v' ∈ language S) ↔ v ∈ language S :=
      ⟨fun ⟨_, h, h'⟩ => Option.some.inj h ▸ h', fun h => ⟨v, rfl, h⟩⟩
    have hans : ((allWords L (N + 1 - v.length)).map fun u =>
        encode (bigWordL e a₀ (v ++ u))).map gt =
        (allWords L (N + 1 - v.length)).map fun u => if v ++ u ∈ language S then 0 else 1 := by
      rw [List.map_map]
      refine List.map_congr_left fun u hu => ?_
      have hlen : N + 1 ≤ (v ++ u).length := by
        rw [List.length_append, (mem_allWords hL).1 hu]
        omega
      have hw := wordValue_substWord_ne_one_iff S e hinf hmin hR hN hDG a₀ (v ++ u) hlen
      show gt (encode (bigWordL e a₀ (v ++ u))) = if v ++ u ∈ language S then 0 else 1
      rw [hgt, bigWordL_eq]
      by_cases hmem : v ++ u ∈ language S
      · rw [if_pos hmem, if_neg (hw.2 hmem)]
      · rw [if_neg hmem, if_pos (not_not.1 (mt hw.1 hmem))]
    rw [hans]
    by_cases hv : v ∈ language S
    · obtain ⟨u, hu, huv⟩ := (mem_language_iff_exists_append S hL v (N + 1 - v.length)).1 hv
      have hfalse : ((allWords L (N + 1 - v.length)).map fun u =>
          if v ++ u ∈ language S then 0 else 1).all (fun a => decide (a = 1)) = false := by
        rw [Bool.eq_false_iff]
        intro h
        rw [List.all_eq_true] at h
        have h0 := h 0 (List.mem_map.2 ⟨u, hu, if_pos huv⟩)
        exact absurd (of_decide_eq_true h0) zero_ne_one
      rw [if_pos (hex.2 hv), hfalse, cond_false]
    · have htrue : ((allWords L (N + 1 - v.length)).map fun u =>
          if v ++ u ∈ language S then 0 else 1).all (fun a => decide (a = 1)) = true := by
        rw [List.all_eq_true]
        intro a ha
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ha
        have hnot : v ++ u ∉ language S := fun h =>
          hv ((mem_language_iff_exists_append S hL v _).2 ⟨u, hu, h⟩)
        simp [hnot]
      rw [if_neg fun h => hv (hex.1 h), htrue, cond_true]

end Main

end GroupApproximation.Full.SKTFG

#audit_axioms GroupApproximation.Full.SKTFG.wordValue_substWord_shape
#audit_axioms GroupApproximation.Full.SKTFG.turingReducible_language_genFam
