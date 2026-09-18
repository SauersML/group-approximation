import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Forward.ConfigBasic

/-!
# One machine step preserves the configuration element (relative form)

Input for `thm:fixed-radical-membership` of `non_mf_group_notes.tex`, forward direction of
Kharlampovich--Myasnikov--Sapir (arXiv:1204.6506) Theorem `tmm`(b), equation `(e000)`.

Let `T` be a normal subgroup of `G(M)` whose elements commute pairwise and which contains
the letters `x_{q_j A_0}`.  Then `c ⊢ d` implies `configElem M c = configElem M d`
(`configElem_eq_of_step_of_abelian`).  On `T` the operations `f * a_i` and `f * A_i` commute
when the letters involved commute (G1, G2), so the operation changed by a step can be
pulled out of the fold and cancelled by the machine relator (G8).
-/

namespace GroupApproximation.Full.Kharlampovich

namespace KMS

namespace Forward

variable {K N : ℕ} (M : Minsky.Machine K N)

/-- The fold of the `f * A_{k+1}` with the factor `k = n` left out. -/
def cOpSkip (n k : Fin K) : KhGroup M → KhGroup M :=
  if k = n then fun f ↦ f else cOp M k

theorem cOpSkip_self (n : Fin K) (f : KhGroup M) : cOpSkip M n n f = f := by
  show (if n = n then fun f ↦ f else cOp M n) f = f
  rw [if_pos (rfl : n = n)]

theorem cOpSkip_of_ne {n k : Fin K} (h : k ≠ n) (f : KhGroup M) :
    cOpSkip M n k f = cOp M k f := by
  show (if k = n then fun f ↦ f else cOp M k) f = cOp M k f
  rw [if_neg h]

section Abelian

variable {T : Subgroup (KhGroup M)} [T.Normal] (hT : ∀ u ∈ T, ∀ v ∈ T, Commute u v)
include hT

theorem sOp_mem (n : Fin K) : ∀ f ∈ (T : Set (KhGroup M)), sOp M n f ∈ (T : Set (KhGroup M)) :=
  (isTMap_khStar hT (kLet M (.a n)) (kLet M (.a' n))).mem

theorem cOp_mem (n : Fin K) : ∀ f ∈ (T : Set (KhGroup M)), cOp M n f ∈ (T : Set (KhGroup M)) :=
  (isTMap_khComm hT (kLet M (.bigA n.succ))).mem

theorem sOp_iterate_mem (g : Fin K → ℕ) (k : Fin K) :
    ∀ f ∈ (T : Set (KhGroup M)), (sOp M k)^[g k] f ∈ (T : Set (KhGroup M)) :=
  iterate_mem (T := (T : Set (KhGroup M))) (F := sOp M k) (sOp_mem M hT k) (g k)

theorem cOpSkip_mem (n k : Fin K) :
    ∀ f ∈ (T : Set (KhGroup M)), cOpSkip M n k f ∈ (T : Set (KhGroup M)) := by
  intro f hf
  by_cases hkn : k = n
  · rw [hkn, cOpSkip_self]
    exact hf
  · rw [cOpSkip_of_ne M hkn]
    exact cOp_mem M hT k f hf

theorem stars_mem (g : Fin K → ℕ) :
    ∀ f ∈ (T : Set (KhGroup M)),
      opFold (fun k ↦ (sOp M k)^[g k]) (List.finRange K) f ∈ (T : Set (KhGroup M)) :=
  opFold_mem (T := (T : Set (KhGroup M))) (G := fun k ↦ (sOp M k)^[g k]) (List.finRange K)
    (fun k _ ↦ sOp_iterate_mem M hT g k)

/-- Stars by `a_{n+1}` and `a_{k+1}` commute on `T`. -/
theorem sOp_iterate_comm (g : Fin K → ℕ) (n k : Fin K) :
    ∀ f ∈ (T : Set (KhGroup M)), (sOp M k)^[g k] (sOp M n f) = sOp M n ((sOp M k)^[g k] f) :=
  iterate_comm (T := (T : Set (KhGroup M))) (F := sOp M k) (H := sOp M n) (sOp_mem M hT k)
    (fun f hf ↦ khStar_khStar_of_commute hT (commute_a_a M n k) (commute_a_a' M n k)
      (commute_a'_a M n k) (commute_a'_a' M n k) hf) (g k)

/-- With glass `n` empty, `f * A_{n+1}` commutes on `T` with every star factor. -/
theorem sOp_iterate_cOp_comm (g : Fin K → ℕ) {n : Fin K} (hz : g n = 0) (k : Fin K) :
    ∀ f ∈ (T : Set (KhGroup M)), (sOp M k)^[g k] (cOp M n f) = cOp M n ((sOp M k)^[g k] f) := by
  intro f hf
  by_cases hkn : k = n
  · rw [hkn, hz, Function.iterate_zero_apply, Function.iterate_zero_apply]
  · exact iterate_comm (T := (T : Set (KhGroup M))) (F := sOp M k) (H := cOp M n)
      (sOp_mem M hT k)
      (fun h hh ↦ (khComm_khStar_of_commute hT (commute_bigA_a M hkn)
        (commute_bigA_a' M hkn) hh).symm) (g k) f hf

theorem cOpSkip_comm (n k : Fin K) :
    ∀ f ∈ (T : Set (KhGroup M)), cOpSkip M n k (cOp M n f) = cOp M n (cOpSkip M n k f) := by
  intro f hf
  by_cases hkn : k = n
  · rw [hkn, cOpSkip_self, cOpSkip_self]
  · rw [cOpSkip_of_ne M hkn, cOpSkip_of_ne M hkn]
    exact khComm_khComm_of_commute hT (commute_bigA_bigA M n.succ k.succ) hf

theorem configElem_step_add {c d : Minsky.Cfg K N} {i j : Fin (N + 1)} {n : Fin K}
    (hx : ∀ j : Fin (N + 1), kLet M (.x j {0}) ∈ (T : Set (KhGroup M)))
    (hr : (i, Minsky.Instr.add n j) ∈ M.prog) (hi : i = c.state) (hdj : d.state = j)
    (hdg : d.glass = Function.update c.glass n (c.glass n + 1)) :
    configElem M c = configElem M d := by
  rw [configElem_eq M c, configElem_eq M d, ← hi, hdj, add_relation M hr]
  refine congrArg (opFold (cOp M) (List.finRange K)) ?_
  rw [opFold_comm (T := (T : Set (KhGroup M))) (G := fun k ↦ (sOp M k)^[c.glass k])
    (H := sOp M n) (List.finRange K) (fun k _ ↦ sOp_iterate_mem M hT c.glass k)
    (fun k _ ↦ sOp_iterate_comm M hT c.glass n k) _ (hx j)]
  refine (opFold_extract (T := (T : Set (KhGroup M))) (G := fun k ↦ (sOp M k)^[d.glass k])
    (G' := fun k ↦ (sOp M k)^[c.glass k]) (H := sOp M n) (n := n) (List.finRange K)
    (List.mem_finRange n) (List.nodup_finRange K) ?_ ?_
    (fun k _ ↦ sOp_iterate_mem M hT c.glass k)
    (fun k _ ↦ sOp_iterate_comm M hT c.glass n k) _ (hx j)).symm
  · intro k _ hkn f
    show (sOp M k)^[d.glass k] f = (sOp M k)^[c.glass k] f
    rw [hdg, Function.update_of_ne hkn]
  · intro f _
    show (sOp M n)^[d.glass n] f = sOp M n ((sOp M n)^[c.glass n] f)
    rw [hdg, Function.update_self, Function.iterate_succ_apply']

theorem configElem_step_sub {c d : Minsky.Cfg K N} {i j : Fin (N + 1)} {n : Fin K}
    (hx : ∀ j : Fin (N + 1), kLet M (.x j {0}) ∈ (T : Set (KhGroup M)))
    (hr : (i, Minsky.Instr.sub n j) ∈ M.prog) (hi : i = c.state) (hpos : 0 < c.glass n)
    (hdj : d.state = j) (hdg : d.glass = Function.update c.glass n (c.glass n - 1)) :
    configElem M c = configElem M d := by
  rw [configElem_eq M c, configElem_eq M d, ← hi, hdj, ← sub_relation M hr]
  refine congrArg (opFold (cOp M) (List.finRange K)) ?_
  rw [opFold_comm (T := (T : Set (KhGroup M))) (G := fun k ↦ (sOp M k)^[d.glass k])
    (H := sOp M n) (List.finRange K) (fun k _ ↦ sOp_iterate_mem M hT d.glass k)
    (fun k _ ↦ sOp_iterate_comm M hT d.glass n k) _ (hx i)]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, c.glass n = m + 1 := ⟨c.glass n - 1, by omega⟩
  refine opFold_extract (T := (T : Set (KhGroup M))) (G := fun k ↦ (sOp M k)^[c.glass k])
    (G' := fun k ↦ (sOp M k)^[d.glass k]) (H := sOp M n) (n := n) (List.finRange K)
    (List.mem_finRange n) (List.nodup_finRange K) ?_ ?_
    (fun k _ ↦ sOp_iterate_mem M hT d.glass k)
    (fun k _ ↦ sOp_iterate_comm M hT d.glass n k) _ (hx i)
  · intro k _ hkn f
    show (sOp M k)^[c.glass k] f = (sOp M k)^[d.glass k] f
    rw [hdg, Function.update_of_ne hkn]
  · intro f _
    show (sOp M n)^[c.glass n] f = sOp M n ((sOp M n)^[d.glass n] f)
    rw [hdg, Function.update_self, hm, Nat.add_sub_cancel, Function.iterate_succ_apply']

theorem configElem_step_zero {c d : Minsky.Cfg K N} {i j : Fin (N + 1)} {n : Fin K}
    (hx : ∀ j : Fin (N + 1), kLet M (.x j {0}) ∈ (T : Set (KhGroup M)))
    (hr : (i, Minsky.Instr.zero n j) ∈ M.prog) (hi : i = c.state) (hz : c.glass n = 0)
    (hdj : d.state = j) (hdg : d.glass = c.glass) :
    configElem M c = configElem M d := by
  have P : ∀ f ∈ (T : Set (KhGroup M)),
      opFold (cOp M) (List.finRange K)
          (opFold (fun k ↦ (sOp M k)^[c.glass k]) (List.finRange K) f) =
        opFold (cOpSkip M n) (List.finRange K)
          (opFold (fun k ↦ (sOp M k)^[c.glass k]) (List.finRange K) (cOp M n f)) := by
    intro f hf
    have hY := stars_mem M hT c.glass f hf
    rw [opFold_extract (T := (T : Set (KhGroup M))) (G := cOp M) (G' := cOpSkip M n)
        (H := cOp M n) (n := n) (List.finRange K) (List.mem_finRange n)
        (List.nodup_finRange K) (fun k _ hkn g ↦ (cOpSkip_of_ne M hkn g).symm)
        (fun g _ ↦ by rw [cOpSkip_self]) (fun k _ ↦ cOpSkip_mem M hT n k)
        (fun k _ ↦ cOpSkip_comm M hT n k) _ hY,
      ← opFold_comm (T := (T : Set (KhGroup M))) (G := cOpSkip M n) (H := cOp M n)
        (List.finRange K) (fun k _ ↦ cOpSkip_mem M hT n k)
        (fun k _ ↦ cOpSkip_comm M hT n k) _ hY,
      opFold_comm (T := (T : Set (KhGroup M))) (G := fun k ↦ (sOp M k)^[c.glass k])
        (H := cOp M n) (List.finRange K) (fun k _ ↦ sOp_iterate_mem M hT c.glass k)
        (fun k _ ↦ sOp_iterate_cOp_comm M hT c.glass hz k) _ hf]
  rw [configElem_eq M c, configElem_eq M d, ← hi, hdj, hdg, P _ (hx i), P _ (hx j),
    zero_relation M hr]

/-- One step of the machine preserves the configuration element, given an abelian normal
subgroup of `G(M)` containing the letters `x_{q_j A_0}`. -/
theorem configElem_eq_of_step_of_abelian
    (hx : ∀ j : Fin (N + 1), kLet M (.x j {0}) ∈ (T : Set (KhGroup M)))
    {c d : Minsky.Cfg K N} (h : M.Step c d) : configElem M c = configElem M d := by
  obtain ⟨⟨i, ins⟩, hr, hi, hfire⟩ := h
  have hi' : i = c.state := hi
  cases ins with
  | add n j =>
    have hf : d.state = j ∧ d.glass = Function.update c.glass n (c.glass n + 1) := hfire
    exact configElem_step_add M hT hx hr hi' hf.1 hf.2
  | sub n j =>
    have hf : 0 < c.glass n ∧ d.state = j ∧
        d.glass = Function.update c.glass n (c.glass n - 1) := hfire
    exact configElem_step_sub M hT hx hr hi' hf.1 hf.2.1 hf.2.2
  | zero n j =>
    have hf : c.glass n = 0 ∧ d.state = j ∧ d.glass = c.glass := hfire
    exact configElem_step_zero M hT hx hr hi' hf.1 hf.2.1 hf.2.2

end Abelian

end Forward

end KMS

end GroupApproximation.Full.Kharlampovich
