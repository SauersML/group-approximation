import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Insert
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Minsky

/-!
# Words of the KMS model group and their machine classes

Input for the "if" direction of KMS Theorem `tmm`(b) (`l654`, `l789` of
Kharlampovich--Myasnikov--Sapir, arXiv:1204.6506, Sec. 4.1), used in
`thm:fixed-radical-membership` of `non_mf_group_notes.tex`.

The model group acts on functions on pairs `(v, c)`, where `c` is a class of
words `q_j a^{(m)} ∏_{i ∈ S} A_i`.  Here a word is a state `j`, a glass vector
`m` and a flag set `S ⊆ {0, …, K}`.  Two words are related (`R`) when they carry
the same flags, `A_0` is among them, and one machine step takes the
configuration of the first to that of the second.  A zero test on glass `n`
additionally needs the flag `A_{n+1}`.

The appends `appA n`, `appT n` (append `a_{n+1}` or `ã_{n+1}` when allowed) and
`appBig i` (append `A_i`) respect `R`, so they descend to classes.  An
equivalence of words gives the machine equivalence `≡_M` of their
configurations (`equiv_of_eqvGen`).
-/

namespace GroupApproximation.Full.Kharlampovich

namespace KMS

namespace Backward

variable {K N : ℕ}

/-- A word `q_j a_1^{(m_1)} ⋯ a_K^{(m_K)} ∏_{i ∈ S} A_i` of the model (KMS `l654`). -/
structure Wd (K N : ℕ) : Type where
  /-- The state `j`. -/
  state : Fin (N + 1)
  /-- The glass vector `m`. -/
  glass : Fin K → ℕ
  /-- The flag set `S`. -/
  flags : Finset (Fin (K + 1))

/-- One more coin in glass `n`. -/
def bump (m : Fin K → ℕ) (n : Fin K) (k : Fin K) : ℕ :=
  if k = n then m k + 1 else m k

/-- The extra flag a zero test on glass `n` needs: `A_{n+1}`. -/
def ZeroFlag : Minsky.Instr K N → Finset (Fin (K + 1)) → Prop
  | .zero n _, S => n.succ ∈ S
  | .add _ _, _ => True
  | .sub _ _, _ => True

/-- One machine step between words with the same flags, containing `A_0`. -/
def R (M : Minsky.Machine K N) (w w' : Wd K N) : Prop :=
  w'.flags = w.flags ∧ (0 : Fin (K + 1)) ∈ w.flags ∧
    ∃ r ∈ M.prog, r.1 = w.state ∧
      r.2.Fires ⟨w.state, w.glass⟩ ⟨w'.state, w'.glass⟩ ∧ ZeroFlag r.2 w.flags

theorem zeroFlag_mono {S T : Finset (Fin (K + 1))} (hST : S ⊆ T) {r : Minsky.Instr K N}
    (h : ZeroFlag r S) : ZeroFlag r T := by
  cases r with
  | add => trivial
  | sub => trivial
  | zero n _ => exact Finset.mem_of_subset hST h

/-- Adding a coin to a glass that the instruction does not zero-test commutes
with firing. -/
theorem fires_bump {n : Fin K} {S : Finset (Fin (K + 1))} (hn : n.succ ∉ S)
    {r : Minsky.Instr K N} {c d : Minsky.Cfg K N} (hz : ZeroFlag r S) (h : r.Fires c d) :
    r.Fires ⟨c.state, bump c.glass n⟩ ⟨d.state, bump d.glass n⟩ := by
  cases r with
  | add n0 j =>
    obtain ⟨hs, hg⟩ := h
    show d.state = j ∧
      bump d.glass n = Function.update (bump c.glass n) n0 (bump c.glass n n0 + 1)
    refine ⟨hs, ?_⟩
    rw [hg]
    funext k
    simp only [bump, Function.update_apply]
    grind
  | sub n0 j =>
    obtain ⟨hpos, hs, hg⟩ := h
    show 0 < bump c.glass n n0 ∧ d.state = j ∧
      bump d.glass n = Function.update (bump c.glass n) n0 (bump c.glass n n0 - 1)
    refine ⟨?_, hs, ?_⟩
    · show 0 < (if n0 = n then c.glass n0 + 1 else c.glass n0)
      split_ifs <;> omega
    · rw [hg]
      funext k
      simp only [bump, Function.update_apply]
      grind
  | zero n0 j =>
    obtain ⟨hz0, hs, hg⟩ := h
    have hne : n0 ≠ n := by
      rintro rfl
      exact hn hz
    show bump c.glass n n0 = 0 ∧ d.state = j ∧ bump d.glass n = bump c.glass n
    refine ⟨?_, hs, ?_⟩
    · show (if n0 = n then c.glass n0 + 1 else c.glass n0) = 0
      rw [if_neg hne]
      exact hz0
    · rw [hg]

/-! ## Appends -/

/-- Append `a_{n+1}`: one more coin in glass `n`, unless the flag `A_{n+1}` is present. -/
def appA (n : Fin K) (w : Wd K N) : Wd K N :=
  if n.succ ∈ w.flags then w else ⟨w.state, bump w.glass n, w.flags⟩

/-- Append `ã_{n+1}`: one more coin in glass `n`, unless the flag `A_0` is present. -/
def appT (n : Fin K) (w : Wd K N) : Wd K N :=
  if (0 : Fin (K + 1)) ∈ w.flags then w else ⟨w.state, bump w.glass n, w.flags⟩

/-- Append `A_i`: add the flag `i`. -/
def appBig (i : Fin (K + 1)) (w : Wd K N) : Wd K N :=
  ⟨w.state, w.glass, insert i w.flags⟩

theorem appA_flags (n : Fin K) (w : Wd K N) : (appA n w).flags = w.flags := by
  unfold appA
  split_ifs <;> rfl

theorem appT_flags (n : Fin K) (w : Wd K N) : (appT n w).flags = w.flags := by
  unfold appT
  split_ifs <;> rfl

theorem R_appA (M : Minsky.Machine K N) (n : Fin K) ⦃w w' : Wd K N⦄ (h : R M w w') :
    R M (appA n w) (appA n w') := by
  obtain ⟨hf, h0, r, hr, hrs, hfire, hzf⟩ := h
  by_cases hn : n.succ ∈ w.flags
  · have hn' : n.succ ∈ w'.flags := by
      rw [hf]
      exact hn
    rw [appA, appA, if_pos hn, if_pos hn']
    exact ⟨hf, h0, r, hr, hrs, hfire, hzf⟩
  · have hn' : n.succ ∉ w'.flags := by
      rw [hf]
      exact hn
    rw [appA, appA, if_neg hn, if_neg hn']
    exact ⟨hf, h0, r, hr, hrs, fires_bump hn hzf hfire, hzf⟩

theorem R_appT (M : Minsky.Machine K N) (n : Fin K) ⦃w w' : Wd K N⦄ (h : R M w w') :
    R M (appT n w) (appT n w') := by
  obtain ⟨hf, h0, hrest⟩ := h
  have h0' : (0 : Fin (K + 1)) ∈ w'.flags := by
    rw [hf]
    exact h0
  rw [appT, appT, if_pos h0, if_pos h0']
  exact ⟨hf, h0, hrest⟩

theorem R_appBig (M : Minsky.Machine K N) (i : Fin (K + 1)) ⦃w w' : Wd K N⦄
    (h : R M w w') : R M (appBig i w) (appBig i w') := by
  obtain ⟨hf, h0, r, hr, hrs, hfire, hzf⟩ := h
  refine ⟨?_, Finset.mem_insert_of_mem h0, r, hr, hrs, hfire,
    zeroFlag_mono (Finset.subset_insert i w.flags) hzf⟩
  show insert i w'.flags = insert i w.flags
  rw [hf]

/-! ## Classes -/

/-- The classes of words (KMS `l654`: words modulo the machine relations). -/
abbrev Cls (M : Minsky.Machine K N) : Type := Quot (R M)

variable {M : Minsky.Machine K N}

/-- The flags of a class. -/
def Cls.flags : Cls M → Finset (Fin (K + 1)) :=
  Quot.lift Wd.flags (fun _ _ h ↦ (And.left h).symm)

/-- Append `a_{n+1}` to a class. -/
def Cls.appA (n : Fin K) : Cls M → Cls M :=
  Quot.map (Backward.appA n) (R_appA M n)

/-- Append `ã_{n+1}` to a class. -/
def Cls.appT (n : Fin K) : Cls M → Cls M :=
  Quot.map (Backward.appT n) (R_appT M n)

/-- Append `A_i` to a class. -/
def Cls.appBig (i : Fin (K + 1)) : Cls M → Cls M :=
  Quot.map (Backward.appBig i) (R_appBig M i)

theorem Cls.flags_mk (w : Wd K N) : Cls.flags (Quot.mk (R M) w) = w.flags := rfl

theorem Cls.appA_mk (n : Fin K) (w : Wd K N) :
    Cls.appA n (Quot.mk (R M) w) = Quot.mk (R M) (Backward.appA n w) := rfl

theorem Cls.appT_mk (n : Fin K) (w : Wd K N) :
    Cls.appT n (Quot.mk (R M) w) = Quot.mk (R M) (Backward.appT n w) := rfl

theorem Cls.appBig_mk (i : Fin (K + 1)) (w : Wd K N) :
    Cls.appBig i (Quot.mk (R M) w) = Quot.mk (R M) (Backward.appBig i w) := rfl

theorem Cls.flags_appA (n : Fin K) (c : Cls M) : Cls.flags (Cls.appA n c) = Cls.flags c := by
  induction c using Quot.ind with
  | mk w => exact appA_flags n w

theorem Cls.flags_appT (n : Fin K) (c : Cls M) : Cls.flags (Cls.appT n c) = Cls.flags c := by
  induction c using Quot.ind with
  | mk w => exact appT_flags n w

theorem Cls.flags_appBig (i : Fin (K + 1)) (c : Cls M) :
    Cls.flags (Cls.appBig i c) = insert i (Cls.flags c) := by
  induction c using Quot.ind with
  | mk w => rfl

/-! ## Back to the machine -/

/-- Equivalent words have `≡_M`-equivalent configurations. -/
theorem equiv_of_eqvGen {w w' : Wd K N} (h : Relation.EqvGen (R M) w w') :
    M.Equiv ⟨w.state, w.glass⟩ ⟨w'.state, w'.glass⟩ := by
  induction h with
  | rel _ _ hxy =>
    obtain ⟨-, -, r, hr, hrs, hfire, -⟩ := hxy
    exact Relation.EqvGen.rel _ _ ⟨r, hr, hrs, hfire⟩
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Configurations whose words with a common flag set have the same class are
`≡_M`-equivalent. -/
theorem equiv_of_mk_eq {c d : Minsky.Cfg K N} {S : Finset (Fin (K + 1))}
    (h : Quot.mk (R M) (⟨c.state, c.glass, S⟩ : Wd K N) =
      Quot.mk (R M) (⟨d.state, d.glass, S⟩ : Wd K N)) :
    M.Equiv c d := by
  have h' := equiv_of_eqvGen (Quot.eqvGen_exact h)
  exact h'

end Backward

end KMS

end GroupApproximation.Full.Kharlampovich
