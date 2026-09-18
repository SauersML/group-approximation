import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Backward.Words

/-!
# Activity and commutation of the appends

Input for the "if" direction of KMS Theorem `tmm`(b) (`l654`, `l789` of
Kharlampovich--Myasnikov--Sapir, arXiv:1204.6506, Sec. 4.1), used in
`thm:fixed-radical-membership` of `non_mf_group_notes.tex`.

A letter of block `M_i` acts only at classes without the flag `A_i` (`actB M i`).
The appends keep the flags other than the appended one (`actB_appA`, `actB_appT`,
`actB_appBig_ne`), and `A_i` makes its own block inactive (`not_actB_appBig`).
The appends commute with each other, where the big append needs a different block.
-/

namespace GroupApproximation.Full.Kharlampovich

namespace KMS

namespace Backward

variable {K N : ℕ}

/-! ## Words -/

theorem bump_comm (m : Fin K → ℕ) (n n' : Fin K) :
    bump (bump m n) n' = bump (bump m n') n := by
  funext k
  simp only [bump]
  grind

theorem appA_appA_comm (n m : Fin K) (w : Wd K N) : appA n (appA m w) = appA m (appA n w) := by
  obtain ⟨s, g, S⟩ := w
  by_cases h1 : n.succ ∈ S
  · by_cases h2 : m.succ ∈ S
    · simp only [appA, h1, h2, ↓reduceIte]
    · simp only [appA, h1, h2, ↓reduceIte]
  · by_cases h2 : m.succ ∈ S
    · simp only [appA, h1, h2, ↓reduceIte]
    · simp only [appA, h1, h2, ↓reduceIte]
      rw [bump_comm]

theorem appA_appT_comm (n m : Fin K) (w : Wd K N) : appA n (appT m w) = appT m (appA n w) := by
  obtain ⟨s, g, S⟩ := w
  by_cases h1 : n.succ ∈ S
  · by_cases h2 : (0 : Fin (K + 1)) ∈ S
    · simp only [appA, appT, h1, h2, ↓reduceIte]
    · simp only [appA, appT, h1, h2, ↓reduceIte]
  · by_cases h2 : (0 : Fin (K + 1)) ∈ S
    · simp only [appA, appT, h1, h2, ↓reduceIte]
    · simp only [appA, appT, h1, h2, ↓reduceIte]
      rw [bump_comm]

theorem appT_appT_comm (n m : Fin K) (w : Wd K N) : appT n (appT m w) = appT m (appT n w) := by
  obtain ⟨s, g, S⟩ := w
  by_cases h0 : (0 : Fin (K + 1)) ∈ S
  · simp only [appT, h0, ↓reduceIte]
  · simp only [appT, h0, ↓reduceIte]
    rw [bump_comm]

/-- Without the flags `A_0` and `A_{n+1}`, the letters `ã_{n+1}` and `a_{n+1}` append
the same coin. -/
theorem appT_eq_appA_of (n : Fin K) (w : Wd K N) (h1 : n.succ ∉ w.flags)
    (h0 : (0 : Fin (K + 1)) ∉ w.flags) : appT n w = appA n w := by
  rw [appT, appA, if_neg h0, if_neg h1]

theorem appBig_appA_comm (n : Fin K) (i : Fin (K + 1)) (h : n.succ ≠ i) (w : Wd K N) :
    appBig i (appA n w) = appA n (appBig i w) := by
  obtain ⟨s, g, S⟩ := w
  by_cases h1 : n.succ ∈ S
  · have h2 : n.succ ∈ insert i S := Finset.mem_insert_of_mem h1
    simp only [appA, appBig, h1, h2, ↓reduceIte]
  · have h2 : n.succ ∉ insert i S := by
      rw [Finset.mem_insert]
      exact fun h3 ↦ h3.elim h h1
    simp only [appA, appBig, h1, h2, ↓reduceIte]

theorem appBig_appT_comm (n : Fin K) (i : Fin (K + 1)) (h : (0 : Fin (K + 1)) ≠ i)
    (w : Wd K N) : appBig i (appT n w) = appT n (appBig i w) := by
  obtain ⟨s, g, S⟩ := w
  by_cases h1 : (0 : Fin (K + 1)) ∈ S
  · have h2 : (0 : Fin (K + 1)) ∈ insert i S := Finset.mem_insert_of_mem h1
    simp only [appT, appBig, h1, h2, ↓reduceIte]
  · have h2 : (0 : Fin (K + 1)) ∉ insert i S := by
      rw [Finset.mem_insert]
      exact fun h3 ↦ h3.elim h h1
    simp only [appT, appBig, h1, h2, ↓reduceIte]

theorem appBig_comm (i j : Fin (K + 1)) (w : Wd K N) :
    appBig i (appBig j w) = appBig j (appBig i w) := by
  show (⟨w.state, w.glass, insert i (insert j w.flags)⟩ : Wd K N) =
    ⟨w.state, w.glass, insert j (insert i w.flags)⟩
  rw [Finset.insert_comm]

/-! ## Activity on classes -/

/-- The letters of block `M_i` act at the classes without the flag `A_i` (KMS `l789`). -/
def actB (M : Minsky.Machine K N) (i : Fin (K + 1)) (c : Cls M) : Prop :=
  i ∉ Cls.flags c

instance actB.decidablePred (M : Minsky.Machine K N) (i : Fin (K + 1)) :
    DecidablePred (actB M i) :=
  fun c ↦ inferInstanceAs (Decidable (i ∉ Cls.flags c))

variable {M : Minsky.Machine K N}

theorem actB_appA (j : Fin (K + 1)) (n : Fin K) (c : Cls M) :
    actB M j (Cls.appA n c) ↔ actB M j c := by
  show j ∉ Cls.flags (Cls.appA n c) ↔ j ∉ Cls.flags c
  rw [Cls.flags_appA]

theorem actB_appT (j : Fin (K + 1)) (n : Fin K) (c : Cls M) :
    actB M j (Cls.appT n c) ↔ actB M j c := by
  show j ∉ Cls.flags (Cls.appT n c) ↔ j ∉ Cls.flags c
  rw [Cls.flags_appT]

theorem actB_appBig_ne {i j : Fin (K + 1)} (h : i ≠ j) (c : Cls M) :
    actB M j (Cls.appBig i c) ↔ actB M j c := by
  show j ∉ Cls.flags (Cls.appBig i c) ↔ j ∉ Cls.flags c
  simp only [Cls.flags_appBig, Finset.mem_insert, h.symm, false_or]

theorem not_actB_appBig (i : Fin (K + 1)) (c : Cls M) : ¬ actB M i (Cls.appBig i c) :=
  fun h ↦ h (by
    rw [Cls.flags_appBig]
    exact Finset.mem_insert_self i _)

/-! ## Commutation on classes -/

theorem Cls.appA_appA_comm (n m : Fin K) :
    ∀ c : Cls M, Cls.appA n (Cls.appA m c) = Cls.appA m (Cls.appA n c) :=
  Quot.ind fun w ↦ congrArg (Quot.mk (R M)) (Backward.appA_appA_comm n m w)

theorem Cls.appA_appT_comm (n m : Fin K) :
    ∀ c : Cls M, Cls.appA n (Cls.appT m c) = Cls.appT m (Cls.appA n c) :=
  Quot.ind fun w ↦ congrArg (Quot.mk (R M)) (Backward.appA_appT_comm n m w)

theorem Cls.appT_appT_comm (n m : Fin K) :
    ∀ c : Cls M, Cls.appT n (Cls.appT m c) = Cls.appT m (Cls.appT n c) :=
  Quot.ind fun w ↦ congrArg (Quot.mk (R M)) (Backward.appT_appT_comm n m w)

theorem Cls.appT_eq_appA_of (n : Fin K) :
    ∀ c : Cls M, actB M n.succ c → actB M 0 c → Cls.appT n c = Cls.appA n c :=
  Quot.ind fun w h1 h0 ↦ congrArg (Quot.mk (R M)) (Backward.appT_eq_appA_of n w h1 h0)

theorem Cls.appBig_appA_comm (n : Fin K) (i : Fin (K + 1)) (h : n.succ ≠ i) :
    ∀ c : Cls M, Cls.appBig i (Cls.appA n c) = Cls.appA n (Cls.appBig i c) :=
  Quot.ind fun w ↦ congrArg (Quot.mk (R M)) (Backward.appBig_appA_comm n i h w)

theorem Cls.appBig_appT_comm (n : Fin K) (i : Fin (K + 1)) (h : (0 : Fin (K + 1)) ≠ i) :
    ∀ c : Cls M, Cls.appBig i (Cls.appT n c) = Cls.appT n (Cls.appBig i c) :=
  Quot.ind fun w ↦ congrArg (Quot.mk (R M)) (Backward.appBig_appT_comm n i h w)

theorem Cls.appBig_comm (i j : Fin (K + 1)) :
    ∀ c : Cls M, Cls.appBig i (Cls.appBig j c) = Cls.appBig j (Cls.appBig i c) :=
  Quot.ind fun w ↦ congrArg (Quot.mk (R M)) (Backward.appBig_comm i j w)

end Backward

end KMS

end GroupApproximation.Full.Kharlampovich
