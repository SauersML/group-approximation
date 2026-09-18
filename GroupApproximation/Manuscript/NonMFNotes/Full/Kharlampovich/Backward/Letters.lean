import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Backward.Tables
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Backward.PermAlg
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Backward.Moves

/-!
# The letters `L_1 ∪ L_2` as permutations

Input for the "if" direction of KMS Theorem `tmm`(b) (`l654`, `l789` of
Kharlampovich--Myasnikov--Sapir, arXiv:1204.6506, Sec. 4.1), used in
`thm:fixed-radical-membership` of `non_mf_group_notes.tex`.

A small letter is recorded by its glass `n`, whether it is a tilde letter (block
`M_0`) and whether it is primed.  It acts by the local operator of its table at the
classes without the flag of its block, appending `a_{n+1}` or `ã_{n+1}` (`Small.perm`).
The letter `A_i` acts by `φ ↦ φ + φ ∘ A_i` at the classes without `A_i` (`pB`).
`genH` sends the `x`-letters to `1`.

This file proves that the small letters commute pairwise (G1 for `H_2`), that letters
of different blocks commute (G2), and that a letter of block `M_i` fixes the values at
classes carrying `A_i` (the input for G5 c)).
-/

namespace GroupApproximation.Full.Kharlampovich

namespace KMS

namespace Backward

variable {K N : ℕ}

/-- A small letter `a_{n+1}`, `a'_{n+1}`, `ã_{n+1}` or `ã'_{n+1}`. -/
structure Small (K : ℕ) : Type where
  /-- The glass. -/
  n : Fin K
  /-- Whether the letter is a tilde letter. -/
  tilde : Bool
  /-- Whether the letter is primed. -/
  prime : Bool

namespace Small

/-- The block of a small letter. -/
def blk (u : Small K) : Fin (K + 1) := cond u.tilde 0 u.n.succ

/-- The append of a small letter. -/
def sig (M : Minsky.Machine K N) (u : Small K) : Cls M → Cls M :=
  cond u.tilde (Cls.appT u.n) (Cls.appA u.n)

/-- The table of a small letter. -/
def tab (u : Small K) : Tab := cond u.prime tAp tA

/-- The table of the inverse of a small letter. -/
def tabi (u : Small K) : Tab := cond u.prime tApi tAi

end Small

variable {M : Minsky.Machine K N}

theorem actB_sig (j : Fin (K + 1)) (u : Small K) (c : Cls M) :
    actB M j (u.sig M c) ↔ actB M j c := by
  obtain ⟨n, b, _⟩ := u
  cases b
  · exact actB_appA j n c
  · exact actB_appT j n c

theorem tab_inv (u : Small K) (t : Tri) (g h : Tri → ZMod 2) (y : ZMod 2) :
    u.tabi.app t (fun s ↦ u.tab.app s g (h s)) (u.tab.app t h y) = g t := by
  obtain ⟨_, _, p⟩ := u
  cases p
  · exact tA_tAi t g h y
  · exact tAp_tApi t g h y

theorem tabi_inv (u : Small K) (t : Tri) (g h : Tri → ZMod 2) (y : ZMod 2) :
    u.tab.app t (fun s ↦ u.tabi.app s g (h s)) (u.tabi.app t h y) = g t := by
  obtain ⟨_, _, p⟩ := u
  cases p
  · exact tAi_tA t g h y
  · exact tApi_tAp t g h y

theorem tab_comm (u w : Small K) (t : Tri) (g h : Tri → ZMod 2) (y : ZMod 2) :
    u.tab.app t (fun s ↦ w.tab.app s g (h s)) (w.tab.app t h y) =
      w.tab.app t (fun s ↦ u.tab.app s g (h s)) (u.tab.app t h y) := by
  obtain ⟨_, _, p⟩ := u
  obtain ⟨_, _, p'⟩ := w
  cases p <;> cases p'
  · exact tab_comm_self tA t g h y
  · exact tA_tAp_comm t g h y
  · exact tAp_tA_comm t g h y
  · exact tab_comm_self tAp t g h y

theorem sig_eq_of (u w : Small K) (hn : u.n = w.n) (c : Cls M) (hu : actB M u.blk c)
    (hw : actB M w.blk c) : w.sig M c = u.sig M c := by
  obtain ⟨n, b, _⟩ := u
  obtain ⟨m, b', _⟩ := w
  have hn' : n = m := hn
  cases hn'
  cases b <;> cases b'
  · rfl
  · exact Cls.appT_eq_appA_of _ c hu hw
  · exact (Cls.appT_eq_appA_of _ c hw hu).symm
  · rfl

theorem sig_comm (u w : Small K) (c : Cls M) : u.sig M (w.sig M c) = w.sig M (u.sig M c) := by
  obtain ⟨n, b, _⟩ := u
  obtain ⟨m, b', _⟩ := w
  cases b <;> cases b'
  · exact Cls.appA_appA_comm n m c
  · exact Cls.appA_appT_comm n m c
  · exact (Cls.appA_appT_comm m n c).symm
  · exact Cls.appT_appT_comm n m c

theorem appBig_sig_comm (i : Fin (K + 1)) (u : Small K) (h : u.blk ≠ i) (c : Cls M) :
    Cls.appBig i (u.sig M c) = u.sig M (Cls.appBig i c) := by
  obtain ⟨n, b, _⟩ := u
  cases b
  · exact Cls.appBig_appA_comm n i h c
  · exact Cls.appBig_appT_comm n i h c

/-- The permutation of a small letter (KMS `l789`). -/
def Small.perm (M : Minsky.Machine K N) (u : Small K) : Equiv.Perm (Fn K (Cls M)) :=
  permL u.n (actB M u.blk) (u.sig M) u.tab u.tabi (actB_sig u.blk u) (tab_inv u) (tabi_inv u)

/-- The permutation of the letter `A_i` (KMS `l789`). -/
def pB (M : Minsky.Machine K N) (i : Fin (K + 1)) : Equiv.Perm (Fn K (Cls M)) :=
  permB (actB M i) (Cls.appBig i) (fun c _ ↦ not_actB_appBig i c)

/-- The letters of `L_1 ∪ L_2` as permutations; the `x`-letters go to `1`. -/
def genH (M : Minsky.Machine K N) : KhGen K N → Equiv.Perm (Fn K (Cls M))
  | .x _ _ => 1
  | .bigA i => pB M i
  | .a n => Small.perm M ⟨n, false, false⟩
  | .a' n => Small.perm M ⟨n, false, true⟩
  | .ta n => Small.perm M ⟨n, true, false⟩
  | .ta' n => Small.perm M ⟨n, true, true⟩

theorem Small.perm_apply (u : Small K) (φ : Fn K (Cls M)) :
    Small.perm M u φ = opL u.n (actB M u.blk) (u.sig M) u.tab φ := rfl

theorem Small.perm_inv_apply (u : Small K) (φ : Fn K (Cls M)) :
    (Small.perm M u)⁻¹ φ = opL u.n (actB M u.blk) (u.sig M) u.tabi φ := rfl

theorem pB_apply (i : Fin (K + 1)) (φ : Fn K (Cls M)) :
    pB M i φ = opB (actB M i) (Cls.appBig i) φ := rfl

theorem pB_inv_apply (i : Fin (K + 1)) (φ : Fn K (Cls M)) :
    (pB M i)⁻¹ φ = opB (actB M i) (Cls.appBig i) φ := rfl

theorem Small.isFix (u : Small K) : IsFix (actB M u.blk) (Small.perm M u) :=
  isFix_permL u.n (actB M u.blk) (u.sig M) u.tab u.tabi (actB_sig u.blk u) (tab_inv u)
    (tabi_inv u)

/-! ## Commutation -/

theorem Small.comm_same (n : Fin K) (b p b' p' : Bool) (φ : Fn K (Cls M)) :
    Small.perm M ⟨n, b, p⟩ (Small.perm M ⟨n, b', p'⟩ φ) =
      Small.perm M ⟨n, b', p'⟩ (Small.perm M ⟨n, b, p⟩ φ) :=
  opL_comm_self n (actB M (Small.blk ⟨n, b, p⟩)) (Small.sig M ⟨n, b, p⟩)
    (actB_sig (Small.blk ⟨n, b, p⟩) ⟨n, b, p⟩) (actB_sig (Small.blk ⟨n, b', p'⟩) ⟨n, b, p⟩)
    (actB_sig (Small.blk ⟨n, b, p⟩) ⟨n, b', p'⟩) (sig_eq_of ⟨n, b, p⟩ ⟨n, b', p'⟩ rfl)
    (tab_comm ⟨n, b, p⟩ ⟨n, b', p'⟩) φ

theorem Small.comm_ne {n m : Fin K} (hn : n ≠ m) (b p b' p' : Bool) (φ : Fn K (Cls M)) :
    Small.perm M ⟨n, b, p⟩ (Small.perm M ⟨m, b', p'⟩ φ) =
      Small.perm M ⟨m, b', p'⟩ (Small.perm M ⟨n, b, p⟩ φ) :=
  opL_comm_ne n (actB M (Small.blk ⟨n, b, p⟩)) (Small.sig M ⟨n, b, p⟩) hn
    (actB_sig (Small.blk ⟨m, b', p'⟩) ⟨n, b, p⟩) (actB_sig (Small.blk ⟨n, b, p⟩) ⟨m, b', p'⟩)
    (fun c _ _ ↦ sig_comm ⟨m, b', p'⟩ ⟨n, b, p⟩ c) (Small.tab ⟨n, b, p⟩)
    (Small.tab ⟨m, b', p'⟩) φ

/-- Small letters commute (G1 for `H_2`). -/
theorem Small.comm (u w : Small K) :
    Small.perm M u * Small.perm M w = Small.perm M w * Small.perm M u := by
  obtain ⟨n, b, p⟩ := u
  obtain ⟨m, b', p'⟩ := w
  refine Equiv.ext fun φ ↦ ?_
  by_cases hn : n = m
  · cases hn
    exact Small.comm_same _ b p b' p' φ
  · exact Small.comm_ne hn b p b' p' φ

/-- `A_i` commutes with a small letter of another block (G2). -/
theorem pB_small_comm (i : Fin (K + 1)) (u : Small K) (h : u.blk ≠ i) :
    pB M i * Small.perm M u = Small.perm M u * pB M i :=
  Equiv.ext fun φ ↦ opB_opL_comm (actB M i) (Cls.appBig i) u.n u.tab (actB_appBig_ne h.symm)
    (actB_sig i u) (fun c _ _ ↦ appBig_sig_comm i u h c) φ

/-- The letters `A_i` commute (G1 for `H_1`). -/
theorem pB_comm (i j : Fin (K + 1)) : pB M i * pB M j = pB M j * pB M i := by
  by_cases h : i = j
  · rw [h]
  · exact Equiv.ext fun φ ↦ opB_comm (actB M i) (Cls.appBig i) (actB_appBig_ne h)
      (actB_appBig_ne (Ne.symm h)) (fun c _ _ ↦ Cls.appBig_comm i j c) φ

/-! ## Letters by block -/

theorem genH_of_small :
    ∀ s : KhGen K N, s.IsSmall → ∃ u : Small K, genH M s = Small.perm M u
  | .x _ _, hs => False.elim hs
  | .bigA _, hs => False.elim hs
  | .a n, _ => ⟨⟨n, false, false⟩, rfl⟩
  | .a' n, _ => ⟨⟨n, false, true⟩, rfl⟩
  | .ta n, _ => ⟨⟨n, true, false⟩, rfl⟩
  | .ta' n, _ => ⟨⟨n, true, true⟩, rfl⟩

theorem genH_of_block : ∀ (s : KhGen K N) (i : Fin (K + 1)), s.block = some i →
    genH M s = pB M i ∨ ∃ u : Small K, u.blk = i ∧ genH M s = Small.perm M u
  | .x _ _, _, h => by simp only [KhGen.block, reduceCtorEq] at h
  | .bigA _, _, h => Or.inl (congrArg (pB M) (Option.some_inj.mp h))
  | .a n, _, h => Or.inr ⟨⟨n, false, false⟩, Option.some_inj.mp h, rfl⟩
  | .a' n, _, h => Or.inr ⟨⟨n, false, true⟩, Option.some_inj.mp h, rfl⟩
  | .ta n, _, h => Or.inr ⟨⟨n, true, false⟩, Option.some_inj.mp h, rfl⟩
  | .ta' n, _, h => Or.inr ⟨⟨n, true, true⟩, Option.some_inj.mp h, rfl⟩

theorem pB_fix (i : Fin (K + 1)) (φ : Fn K (Cls M)) (v : Fin K → Tri) {c : Cls M}
    (hc : ¬ actB M i c) : pB M i φ v c = φ v c := by
  show opB (actB M i) (Cls.appBig i) φ v c = φ v c
  simp only [opB, hc, ↓reduceIte]

theorem pB_inv_fix (i : Fin (K + 1)) (φ : Fn K (Cls M)) (v : Fin K → Tri) {c : Cls M}
    (hc : ¬ actB M i c) : (pB M i)⁻¹ φ v c = φ v c := by
  show opB (actB M i) (Cls.appBig i) φ v c = φ v c
  simp only [opB, hc, ↓reduceIte]

/-- A letter of block `M_i` and its inverse fix the values at classes carrying `A_i`
(the input for G5 c)). -/
theorem genH_fix (s : KhGen K N) (i : Fin (K + 1)) (h : s.block = some i)
    (φ : Fn K (Cls M)) (v : Fin K → Tri) {c : Cls M} (hc : ¬ actB M i c) :
    genH M s φ v c = φ v c ∧ (genH M s)⁻¹ φ v c = φ v c := by
  rcases genH_of_block s i h with he | ⟨u, hu, he⟩
  · rw [he]
    exact ⟨pB_fix i φ v hc, pB_inv_fix i φ v hc⟩
  · rw [he]
    subst hu
    exact ⟨(Small.isFix u).fix φ v c hc, (Small.isFix u).inv.fix φ v c hc⟩

end Backward

end KMS

end GroupApproximation.Full.Kharlampovich
