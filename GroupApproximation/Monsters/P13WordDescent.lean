import GroupApproximation.Monsters.P13DescentCore

/-!
# The word descent: measure and splice infrastructure

The descent normalizes an arbitrary word of unit root letters into a
norm-monotone word times a signed-swap element, by repeatedly
rewriting the topmost worst norm violation.  This file formalizes the
trajectory measure and the splice principle behind every rewrite:

* `sigma W b j` — the trajectory norm of the `j`-th suffix;
* `Viol W b j` — a violation: the letter at `j` decreases the norm;
* `lam` — the largest violated height, and `topViol` — the least
  position attaining it; the termination measure is the pair
  `(lam, length − topViol)` in lexicographic order;
* splice lemmas: a rewrite that replaces a block of letters by another
  block with the same evaluation changes `sigma` only at the
  block-internal positions;
* norm invariance: conjugating a word by a signed swap and moving the
  swap into the monomial tail preserves every trajectory norm.

The class-by-class rewrite lemmas and the master induction follow in
the second half of the file.  The measure and the case table were
validated numerically first (`scripts/descent_model.py`): every local
rewrite is matrix-checked and the measure decreases on every step
across thousands of random words.
-/

namespace GroupApproximation
namespace P13WordDescent

open LiteralP13Presentation P13SteinbergCalculus LiteralP13MatrixModel
open P13WeylCalculus P13Weyl13Calculus P13Weyl23Calculus
open P13ColumnLift P13ParabolicKernel P13MonomialMachine P13DescentCore

noncomputable section

/-! ## The trajectory norms -/

/-- The norm of the `j`-th suffix vector. -/
def sigma (W : List Letter) (b : Fin 3 → ℤ) (j : ℕ) : ℕ :=
  vnorm (vecOf (W.drop j) b)

@[simp] theorem sigma_cons_succ (l : Letter) (W : List Letter) (b : Fin 3 → ℤ)
    (j : ℕ) : sigma (l :: W) b (j + 1) = sigma W b j := rfl

theorem sigma_of_ge (W : List Letter) (b : Fin 3 → ℤ) {j : ℕ}
    (h : W.length ≤ j) : sigma W b j = vnorm b := by
  unfold sigma
  rw [List.drop_of_length_le h, vecOf_nil]

/-- A violation: the letter at position `j` strictly decreases the
trajectory norm. -/
def Viol (W : List Letter) (b : Fin 3 → ℤ) (j : ℕ) : Prop :=
  j < W.length ∧ sigma W b j < sigma W b (j + 1)

instance (W : List Letter) (b : Fin 3 → ℤ) (j : ℕ) :
    Decidable (Viol W b j) := by
  unfold Viol
  infer_instance

/-- Monotonicity is the absence of violations. -/
theorem mono_iff_no_viol (W : List Letter) (b : Fin 3 → ℤ) :
    Mono W b ↔ ∀ j, ¬ Viol W b j := by
  induction W with
  | nil =>
      simp only [Mono, Viol]
      constructor
      · intro _ j ⟨hj, _⟩
        exact absurd hj (by simp)
      · intro _
        trivial
  | cons l W ih =>
      constructor
      · rintro ⟨hm, hstep⟩ j hviol
        obtain ⟨hj, hlt⟩ := hviol
        match j with
        | 0 =>
            have h0 : sigma (l :: W) b 0 =
                vnorm (act (toSL3 (letterVal l)) (vecOf W b)) := by
              unfold sigma
              rw [List.drop_zero, ← vecOf_cons]
            rw [h0, sigma_cons_succ] at hlt
            have : sigma W b 0 = vnorm (vecOf W b) := by
              unfold sigma
              rw [List.drop_zero]
            rw [this] at hlt
            exact absurd hstep (by lia)
        | j + 1 =>
            rw [sigma_cons_succ, sigma_cons_succ] at hlt
            exact (ih.mp hm) j ⟨by simpa using hj, hlt⟩
      · intro hnov
        refine ⟨ih.mpr fun j hviol => ?_, ?_⟩
        · obtain ⟨hj, hlt⟩ := hviol
          exact hnov (j + 1) ⟨by simpa using hj,
            by rwa [sigma_cons_succ, sigma_cons_succ]⟩
        · by_contra hlt
          push Not at hlt
          refine hnov 0 ⟨by simp, ?_⟩
          have h0 : sigma (l :: W) b 0 =
              vnorm (act (toSL3 (letterVal l)) (vecOf W b)) := by
            unfold sigma
            rw [List.drop_zero, ← vecOf_cons]
          have h1 : sigma (l :: W) b 1 = vnorm (vecOf W b) := by
            rw [sigma_cons_succ]
            unfold sigma
            rw [List.drop_zero]
          have h2 : sigma (l :: W) b (0 + 1) = sigma (l :: W) b 1 := rfl
          lia

/-! ## The measure -/

/-- The violation positions, as a finite set. -/
def violSet (W : List Letter) (b : Fin 3 → ℤ) : Finset ℕ :=
  (Finset.range W.length).filter (fun j => Viol W b j)

theorem mem_violSet {W : List Letter} {b : Fin 3 → ℤ} {j : ℕ} :
    j ∈ violSet W b ↔ Viol W b j := by
  unfold violSet
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- The largest violated height. -/
def lam (W : List Letter) (b : Fin 3 → ℤ) : ℕ :=
  (violSet W b).sup (fun j => sigma W b (j + 1))

theorem le_lam {W : List Letter} {b : Fin 3 → ℤ} {j : ℕ}
    (hv : Viol W b j) : sigma W b (j + 1) ≤ lam W b :=
  Finset.le_sup (f := fun j => sigma W b (j + 1)) (mem_violSet.mpr hv)

theorem lam_pos {W : List Letter} {b : Fin 3 → ℤ} {j : ℕ}
    (hv : Viol W b j) : 0 < lam W b :=
  lt_of_lt_of_le (by have := hv.2; lia) (le_lam hv)

/-- Some violation attains the largest height, when violations exist. -/
theorem exists_top {W : List Letter} {b : Fin 3 → ℤ} {j₀ : ℕ}
    (hv : Viol W b j₀) :
    ∃ j, Viol W b j ∧ sigma W b (j + 1) = lam W b := by
  have hne : (violSet W b).Nonempty := ⟨j₀, mem_violSet.mpr hv⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_mem_eq_sup (violSet W b) hne
    (fun j => sigma W b (j + 1))
  exact ⟨j, mem_violSet.mp hj, hmax.symm⟩

/-- The least violation position attaining the largest height. -/
def topViol (W : List Letter) (b : Fin 3 → ℤ)
    (h : ∃ j, Viol W b j ∧ sigma W b (j + 1) = lam W b) : ℕ :=
  Nat.find h

theorem topViol_spec {W : List Letter} {b : Fin 3 → ℤ}
    (h : ∃ j, Viol W b j ∧ sigma W b (j + 1) = lam W b) :
    Viol W b (topViol W b h) ∧
      sigma W b (topViol W b h + 1) = lam W b :=
  Nat.find_spec h

theorem topViol_min {W : List Letter} {b : Fin 3 → ℤ}
    (h : ∃ j, Viol W b j ∧ sigma W b (j + 1) = lam W b) {j : ℕ}
    (hj : j < topViol W b h) :
    ¬ (Viol W b j ∧ sigma W b (j + 1) = lam W b) :=
  Nat.find_min h hj

open Classical in
/-- The lexicographic termination measure. -/
noncomputable def meas (W : List Letter) (b : Fin 3 → ℤ) : ℕ × ℕ :=
  if h : ∃ j, Viol W b j ∧ sigma W b (j + 1) = lam W b then
    (lam W b, W.length - topViol W b h)
  else (0, 0)

/-! ## Splice: rewrites are local in the trajectory -/

/-- Trajectory values in the deep part are untouched by a rewrite of
shallower letters. -/
theorem sigma_append_deep (A C : List Letter) (b : Fin 3 → ℤ) (t : ℕ) :
    sigma (A ++ C) b (A.length + t) = sigma C b t := by
  unfold sigma
  have h : (A ++ C).drop (A.length + t) = C.drop t := by
    rw [← List.drop_drop, List.drop_left]
  rw [h]

/-! ## Inverse spellings of the remaining swaps -/

theorem w_inv_word : w⁻¹ = x 0 (-1) * x 2 1 * x 0 (-1) := by
  show (x 0 1 * x 2 (-1) * x 0 1)⁻¹ = x 0 (-1) * x 2 1 * x 0 (-1)
  simp only [x]
  group

theorem w13_inv_word : w13⁻¹ = x 1 (-1) * x 4 1 * x 1 (-1) := by
  show (x 1 1 * x 4 (-1) * x 1 1)⁻¹ = x 1 (-1) * x 4 1 * x 1 (-1)
  simp only [x]
  group

/-! ## Norm invariance of the signed swaps -/

theorem vnorm_act_w (v : Fin 3 → ℤ) :
    vnorm (act (toSL3 w) v) = vnorm v := by
  rw [act_w]
  simp [vnorm]
  lia

theorem vnorm_act_w13 (v : Fin 3 → ℤ) :
    vnorm (act (toSL3 w13) v) = vnorm v := by
  rw [act_w13]
  simp [vnorm]
  lia

theorem vnorm_act_w23 (v : Fin 3 → ℤ) :
    vnorm (act (toSL3 w23) v) = vnorm v := by
  rw [act_w23]
  simp [vnorm]
  lia

theorem vnorm_act_inv {m : P13}
    (hm : ∀ u, vnorm (act (toSL3 m) u) = vnorm u) (v : Fin 3 → ℤ) :
    vnorm (act ((toSL3 m)⁻¹) v) = vnorm v := by
  have h := hm (act ((toSL3 m)⁻¹) v)
  rw [← act_mul, mul_inv_cancel, act_one] at h
  exact h.symm

/-! ## The braid identities

In each block the anti-aligned pair collapses onto the block Weyl
element by bare cancellation of the third braid letter. -/

/-! ## The generic splice measure decrease

A rewrite replaces the two letters at the topmost worst violation by a
block of at most three letters (with the evaluation preserved, up to a
signed swap pushed into the monomial tail).  When every block-internal
trajectory norm lies strictly below the violated height, the measure
decreases: the height cannot grow, and if it persists, its topmost
site sinks strictly deeper.  This single lemma serves every rewrite
class; the numerical model certifies that a peak-cutting block always
exists. -/

/-- The data of one descent step at the topmost worst violation. -/
structure SpliceData (W : List Letter) (b : Fin 3 → ℤ) where
  /-- the topmost worst violation exists -/
  hex : ∃ j, Viol W b j ∧ sigma W b (j + 1) = lam W b
  /-- shallow part -/
  A : List Letter
  /-- replacement block, length at most three -/
  P' : List Letter
  /-- deep part of the new word -/
  C' : List Letter
  /-- the new base -/
  b' : Fin 3 → ℤ
  /-- decomposition at the violation -/
  hW : W.length = A.length + 2 + (W.length - A.length - 2)
  hA : A.length = topViol W b hex
  hlen : P'.length ≤ 3
  /-- the deep part has the length of the old deep part -/
  hC : C'.length = W.length - A.length - 2

/-- Shallow trajectory agreement, deep trajectory agreement, and the
peak cut, packaged as the hypotheses of the measure comparison. -/
structure SpliceFacts (W : List Letter) (b : Fin 3 → ℤ)
    (D : SpliceData W b) : Prop where
  /-- values at or above the block top agree -/
  shallow : ∀ j ≤ D.A.length,
    sigma (D.A ++ D.P' ++ D.C') D.b' j = sigma W b j
  /-- values at or below the block bottom agree with the old deep part -/
  deep : ∀ t, sigma (D.A ++ D.P' ++ D.C') D.b'
      (D.A.length + D.P'.length + t) = sigma W b (D.A.length + 2 + t)
  /-- every strictly internal value of the new block is below the
  violated height -/
  cut : ∀ t, 0 < t → t < D.P'.length →
    sigma (D.A ++ D.P' ++ D.C') D.b' (D.A.length + t) < lam W b

/-- A strict trajectory increase at `j` already places `j` inside the
word: beyond the word both norms are the base norm. -/
private theorem viol_of_lt {W : List Letter} {b : Fin 3 → ℤ} {j : ℕ}
    (h : sigma W b j < sigma W b (j + 1)) : Viol W b j := by
  refine ⟨?_, h⟩
  by_contra hge
  push Not at hge
  have h1 := sigma_of_ge W b hge
  have h2 := sigma_of_ge W b (le_trans hge (Nat.le_add_right j 1))
  lia

/-- The value below the top violation is bounded by the violated
height: otherwise the position below would violate at a greater
height. -/
private theorem sigma_succ_top_le {W : List Letter} {b : Fin 3 → ℤ}
    (hex : ∃ j, Viol W b j ∧ sigma W b (j + 1) = lam W b) :
    sigma W b (topViol W b hex + 1 + 1) ≤ lam W b := by
  obtain ⟨_, htop⟩ := topViol_spec hex
  by_contra hgt
  push Not at hgt
  have hlt : sigma W b (topViol W b hex + 1) <
      sigma W b (topViol W b hex + 1 + 1) := by
    rw [htop]
    lia
  have := le_lam (viol_of_lt hlt)
  lia

/-- Position analysis for a violation of the spliced word: it is a
shallow copy of an old violation, or its height is cut, or its height
is bounded and its site has sunk. -/
private theorem newViol_cases (W : List Letter) (b : Fin 3 → ℤ)
    (D : SpliceData W b) (F : SpliceFacts W b D)
    (hK1 : sigma W b (D.A.length + 2) ≤ lam W b)
    {j : ℕ} (hvj : Viol (D.A ++ D.P' ++ D.C') D.b' j) :
    (j < D.A.length ∧ Viol W b j ∧
        sigma (D.A ++ D.P' ++ D.C') D.b' (j + 1) = sigma W b (j + 1))
    ∨ sigma (D.A ++ D.P' ++ D.C') D.b' (j + 1) < lam W b
    ∨ (sigma (D.A ++ D.P' ++ D.C') D.b' (j + 1) ≤ lam W b ∧
        (D.A ++ D.P' ++ D.C').length - j < W.length - D.A.length) := by
  have hlen' : (D.A ++ D.P' ++ D.C').length =
      D.A.length + D.P'.length + D.C'.length := by
    simp [Nat.add_assoc]
  rcases Nat.lt_or_ge j D.A.length with hsh | hge
  · -- shallow: the old pair survives verbatim
    have hsj : sigma (D.A ++ D.P' ++ D.C') D.b' j = sigma W b j :=
      F.shallow j (le_of_lt hsh)
    have hsj1 : sigma (D.A ++ D.P' ++ D.C') D.b' (j + 1) =
        sigma W b (j + 1) := F.shallow (j + 1) (by lia)
    have h2 := hvj.2
    rw [hsj, hsj1] at h2
    exact Or.inl ⟨hsh, viol_of_lt h2, hsj1⟩
  · rcases Nat.lt_or_ge j (D.A.length + D.P'.length) with hblk | hdeep
    · -- inside the block
      rcases Nat.lt_or_ge (j + 1) (D.A.length + D.P'.length) with hin | hbd
      · -- the height is a cut internal
        have hc := F.cut (j + 1 - D.A.length) (by omega) (by omega)
        rw [show D.A.length + (j + 1 - D.A.length) = j + 1 from by
          omega] at hc
        exact Or.inr (Or.inl hc)
      · -- the height is the old value below the block
        have hj1 : j + 1 = D.A.length + D.P'.length := by lia
        have hd0 := F.deep 0
        simp only [Nat.add_zero] at hd0
        rw [← hj1] at hd0
        refine Or.inr (Or.inr ⟨?_, ?_⟩)
        · rw [hd0]
          exact hK1
        · have hA := D.hA
          have hC := D.hC
          have hWl := D.hW
          have hjlt := hvj.1
          omega
    · -- deep: an old pair, shifted
      have hd0 := F.deep (j - D.A.length - D.P'.length)
      have hd1 := F.deep (j - D.A.length - D.P'.length + 1)
      rw [show D.A.length + D.P'.length +
          (j - D.A.length - D.P'.length) = j from by omega] at hd0
      rw [show D.A.length + D.P'.length +
          (j - D.A.length - D.P'.length + 1) = j + 1 from by omega] at hd1
      rw [show D.A.length + 2 + (j - D.A.length - D.P'.length + 1) =
          (D.A.length + 2 + (j - D.A.length - D.P'.length)) + 1 from by
        omega] at hd1
      have h2 := hvj.2
      rw [hd0, hd1] at h2
      have hold := viol_of_lt h2
      have hht := le_lam hold
      refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · rw [hd1]
        exact hht
      · have hA := D.hA
        have hC := D.hC
        have hWl := D.hW
        have hjlt := hvj.1
        omega

/-- **Generic measure decrease.**  Any peak-cutting splice at the
topmost worst violation strictly decreases the lexicographic
measure. -/
theorem meas_lt_of_splice (W : List Letter) (b : Fin 3 → ℤ)
    (D : SpliceData W b) (F : SpliceFacts W b D) :
    Prod.Lex (· < ·) (· < ·)
      (meas (D.A ++ D.P' ++ D.C') D.b') (meas W b) := by
  have hK0 : 0 < lam W b := lam_pos (topViol_spec D.hex).1
  have hK1 : sigma W b (D.A.length + 2) ≤ lam W b := by
    have h := sigma_succ_top_le D.hex
    have hA := D.hA
    rw [show D.A.length + 2 = topViol W b D.hex + 1 + 1 from by lia]
    exact h
  have hmeasW : meas W b =
      (lam W b, W.length - topViol W b D.hex) := by
    unfold meas
    rw [dif_pos D.hex]
  by_cases hex' : ∃ j, Viol (D.A ++ D.P' ++ D.C') D.b' j ∧
      sigma (D.A ++ D.P' ++ D.C') D.b' (j + 1) =
        lam (D.A ++ D.P' ++ D.C') D.b'
  · -- violations remain: compare heights
    have hmeasW' : meas (D.A ++ D.P' ++ D.C') D.b' =
        (lam (D.A ++ D.P' ++ D.C') D.b',
          (D.A ++ D.P' ++ D.C').length -
            topViol (D.A ++ D.P' ++ D.C') D.b' hex') := by
      unfold meas
      rw [dif_pos hex']
    have hlam' : lam (D.A ++ D.P' ++ D.C') D.b' ≤ lam W b := by
      apply Finset.sup_le
      intro j hj
      rcases newViol_cases W b D F hK1 (mem_violSet.mp hj) with
        ⟨_, hold, heq⟩ | hcut | ⟨hle, _⟩
      · rw [heq]
        exact le_lam hold
      · lia
      · exact hle
    rcases lt_or_eq_of_le hlam' with hlt | hlameq
    · rw [hmeasW', hmeasW]
      exact Prod.Lex.left _ _ hlt
    · -- the height persists: its topmost site has sunk
      obtain ⟨hv', htop'⟩ := topViol_spec hex'
      rcases newViol_cases W b D F hK1 hv' with
        ⟨hjlt, hold, heq⟩ | hcut | ⟨_, hprog⟩
      · exfalso
        have hσ : sigma W b (topViol (D.A ++ D.P' ++ D.C') D.b' hex'
            + 1) = lam W b := by
          rw [← heq, htop', hlameq]
        have hA := D.hA
        exact topViol_min D.hex (by lia) ⟨hold, hσ⟩
      · exfalso
        rw [htop', hlameq] at hcut
        lia
      · rw [hmeasW', hmeasW, hlameq]
        apply Prod.Lex.right
        have hA := D.hA
        omega
  · -- no violation survives: the measure collapses to the bottom
    have hmeasW' : meas (D.A ++ D.P' ++ D.C') D.b' = (0, 0) := by
      unfold meas
      rw [dif_neg hex']
    rw [hmeasW', hmeasW]
    exact Prod.Lex.left _ _ hK0

end

end P13WordDescent
end GroupApproximation
