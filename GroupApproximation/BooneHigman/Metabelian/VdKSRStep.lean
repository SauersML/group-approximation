import GroupApproximation.BooneHigman.Metabelian.VdKSRCollapse
import Mathlib.Algebra.BigOperators.Ring.Finset
import GroupApproximation.Meta.AxiomGuard

/-!
# Elementary Krull dimension `< n` implies stable range `≤ n`

Lane `bh-met-90m`, part 2.  Heitmann-style induction on `n`, generalising the ideal `I`:
if `vdkSR_KdimLE I n`, then every row `v ∈ R^{n+1}` that is unimodular modulo `I` is reducible
modulo `I` (`vdkSR_reducible_of_kdimLE`).

Step (`n + 1`): write `v = (y, v')`.  `v'` is unimodular modulo the boundary ideal `bdry I y`, so
by induction `(v'_j + b'_j c)_j` (`c` the last entry of `v'`) is unimodular modulo `bdry I y`,
witnessed by `y^m (1 - ∑ (v'_j + b'_j c) w''_j - y t) ∈ I`.  With
`b₀ = (w_c - ∑ b'_j w_j) (1 - (yt)^{m+1})`, the row `(y + b₀ c, v'_j + b'_j c)` is unimodular
modulo `I`: in `R / (span(row) + I)` the ring identity `vdkSR_quot_key` gives `1 = 0`.

Taking `I = ⊥` gives `vdkSR_stableRangeLE_of_kdimLE`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

section Step

variable {R : Type*} [CommRing R]

/-- The quotient computation of the induction step. -/
theorem vdkSR_one_mem_core {n : ℕ} (I M : Ideal R) (hIM : I ≤ M) (y c t w0 wl : R) (m : ℕ)
    (a b' wa w'' : Fin n → R)
    (hw : 1 - (y * w0 + (∑ j, a j * wa j + c * wl)) ∈ I)
    (htm : y ^ m * (1 - ∑ j, (a j + b' j * c) * w'' j - y * t) ∈ I)
    (h0 : y + (wl - ∑ j, b' j * wa j) * (1 - (y * t) ^ (m + 1)) * c ∈ M)
    (hs : ∀ j, a j + b' j * c ∈ M) : (1 : R) ∈ M := by
  refine Ideal.Quotient.eq_zero_iff_mem.mp ?_
  rw [map_one]
  have hsj : ∀ j, Ideal.Quotient.mk M (a j) =
      -(Ideal.Quotient.mk M (b' j) * Ideal.Quotient.mk M c) := by
    intro j
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr (hs j)
    rw [map_add, map_mul] at h
    linear_combination h
  have hsum1 : ∑ j, Ideal.Quotient.mk M (a j) * Ideal.Quotient.mk M (wa j) =
      -(Ideal.Quotient.mk M c *
        ∑ j, Ideal.Quotient.mk M (b' j) * Ideal.Quotient.mk M (wa j)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [hsj j]; ring
  have hsum2 : ∑ j, (Ideal.Quotient.mk M (a j) +
      Ideal.Quotient.mk M (b' j) * Ideal.Quotient.mk M c) * Ideal.Quotient.mk M (w'' j) = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [hsj j]; ring
  have h1 := Ideal.Quotient.eq_zero_iff_mem.mpr (hIM hw)
  have h2 := Ideal.Quotient.eq_zero_iff_mem.mpr (hIM htm)
  have h3 := Ideal.Quotient.eq_zero_iff_mem.mpr h0
  simp only [map_sub, map_add, map_mul, map_one, map_pow, map_sum] at h1 h2 h3
  refine vdkSR_quot_key (Ideal.Quotient.mk M y) (Ideal.Quotient.mk M t)
    (Ideal.Quotient.mk M w0) (Ideal.Quotient.mk M c)
    (Ideal.Quotient.mk M wl - ∑ j, Ideal.Quotient.mk M (b' j) * Ideal.Quotient.mk M (wa j))
    m ?_ ?_ h3
  · linear_combination h2 + Ideal.Quotient.mk M y ^ m * hsum2
  · linear_combination (-1 : R ⧸ M) * h1 - hsum1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkSR_one_mem_core

theorem vdkSR_reduceRow_cons_zero {n : ℕ} (y b0 : R) (v' : Fin (n + 1) → R) (b' : Fin n → R) :
    vdkStab_reduceRow (Fin.cons y v' : Fin (n + 1 + 1) → R) (Fin.cons b0 b' : Fin (n + 1) → R) 0
      = y + b0 * v' (Fin.last n) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkSR_reduceRow_cons_zero

theorem vdkSR_reduceRow_cons_succ {n : ℕ} (y b0 : R) (v' : Fin (n + 1) → R) (b' : Fin n → R)
    (j : Fin n) :
    vdkStab_reduceRow (Fin.cons y v' : Fin (n + 1 + 1) → R) (Fin.cons b0 b' : Fin (n + 1) → R)
      j.succ = v' (Fin.castSucc j) + b' j * v' (Fin.last n) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkSR_reduceRow_cons_succ

/-- The induction step: an explicit reduction of `(y, v')` modulo `I`. -/
theorem vdkSR_step {n : ℕ} (I : Ideal R) (y : R) (v' : Fin (n + 1) → R)
    (w : Fin (n + 1 + 1) → R) (hw : 1 - (y * w 0 + ∑ i : Fin (n + 1), v' i * w i.succ) ∈ I)
    (b' w'' : Fin n → R) (t : R) (m : ℕ)
    (htm : y ^ m * (1 - ∑ j, vdkStab_reduceRow v' b' j * w'' j - y * t) ∈ I) :
    vdkSR_UnimodMod I (vdkStab_reduceRow (Fin.cons y v' : Fin (n + 1 + 1) → R)
      (Fin.cons ((w (Fin.last n).succ - ∑ j, b' j * w (Fin.castSucc j).succ) *
        (1 - (y * t) ^ (m + 1))) b' : Fin (n + 1) → R)) := by
  apply vdkSR_unimodMod_of_one_mem
  rw [Fin.sum_univ_castSucc] at hw
  exact vdkSR_one_mem_core I _ le_sup_right y (v' (Fin.last n)) t (w 0) (w (Fin.last n).succ) m
    (fun j => v' (Fin.castSucc j)) b' (fun j => w (Fin.castSucc j).succ) w'' hw htm
    (Ideal.mem_sup_left (vdkStab_mem_span_of_eq 0 (vdkSR_reduceRow_cons_zero y _ v' b')))
    (fun j => Ideal.mem_sup_left
      (vdkStab_mem_span_of_eq j.succ (vdkSR_reduceRow_cons_succ y _ v' b' j)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkSR_step

/-- **Heitmann induction**: `Kdim (R/I) < n` (elementary) makes every row of length `n + 1`
that is unimodular modulo `I` reducible modulo `I`. -/
theorem vdkSR_reducible_of_kdimLE : ∀ (n : ℕ) (I : Ideal R), vdkSR_KdimLE I n →
    ∀ v : Fin (n + 1) → R, vdkSR_UnimodMod I v →
      ∃ b : Fin n → R, vdkSR_UnimodMod I (vdkStab_reduceRow v b)
  | 0, I, hI, _, _ => by
    obtain ⟨_, _, h⟩ := hI (fun _ => 0)
    rw [vdkSR_collapse_zero] at h
    refine ⟨fun _ => 0, fun _ => 0, ?_⟩
    rw [Fin.sum_univ_zero, sub_zero]
    exact h
  | n + 1, I, hI, v, hv => by
    obtain ⟨y, v', rfl⟩ : ∃ (y : R) (v' : Fin (n + 1) → R),
        v = (Fin.cons y v' : Fin (n + 1 + 1) → R) :=
      ⟨v 0, Fin.tail v, (Fin.cons_self_tail v).symm⟩
    obtain ⟨w, hw⟩ := hv
    rw [Fin.sum_univ_succ] at hw
    simp only [Fin.cons_zero, Fin.cons_succ] at hw
    have key : y ^ 0 * (1 - ∑ i, v' i * w i.succ - y * w 0) ∈ I := by
      rw [show y ^ 0 * (1 - ∑ i, v' i * w i.succ - y * w 0) =
          1 - (y * w 0 + ∑ i, v' i * w i.succ) by ring]
      exact hw
    have hv' : vdkSR_UnimodMod (vdkSR_bdry I y) v' :=
      ⟨fun i => w i.succ, vdkSR_mem_bdry.mpr ⟨w 0, 0, key⟩⟩
    obtain ⟨b', w'', hb'⟩ :=
      vdkSR_reducible_of_kdimLE n (vdkSR_bdry I y) (vdkSR_kdimLE_bdry hI y) v' hv'
    obtain ⟨t, m, htm⟩ := vdkSR_mem_bdry.mp hb'
    exact ⟨_, vdkSR_step I y v' w hw b' w'' t m htm⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkSR_reducible_of_kdimLE

/-- If `Kdim R < n` (elementary) for all `n ≥ r`, then `sr(R) ≤ r`. -/
theorem vdkSR_stableRangeLE_of_kdimLE (r : ℕ)
    (h : ∀ n : ℕ, r ≤ n → vdkSR_KdimLE (⊥ : Ideal R) n) : vdkStab_StableRangeLE R r := by
  intro n hn v hv
  obtain ⟨w, hw⟩ := hv
  have h0 : 1 - ∑ i, v i * w i ∈ (⊥ : Ideal R) := Ideal.mem_bot.mpr (by rw [hw, sub_self])
  obtain ⟨b, w', hb⟩ := vdkSR_reducible_of_kdimLE n ⊥ (h n hn) v ⟨w, h0⟩
  rw [Ideal.mem_bot, sub_eq_zero] at hb
  exact ⟨b, w', hb.symm⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkSR_stableRangeLE_of_kdimLE

end Step

end GroupApproximation.BooneHigman.Metabelian.ElemFP
