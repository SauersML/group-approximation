import GroupApproximation.Leavitt.LeavittWords
import Mathlib.Tactic.NoncommRing
import GroupApproximation.Meta.AxiomGuard

/-!
# Frame cone: the sibling complement of a word and the coordinate unit `Z`

Khanh (arXiv:2609.08428), proof of Lemma `lem:word-multiplier`:

> For a word `η = c_1⋯c_h`, `h ≥ 1`, let `s_ℓ = c_1⋯c_{ℓ-1}c'_ℓ` … The words
> `η, s_1, …, s_h` form a complete leaf set. Consequently `ker η^* = ⊕_ℓ s_ℓ R` …
> If `y = a_ix` and `b = η_i^*`, then `by = 1`, and `R ⊕ ker b ⇄ R`,
> `(t,z) ↦ yt + z` and `u ↦ (bu, u - ybu)` are mutually inverse.

Instead of the sibling basis we package `ker η^*` by one isometry `s` (so `s' s = 1`,
`s s' + η η^* = 1`, `η^* s = 0`), built by induction on `η` (`exists_complement`): the
sibling tree of `c :: a` is `c'` together with `c` followed by the siblings of `a`.
With `R ≅ R ⊕ R` via `(s_0, s_1)`, the map `(t, r) ↦ y t + s r` becomes the element
`Z = y t_0 + s t_1`, and the inverse formula above becomes `Z' = s_0 b + s_1 s' (1 - y b)`
(`exists_coordinate_unit`), with `Z s_0 = y`.

Lane LVFrame (leaf T1c of the `K₂(4, L) = ⊥` tree, `simple_kazhdan_sofic_group.tex` l.733-735):
port of the foreign module `LeavittK2/FrameCone/Complement.lean`, whose closure contains WIP commits.
-/

namespace GroupApproximation.Full.LVFrame

variable {A : Type*} [Ring A] (L : LeavittFamily A)

theorem complement_nil_zero :
    ∃ s s' : A, L.wordT [0] * s = 0 ∧ s' * s = 1 ∧ s * s' + L.wordS [0] * L.wordT [0] = 1 := by
  refine ⟨L.s1, L.t1, ?_, L.t1_s1, ?_⟩
  · simp only [LeavittFamily.wordT_cons, LeavittFamily.wordT_nil, LeavittFamily.t_zero, one_mul,
      L.t0_s1]
  · simp only [LeavittFamily.wordT_cons, LeavittFamily.wordT_nil, LeavittFamily.t_zero, one_mul,
      LeavittFamily.wordS_cons, LeavittFamily.wordS_nil, LeavittFamily.s_zero, mul_one]
    rw [add_comm]
    exact L.sum_range

#audit_axioms GroupApproximation.Full.LVFrame.complement_nil_zero

theorem complement_nil_one :
    ∃ s s' : A, L.wordT [1] * s = 0 ∧ s' * s = 1 ∧ s * s' + L.wordS [1] * L.wordT [1] = 1 := by
  refine ⟨L.s0, L.t0, ?_, L.t0_s0, ?_⟩
  · simp only [LeavittFamily.wordT_cons, LeavittFamily.wordT_nil, LeavittFamily.t_one, one_mul,
      L.t1_s0]
  · simp only [LeavittFamily.wordT_cons, LeavittFamily.wordT_nil, LeavittFamily.t_one, one_mul,
      LeavittFamily.wordS_cons, LeavittFamily.wordS_nil, LeavittFamily.s_one, mul_one]
    exact L.sum_range

#audit_axioms GroupApproximation.Full.LVFrame.complement_nil_one

theorem complement_cons_zero (a : List (Fin 2)) (r r' : A) (h1 : L.wordT a * r = 0)
    (h2 : r' * r = 1) (h3 : r * r' + L.wordS a * L.wordT a = 1) :
    ∃ s s' : A, L.wordT (0 :: a) * s = 0 ∧ s' * s = 1 ∧
      s * s' + L.wordS (0 :: a) * L.wordT (0 :: a) = 1 := by
  refine ⟨L.s1 * L.t0 + L.s0 * r * L.t1, L.s0 * L.t1 + L.s1 * r' * L.t0, ?_, ?_, ?_⟩
  · simp only [LeavittFamily.wordT_cons, LeavittFamily.t_zero]
    calc
      L.wordT a * L.t0 * (L.s1 * L.t0 + L.s0 * r * L.t1) =
          L.wordT a * (L.t0 * L.s1) * L.t0 + L.wordT a * (L.t0 * L.s0) * r * L.t1 := by
        noncomm_ring
      _ = L.wordT a * r * L.t1 := by
        rw [L.t0_s1, L.t0_s0]
        noncomm_ring
      _ = 0 := by
        rw [h1]
        noncomm_ring
  · calc
      (L.s0 * L.t1 + L.s1 * r' * L.t0) * (L.s1 * L.t0 + L.s0 * r * L.t1) =
          L.s0 * (L.t1 * L.s1) * L.t0 + L.s0 * (L.t1 * L.s0) * r * L.t1 +
            L.s1 * r' * (L.t0 * L.s1) * L.t0 + L.s1 * r' * (L.t0 * L.s0) * r * L.t1 := by
        noncomm_ring
      _ = L.s0 * L.t0 + L.s1 * (r' * r) * L.t1 := by
        rw [L.t1_s1, L.t1_s0, L.t0_s1, L.t0_s0]
        noncomm_ring
      _ = L.s0 * L.t0 + L.s1 * L.t1 := by
        rw [h2]
        noncomm_ring
      _ = 1 := L.sum_range
  · simp only [LeavittFamily.wordT_cons, LeavittFamily.t_zero, LeavittFamily.wordS_cons,
      LeavittFamily.s_zero]
    calc
      (L.s1 * L.t0 + L.s0 * r * L.t1) * (L.s0 * L.t1 + L.s1 * r' * L.t0) +
          L.s0 * L.wordS a * (L.wordT a * L.t0) =
          L.s1 * (L.t0 * L.s0) * L.t1 + L.s1 * (L.t0 * L.s1) * r' * L.t0 +
            L.s0 * r * (L.t1 * L.s0) * L.t1 + L.s0 * r * (L.t1 * L.s1) * r' * L.t0 +
            L.s0 * (L.wordS a * L.wordT a) * L.t0 := by
        noncomm_ring
      _ = L.s1 * L.t1 + L.s0 * (r * r' + L.wordS a * L.wordT a) * L.t0 := by
        rw [L.t0_s0, L.t0_s1, L.t1_s0, L.t1_s1]
        noncomm_ring
      _ = L.s0 * L.t0 + L.s1 * L.t1 := by
        rw [h3]
        noncomm_ring
      _ = 1 := L.sum_range

#audit_axioms GroupApproximation.Full.LVFrame.complement_cons_zero

theorem complement_cons_one (a : List (Fin 2)) (r r' : A) (h1 : L.wordT a * r = 0)
    (h2 : r' * r = 1) (h3 : r * r' + L.wordS a * L.wordT a = 1) :
    ∃ s s' : A, L.wordT (1 :: a) * s = 0 ∧ s' * s = 1 ∧
      s * s' + L.wordS (1 :: a) * L.wordT (1 :: a) = 1 := by
  refine ⟨L.s0 * L.t1 + L.s1 * r * L.t0, L.s1 * L.t0 + L.s0 * r' * L.t1, ?_, ?_, ?_⟩
  · simp only [LeavittFamily.wordT_cons, LeavittFamily.t_one]
    calc
      L.wordT a * L.t1 * (L.s0 * L.t1 + L.s1 * r * L.t0) =
          L.wordT a * (L.t1 * L.s0) * L.t1 + L.wordT a * (L.t1 * L.s1) * r * L.t0 := by
        noncomm_ring
      _ = L.wordT a * r * L.t0 := by
        rw [L.t1_s0, L.t1_s1]
        noncomm_ring
      _ = 0 := by
        rw [h1]
        noncomm_ring
  · calc
      (L.s1 * L.t0 + L.s0 * r' * L.t1) * (L.s0 * L.t1 + L.s1 * r * L.t0) =
          L.s1 * (L.t0 * L.s0) * L.t1 + L.s1 * (L.t0 * L.s1) * r * L.t0 +
            L.s0 * r' * (L.t1 * L.s0) * L.t1 + L.s0 * r' * (L.t1 * L.s1) * r * L.t0 := by
        noncomm_ring
      _ = L.s1 * L.t1 + L.s0 * (r' * r) * L.t0 := by
        rw [L.t0_s0, L.t0_s1, L.t1_s0, L.t1_s1]
        noncomm_ring
      _ = L.s0 * L.t0 + L.s1 * L.t1 := by
        rw [h2]
        noncomm_ring
      _ = 1 := L.sum_range
  · simp only [LeavittFamily.wordT_cons, LeavittFamily.t_one, LeavittFamily.wordS_cons,
      LeavittFamily.s_one]
    calc
      (L.s0 * L.t1 + L.s1 * r * L.t0) * (L.s1 * L.t0 + L.s0 * r' * L.t1) +
          L.s1 * L.wordS a * (L.wordT a * L.t1) =
          L.s0 * (L.t1 * L.s1) * L.t0 + L.s0 * (L.t1 * L.s0) * r' * L.t1 +
            L.s1 * r * (L.t0 * L.s1) * L.t0 + L.s1 * r * (L.t0 * L.s0) * r' * L.t1 +
            L.s1 * (L.wordS a * L.wordT a) * L.t1 := by
        noncomm_ring
      _ = L.s0 * L.t0 + L.s1 * (r * r' + L.wordS a * L.wordT a) * L.t1 := by
        rw [L.t0_s0, L.t0_s1, L.t1_s0, L.t1_s1]
        noncomm_ring
      _ = L.s0 * L.t0 + L.s1 * L.t1 := by
        rw [h3]
        noncomm_ring
      _ = 1 := L.sum_range

#audit_axioms GroupApproximation.Full.LVFrame.complement_cons_one

end GroupApproximation.Full.LVFrame
