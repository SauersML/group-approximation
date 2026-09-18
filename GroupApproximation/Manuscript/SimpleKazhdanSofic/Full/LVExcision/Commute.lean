import Mathlib.Tactic.Group
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.Products

/-!
# Steinberg generators with annihilating coefficients commute (lane LVExcision)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  This is the first
step of stable `K₂` excision for split s-unital ideals (Suslin–Wodzicki, *Excision in algebraic
K-theory*, Ann. Math. 136 (1992), Thm A; Keune, J. Algebra 54 (1978); used in Ara–Brustenga–
Cortiñas, thm:skewyao, `yaoseq6.tex` l.558-640).

The key elementary fact (Lemma C): if `f * b = b`, `d * f = 0` and `b * d = 0`, then every
generator `x_{kl}(d)` commutes with every generator `x_{ij}(b)` of `St_N(T)`, `N ≥ 3`.  The only
non-trivial case is the opposite root `(k, l) = (j, i)`, where `x_{ij}(b) = ⁅x_{im}(f), x_{mj}(b)⁆`
for a third index `m`.  We also record the two conjugation formulas used for the action on the
relative group.
-/

namespace GroupApproximation.Full.LVExcision

open SteinbergGroup
open scoped commutatorElement

variable {T : Type*} [Ring T] {N : ℕ}

/-- Adjacent roots `(i, j)`, `(j, l)` with `b * d = 0`: `x_{jl}(d)` commutes with `x_{ij}(b)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem commute_x_adj_right {b d : T} (hbd : b * d = 0) (i j l : Fin N) (hij : i ≠ j)
    (hjl : j ≠ l) (hil : i ≠ l) : Commute (x j l hjl d) (x i j hij b) := by
  have h : ⁅x i j hij b, x j l hjl d⁆ = 1 := by
    rw [x_commutator i j l hij hjl hil b d, hbd, x_zero]
  exact (commutatorElement_eq_one_iff_mul_comm.mp h).symm

/-- Adjacent roots `(k, i)`, `(i, j)` with `d * b = 0`: `x_{ki}(d)` commutes with `x_{ij}(b)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem commute_x_adj_left {b d : T} (hdb : d * b = 0) (k i j : Fin N) (hki : k ≠ i)
    (hij : i ≠ j) (hkj : k ≠ j) : Commute (x k i hki d) (x i j hij b) := by
  have h : ⁅x k i hki d, x i j hij b⁆ = 1 := by
    rw [x_commutator k i j hki hij hkj d b, hdb, x_zero]
  exact commutatorElement_eq_one_iff_mul_comm.mp h

/-- Opposite roots: `x_{ji}(d)` commutes with `x_{ij}(b)` when `f * b = b`, `d * f = 0` and
`b * d = 0`, using a third index.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii;
Suslin–Wodzicki 1992, Thm A.) -/
theorem commute_x_opposite (hN : 3 ≤ N) {b d f : T} (hfb : f * b = b) (hdf : d * f = 0)
    (hbd : b * d = 0) (i j : Fin N) (hij : i ≠ j) (hji : j ≠ i) :
    Commute (x j i hji d) (x i j hij b) := by
  obtain ⟨m, hmi, hmj⟩ := LVCohnK2.exists_ne_ne_fin hN i j
  have hA : Commute (x j i hji d) (x i m hmi.symm f) := by
    have h : ⁅x j i hji d, x i m hmi.symm f⁆ = 1 := by
      rw [x_commutator j i m hji hmi.symm hmj.symm d f, hdf, x_zero]
    exact commutatorElement_eq_one_iff_mul_comm.mp h
  have hB : Commute (x j i hji d) (x m j hmj b) := by
    have h : ⁅x m j hmj b, x j i hji d⁆ = 1 := by
      rw [x_commutator m j i hmj hji hmi b d, hbd, x_zero]
    exact (commutatorElement_eq_one_iff_mul_comm.mp h).symm
  have hC : Commute (x j i hji d) ⁅x i m hmi.symm f, x m j hmj b⁆ := by
    rw [commutatorElement_def]
    exact ((hA.mul_right hB).mul_right hA.inv_right).mul_right hB.inv_right
  have h : x i j hij b = ⁅x i m hmi.symm f, x m j hmj b⁆ := by
    rw [x_commutator i m j hmi.symm hmj hij f b, hfb]
  rw [h]
  exact hC

/-- Lemma C: if `f * b = b`, `d * f = 0` and `b * d = 0`, then `x_{kl}(d)` commutes with
`x_{ij}(b)` for all roots, `N ≥ 3`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii;
Suslin–Wodzicki 1992, Thm A.) -/
theorem commute_x_of_annihilate (hN : 3 ≤ N) {b d f : T} (hfb : f * b = b) (hdf : d * f = 0)
    (hbd : b * d = 0) (i j k l : Fin N) (hij : i ≠ j) (hkl : k ≠ l) :
    Commute (x k l hkl d) (x i j hij b) := by
  have hdb : d * b = 0 := by
    rw [← hfb, ← mul_assoc, hdf, zero_mul]
  rcases eq_or_ne j k with rfl | hjk
  · rcases eq_or_ne l i with rfl | hli
    · exact commute_x_opposite hN hfb hdf hbd _ _ _ _
    · exact commute_x_adj_right hbd _ _ _ _ _ hli.symm
  · rcases eq_or_ne l i with rfl | hli
    · exact commute_x_adj_left hdb _ _ _ _ _ hjk.symm
    · exact x_commute_of_ne k l i j hkl hij hli hjk d b

/-- Conjugating `x_{jk}(β)` by `x_{ij}(c)` gives `x_{ik}(cβ) x_{jk}(β)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem x_conj_adj_left (i j k : Fin N) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (c β : T) :
    x i j hij c * x j k hjk β * (x i j hij c)⁻¹ = x i k hik (c * β) * x j k hjk β := by
  rw [← x_commutator i j k hij hjk hik c β, commutatorElement_def]
  group

/-- Conjugating `x_{ij}(β)` by `x_{jk}(c)` gives `x_{ik}(-(βc)) x_{ij}(β)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem x_conj_adj_right (i j k : Fin N) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (β c : T) :
    x j k hjk c * x i j hij β * (x j k hjk c)⁻¹ = x i k hik (-(β * c)) * x i j hij β := by
  rw [x_neg, ← x_commutator i j k hij hjk hik β c, commutatorElement_def]
  group

end GroupApproximation.Full.LVExcision
