import GroupApproximation.Steinberg.Basic
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.MoritaGroup

/-!
# Commutator calculus in Steinberg groups (lane LVCohnK2)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  For the Morita
invariance of stable `K₂` (Ara–Brustenga–Cortiñas 2009, ultramatricial stages of the Cohn algebra)
the generators `x_{(i,k),(i,l)}(a)` of `St_{I×J}(R)` with equal first coordinates are sent to the
"diagonal" commutators `⁅x_{ip}(A), x_{pi}(E)⁆` of `St_I(M_J(R))` with `E A = 0`.  This file proves,
for an arbitrary ring `M`, the identities these commutators satisfy:

* `x_conj_adjacent`, `x_conj_adjacent'`: conjugation of adjacent root elements;
* `commute_x_of_mul_eq_zero`: adjacent root elements with `a b = 0` commute;
* `commutator_switch`: `⁅x_{ij}(A), x_{ji}(B₁B₂)⁆ = ⁅x_{ip}(AB₁), x_{pi}(B₂)⁆` when `B₂ A = 0`;
* `diag_eq_of_ne`: the diagonal commutator does not depend on the auxiliary index;
* `diag_add`: additivity in `A`;
* `commutator_diag_x`, `commutator_x_diag`: `⁅D, x_{ij}(N)⁆ = x_{ij}(A E N)` and
  `⁅x_{si}(N), D⁆ = x_{si}(N A E)`;
* `diag_commute_x`: `D` commutes with root elements away from `i` and `p`.
-/

namespace GroupApproximation.Full.LVCohnK2

open SteinbergGroup
open scoped commutatorElement

variable {I : Type*} [Fintype I] [DecidableEq I] {M : Type*} [Ring M]

/-- `x_{ij}(a) x_{jk}(b) x_{ij}(a)⁻¹ = x_{ik}(ab) x_{jk}(b)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem x_conj_adjacent (i j k : I) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : M) :
    x i j hij a * x j k hjk b * (x i j hij a)⁻¹ = x i k hik (a * b) * x j k hjk b := by
  rw [← x_commutator i j k hij hjk hik a b]
  exact conj_eq_commutator_mul _ _

/-- `x_{jk}(b) x_{ij}(a) x_{jk}(b)⁻¹ = x_{ik}(-(ab)) x_{ij}(a)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem x_conj_adjacent' (i j k : I) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : M) :
    x j k hjk b * x i j hij a * (x j k hjk b)⁻¹ = x i k hik (-(a * b)) * x i j hij a := by
  rw [x_neg i k hik (a * b), ← x_commutator i j k hij hjk hik a b]
  exact conj_eq_inv_commutator_mul _ _

/-- Adjacent root elements `x_{ij}(a)`, `x_{jk}(b)` with `a b = 0` commute.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem commute_x_of_mul_eq_zero (i j k : I) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : M) (hab : a * b = 0) : Commute (x i j hij a) (x j k hjk b) := by
  have h : ⁅x i j hij a, x j k hjk b⁆ = 1 :=
    (x_commutator i j k hij hjk hik a b).trans ((congrArg (x i k hik) hab).trans (x_zero i k hik))
  exact commutatorElement_eq_one_iff_mul_comm.mp h

/-- **Switching.**  `⁅x_{ij}(A), x_{ji}(B₁B₂)⁆ = ⁅x_{ip}(AB₁), x_{pi}(B₂)⁆` for distinct `i, j, p`
and `B₂ A = 0`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem commutator_switch (i j p : I) (hij : i ≠ j) (hjp : j ≠ p) (hpi : p ≠ i) (A B₁ B₂ : M)
    (hBA : B₂ * A = 0) :
    ⁅x i j hij A, x j i hij.symm (B₁ * B₂)⁆ = ⁅x i p hpi.symm (A * B₁), x p i hpi B₂⁆ := by
  have hV : ⁅x j p hjp B₁, x p i hpi B₂⁆ = x j i hij.symm (B₁ * B₂) :=
    x_commutator j p i hjp hpi hij.symm B₁ B₂
  have hXY : x i j hij A * x j p hjp B₁ * (x i j hij A)⁻¹ =
      x i p hpi.symm (A * B₁) * x j p hjp B₁ :=
    x_conj_adjacent i j p hij hjp hpi.symm A B₁
  have hXZ : Commute (x i j hij A) (x p i hpi B₂) :=
    (commute_x_of_mul_eq_zero p i j hpi hij hjp.symm B₂ A hBA).symm
  have hBBAB : B₁ * B₂ * (A * B₁) = 0 := by
    rw [mul_assoc B₁ B₂ (A * B₁), ← mul_assoc B₂ A B₁, hBA, zero_mul, mul_zero]
  have hUV : Commute (x i p hpi.symm (A * B₁)) (x j i hij.symm (B₁ * B₂)) :=
    (commute_x_of_mul_eq_zero j i p hij.symm hpi.symm hjp (B₁ * B₂) (A * B₁) hBBAB).symm
  have hVZ : Commute (x j i hij.symm (B₁ * B₂)) (x p i hpi B₂) :=
    x_commute_of_ne j i p i hij.symm hpi hpi.symm hij (B₁ * B₂) B₂
  exact commutator_switch_aux (x i j hij A) (x j p hjp B₁) (x p i hpi B₂)
    (x i p hpi.symm (A * B₁)) (x j i hij.symm (B₁ * B₂)) hV hXY hXZ hUV hVZ

/-- The diagonal commutator `⁅x_{ip}(A), x_{pi}(E)⁆` with `E A = 0` does not depend on `p ≠ i`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem diag_eq_of_ne (i p q : I) (hip : i ≠ p) (hqi : q ≠ i) (A E : M) (hEA : E * A = 0) :
    ⁅x i p hip A, x p i hip.symm E⁆ = ⁅x i q hqi.symm A, x q i hqi E⁆ := by
  by_cases hpq : p = q
  · subst hpq
    rfl
  · have h := commutator_switch i p q hip hpq hqi A 1 E hEA
    simpa only [one_mul, mul_one] using h

/-- **Additivity.**  `⁅x_{ip}(A + A'), x_{pi}(E)⁆ = ⁅x_{ip}(A), x_{pi}(E)⁆ ⁅x_{ip}(A'), x_{pi}(E)⁆`
when `E A = E A' = 0` and some index `q` differs from `i` and `p`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem diag_add (i p q : I) (hip : i ≠ p) (hqi : q ≠ i) (hqp : q ≠ p) (A A' E : M)
    (hEA : E * A = 0) (hEA' : E * A' = 0) :
    ⁅x i p hip (A + A'), x p i hip.symm E⁆ =
      ⁅x i p hip A, x p i hip.symm E⁆ * ⁅x i p hip A', x p i hip.symm E⁆ := by
  have hG := diag_eq_of_ne i p q hip hqi A E hEA
  have h1 : Commute (x i p hip A') (x i q hqi.symm A) :=
    x_commute_of_ne i p i q hip hqi.symm hip.symm hqi A' A
  have h2 : Commute (x i p hip A') (x q i hqi E) :=
    (commute_x_of_mul_eq_zero q i p hqi hip hqp E A' hEA').symm
  have h3 : Commute (x i p hip A') ⁅x i p hip A, x p i hip.symm E⁆ := by
    rw [hG]
    exact commute_commutatorElement h1 h2
  rw [add_comm A A', ← x_mul i p hip A' A]
  exact commutator_mul_left_of_commute _ _ _ h3

/-- `⁅⁅x_{ip}(A), x_{pi}(E)⁆, x_{ij}(N)⁆ = x_{ij}(A (E N))` for distinct `i, p, j` and `E A = 0`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem commutator_diag_x (i p j : I) (hip : i ≠ p) (hij : i ≠ j) (hpj : p ≠ j) (A E N : M)
    (hEA : E * A = 0) :
    ⁅⁅x i p hip A, x p i hip.symm E⁆, x i j hij N⁆ = x i j hij (A * (E * N)) := by
  have hZY : (x p i hip.symm E)⁻¹ * x i j hij N * x p i hip.symm E =
      x p j hpj (-(E * N)) * x i j hij N := by
    have h := x_conj_adjacent p i j hip.symm hij hpj (-E) N
    rw [x_neg p i hip.symm E, inv_inv, neg_mul E N] at h
    exact h
  have hXP : (x i p hip A)⁻¹ * x p j hpj (-(E * N)) * x i p hip A =
      x i j hij (A * (E * N)) * x p j hpj (-(E * N)) := by
    have h := x_conj_adjacent i p j hip hpj hij (-A) (-(E * N))
    rw [x_neg i p hip A, inv_inv, neg_mul_neg A (E * N)] at h
    exact h
  have hXY : Commute (x i p hip A) (x i j hij N) :=
    x_commute_of_ne i p i j hip hij hip.symm hij.symm A N
  have hEAEN : E * (A * (E * N)) = 0 := by rw [← mul_assoc E A (E * N), hEA, zero_mul]
  have hZW : Commute (x p i hip.symm E) (x i j hij (A * (E * N))) :=
    commute_x_of_mul_eq_zero p i j hip.symm hij hpj E (A * (E * N)) hEAEN
  have hZP : Commute (x p i hip.symm E) (x p j hpj (-(E * N))) :=
    x_commute_of_ne p i p j hip.symm hpj hip hpj.symm E (-(E * N))
  have hZY' : x p i hip.symm E * x i j hij N * (x p i hip.symm E)⁻¹ =
      (x p j hpj (-(E * N)))⁻¹ * x i j hij N := by
    rw [x_neg p j hpj (E * N), inv_inv]
    exact x_conj_adjacent p i j hip.symm hij hpj E N
  have hXW : Commute (x i p hip A) (x i j hij (A * (E * N))) :=
    x_commute_of_ne i p i j hip hij hip.symm hij.symm A (A * (E * N))
  exact commutator_commutator_right_aux (x i p hip A) (x i j hij N) (x p i hip.symm E)
    (x p j hpj (-(E * N))) (x i j hij (A * (E * N))) hZY hXP hXY hZW hZP hZY' hXW

/-- `⁅x_{si}(N), ⁅x_{ip}(A), x_{pi}(E)⁆⁆ = x_{si}(N A E)` for distinct `s, i, p` and `E A = 0`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem commutator_x_diag (s i p : I) (hsi : s ≠ i) (hip : i ≠ p) (hsp : s ≠ p) (N A E : M)
    (hEA : E * A = 0) :
    ⁅x s i hsi N, ⁅x i p hip A, x p i hip.symm E⁆⁆ = x s i hsi (N * A * E) := by
  have hXY : (x i p hip A)⁻¹ * x s i hsi N * x i p hip A =
      x s p hsp (N * A) * x s i hsi N := by
    have h := x_conj_adjacent' s i p hsi hip hsp N (-A)
    rw [x_neg i p hip A, inv_inv, mul_neg N A, neg_neg] at h
    exact h
  have hZY : Commute (x p i hip.symm E) (x s i hsi N) :=
    x_commute_of_ne p i s i hip.symm hsi hsi.symm hip E N
  have hZW : x p i hip.symm E * x s p hsp (N * A) * (x p i hip.symm E)⁻¹ =
      (x s i hsi (N * A * E))⁻¹ * x s p hsp (N * A) := by
    have h := x_conj_adjacent' s p i hsp hip.symm hsi (N * A) E
    rw [x_neg s i hsi (N * A * E)] at h
    exact h
  have hNAEA : N * A * E * A = 0 := by rw [mul_assoc (N * A) E A, hEA, mul_zero]
  have hXT : Commute (x i p hip A) (x s i hsi (N * A * E)) :=
    (commute_x_of_mul_eq_zero s i p hsi hip hsp (N * A * E) A hNAEA).symm
  exact commutator_left_commutator_aux (x i p hip A) (x s i hsi N) (x p i hip.symm E)
    (x s p hsp (N * A)) (x s i hsi (N * A * E)) hXY hZY hZW hXT

/-- `⁅x_{ip}(A), x_{pi}(E)⁆` commutes with `x_{st}(N)` when `s, t ∉ {i}` and `s, t ≠ p`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem diag_commute_x (i p s t : I) (hip : i ≠ p) (hst : s ≠ t) (hps : p ≠ s) (hti : t ≠ i)
    (his : i ≠ s) (htp : t ≠ p) (A E N : M) :
    Commute ⁅x i p hip A, x p i hip.symm E⁆ (x s t hst N) := by
  have h1 : Commute (x s t hst N) (x i p hip A) :=
    (x_commute_of_ne i p s t hip hst hps hti A N).symm
  have h2 : Commute (x s t hst N) (x p i hip.symm E) :=
    (x_commute_of_ne p i s t hip.symm hst his htp E N).symm
  exact (commute_commutatorElement h1 h2).symm

end GroupApproximation.Full.LVCohnK2
