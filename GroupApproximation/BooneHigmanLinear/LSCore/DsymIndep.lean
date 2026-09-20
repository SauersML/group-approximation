import GroupApproximation.BooneHigmanLinear.LSCore.Dsym
import GroupApproximation.Meta.AxiomGuard

/-!
# Root independence of Dennis–Stein symbols from their centrality (k2-poly H.L4)

For disjoint index pairs `(i, j)` and `(k, l)`, the Weyl element `W = w_jl(1) w_ik(1)` conjugates
`x_ij(c) ↦ x_kl(c)` and `x_ji(c) ↦ x_lk(c)`, with no signs (`wSwap_x_ij`, `wSwap_x_ji`). So it
conjugates `⟨a, b⟩_(i,j)` to `⟨a, b⟩_(k,l)` (`wSwap_dsym`). If `⟨a, b⟩_(i,j)` is central, the
two symbols are equal (`dsym_eq_of_central`). No bound on `|I|` is needed.
* `dsymRootIndep_of_symbolFacts`: `DsymRootIndep` from the `dsym_central` field of `SymbolFacts`.
* `dsym_mem_zAlpha_of_symbolFacts`: L–S (2), `⟨a, m⟩_α ∈ Z_α(A, M)`, from `SymbolFacts` and
  Theorem 4.2 only.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace LSCore

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.RelGen (Thm42Statement)
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h w_conj_x_row_i
  w_conj_x_col_i)

section Swap

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

variable (R) in
/-- The Weyl element `w_jl(1) w_ik(1)`. -/
def wSwap {i j k l : I} (hik : i ≠ k) (hjl : j ≠ l) : SteinbergGroup I R :=
  w j l hjl 1 * w i k hik 1

theorem wSwap_conj {i j k l : I} (hik : i ≠ k) (hjl : j ≠ l) (y : SteinbergGroup I R) :
    wSwap R hik hjl * y * (wSwap R hik hjl)⁻¹ =
      w j l hjl 1 * (w i k hik 1 * y * (w i k hik 1)⁻¹) * (w j l hjl 1)⁻¹ := by
  simp only [wSwap, mul_inv_rev, mul_assoc]

theorem wSwap_x_ij {i j k l : I} (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k) (hjl : j ≠ l)
    (hkj : k ≠ j) (c : R) :
    wSwap R hik hjl * x i j hij c * (wSwap R hik hjl)⁻¹ = x k l hkl c := by
  rw [wSwap_conj, w_conj_x_row_i i k j hik hij hkj, w_conj_x_col_i j l k hjl hkj hkl]
  congr 1
  simp

theorem wSwap_x_ji {i j k l : I} (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k) (hjl : j ≠ l)
    (hjk : j ≠ k) (c : R) :
    wSwap R hik hjl * x j i hij.symm c * (wSwap R hik hjl)⁻¹ = x l k hkl.symm c := by
  rw [wSwap_conj, w_conj_x_col_i i k j hik hij.symm hjk,
    w_conj_x_row_i j l k hjl hjk hkl.symm]
  congr 1
  simp

/-- Conjugation by `W` moves the symbol `⟨a, b⟩_(i,j)` to `⟨a, b⟩_(k,l)`. -/
theorem wSwap_dsym {i j k l : I} (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k) (hjk : j ≠ k)
    (hjl : j ≠ l) (a b : R) (u : Rˣ) :
    MulAut.conj (wSwap R hik hjl) (dsym i j hij a b u) = dsym k l hkl a b u := by
  have h1 : ∀ c : R, MulAut.conj (wSwap R hik hjl) (x i j hij c) = x k l hkl c := fun c => by
    rw [MulAut.conj_apply, wSwap_x_ij hij hkl hik hjl (fun e => hjk e.symm) c]
  have h2 : ∀ c : R, MulAut.conj (wSwap R hik hjl) (x j i hij.symm c) = x l k hkl.symm c :=
    fun c => by rw [MulAut.conj_apply, wSwap_x_ji hij hkl hik hjl hjk c]
  simp only [dsym, h, w, map_mul, map_inv, h1, h2]

/-- **Root independence**: a central `⟨a, b⟩_(i,j)` equals `⟨a, b⟩_(k,l)` for disjoint pairs. -/
theorem dsym_eq_of_central {i j k l : I} (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k)
    (hjk : j ≠ k) (hjl : j ≠ l) (a b : R) (u : Rˣ)
    (hc : ∀ g : SteinbergGroup I R, Commute (dsym i j hij a b u) g) :
    dsym i j hij a b u = dsym k l hkl a b u := by
  rw [← wSwap_dsym hij hkl hik hjk hjl a b u, MulAut.conj_apply,
    ← (hc (wSwap R hik hjl)).eq, mul_inv_cancel_right]

#audit_axioms dsym_eq_of_central

/-- `DsymRootIndep` from the centrality field of `SymbolFacts`. -/
theorem dsymRootIndep_of_symbolFacts
    (hF : ∀ (i j : I) (hij : i ≠ j), SymbolFacts R i j hij) : DsymRootIndep I R := by
  intro i j k l hij hkl hik _ hjk hjl a b u hu
  exact dsym_eq_of_central hij hkl hik hjk hjl a b u ((hF i j hij).dsym_central a b u hu)

#audit_axioms dsymRootIndep_of_symbolFacts

end Swap

variable {I : Type} [Fintype I] [DecidableEq I] {A : Type} [CommRing A]

/-- **L–S (2)** from `SymbolFacts` and Theorem 4.2: `⟨a, m⟩_α ∈ Z_α(A, M)` for `|I| ≥ 5`. -/
theorem dsym_mem_zAlpha_of_symbolFacts (h42 : Thm42Statement)
    (hF : ∀ (i j : I) (hij : i ≠ j), SymbolFacts A i j hij) (h5 : 5 ≤ Fintype.card I)
    {M : Ideal A} {i j : I} (hij : i ≠ j) (a m : A) (hm : m ∈ M) (u : Aˣ)
    (hu : (u : A) = 1 + a * m) : dsym i j hij a m u ∈ zAlpha M i j :=
  dsym_mem_zAlpha h42 (dsymRootIndep_of_symbolFacts hF) h5 hij a m hm u hu

#audit_axioms dsym_mem_zAlpha_of_symbolFacts

end LSCore
end BooneHigmanLinear
end GroupApproximation
