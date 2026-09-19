import GroupApproximation.ClassTransposition.Presentation.RelWin

/-!
# Every instance of the relation families holds in `H P`

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, §3, the
Theorem): together with the window relations (`RelWin`), Lemma FC (`fc_all`) gives every valid
instance of the families (a)–(d) at every level and position (`inst_all`), for a finite set `P`
of primes (`BddAbove (P' P)`, all elements `≥ 2`, and `2 ∉ P`).
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

variable {P : Set ℕ}

section All

variable (hB : BddAbove (P' P)) (hP2 : 2 ∉ P) (hpos : ∀ p ∈ P' P, 2 ≤ p)
include hB hP2 hpos

theorem fsp_all {n i j p q : ℕ} (hij : i < j) (hj : j < n) (hp : p ∈ P' P) (hq : q ∈ P' P) :
    toH P n [.split i p, .split (j + p - 1) q] = toH P n [.split j q, .split i p] := by
  have hp1 := hpos p hp
  rcases Nat.lt_or_ge (j + 1) n with h | h
  · exact (fsp_front hij h hp hq (by omega)).2
      (fc_all hB hP2 hpos (Or.inl ⟨p, hp, rfl⟩) (by omega) _ (show i + 1 + 1 ≤ j + 1 by omega))
  · have hjn : j + 1 = n := by omega
    rcases hq with rfl | hq'
    · exact fsp_tail_two hij hjn hp (by omega)
    · exact (fsp_tail hij hjn hp hq' (ne_two_of_mem hP2 hq') (by omega)
        (by have := hpos q (mem_P'_of_mem hq'); omega)).2
        (fc_all hB hP2 hpos (Or.inl ⟨p, hp, rfl⟩) (by omega) _ (show i + 1 + 1 ≤ j + 1 by omega))

theorem dl_all {n k i p : ℕ} (hik : i < k) (hk : k + 2 ≤ n) (hp : p ∈ P' P) :
    toH P n [.swap k, .split i p] = toH P n [.split i p, .swap (k + p - 1)] := by
  have hp1 := hpos p hp
  rcases Nat.lt_or_ge (k + 2) n with h | h
  · exact (dl_front hik h hp (by omega)).2
      (fc_all hB hP2 hpos (Or.inl ⟨p, hp, rfl⟩) (by omega) _ (show i + 1 + 1 ≤ k + 1 by omega))
  · exact (dl_tail hik (by omega) hp (by omega)).2
      (fc_all hB hP2 hpos (Or.inl ⟨p, hp, rfl⟩) (by omega) _ (show i + 1 + 1 ≤ k + 1 by omega))

theorem dr_all {n k i p : ℕ} (hki : k + 1 < i) (hi : i < n) (hp : p ∈ P' P) :
    toH P n [.swap k, .split i p] = toH P n [.split i p, .swap k] := by
  have hp1 := hpos p hp
  rcases Nat.lt_or_ge (i + 1) n with h | h
  · exact (dr_front hki h hp (by omega)).2
      (fc_all hB hP2 hpos (Or.inr rfl) (by omega) _ (show k + 1 + 2 ≤ i + 1 by omega))
  · have hin : i + 1 = n := by omega
    rcases hp with rfl | hp'
    · exact dr_tail_two hki hin
    · exact (dr_tail hki hin hp' (ne_two_of_mem hP2 hp') (by omega)).2
        (fc_all hB hP2 hpos (Or.inr rfl) (by omega) _ (show k + 1 + 2 ≤ i + 1 by omega))

theorem fsw_all {n k l : ℕ} (hkl : k + 2 ≤ l) (hl : l + 2 ≤ n) :
    toH P n [.swap k, .swap l] = toH P n [.swap l, .swap k] := by
  rcases Nat.lt_or_ge (l + 2) n with h | h
  · exact (fsw_front hkl h).2
      (fc_all hB hP2 hpos (Or.inr rfl) (by omega) _ (show k + 1 + 2 ≤ l + 1 by omega))
  · exact (fsw_tail hkl (by omega)).2
      (fc_all hB hP2 hpos (Or.inr rfl) (by omega) _ (show k + 1 + 2 ≤ l + 1 by omega))

/-- Every valid instance of the relation families holds in `H P`. -/
theorem inst_all {x : Inst} (hv : x.Valid P) : toH P x.lev x.sides.1 = toH P x.lev x.sides.2 := by
  cases x with
  | sq n k => exact sq_all n k hv
  | br n k => exact br_all n k hv
  | fsw n k l => exact fsw_all hB hP2 hpos hv.1 hv.2
  | fsp n i j p q => exact fsp_all hB hP2 hpos hv.1 hv.2.1 hv.2.2.1 hv.2.2.2
  | dl n k i p => exact dl_all hB hP2 hpos hv.1 hv.2.1 hv.2.2
  | dr n k i p => exact dr_all hB hP2 hpos hv.1 hv.2.1 hv.2.2
  | dk n k p => exact dk_all hB hv.2 n k hv.1
  | dk1 n k p => exact dk1_all hB hv.2 n k hv.1
  | cx n i p q =>
    exact cx_all hB hv.2.1 hv.2.2.1 hv.2.2.2 (by have := hpos p hv.2.1; omega)
      (by have := hpos q hv.2.2.1; omega) n i hv.1

end All

end GroupApproximation.ClassTransposition.Presentation
