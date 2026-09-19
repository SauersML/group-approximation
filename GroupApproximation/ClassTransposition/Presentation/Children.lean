import GroupApproximation.ClassTransposition.Presentation.Canon

/-!
# Uniform split words on consecutive cells

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, Fact O
step O1, in `H P`).

`KUstmt P K`: every split word on one cell whose leaves all have `K` times the cell's modulus is,
in `H P`, the canonical word `D o qs` (for any list of primes `qs` with product `K`) followed by a
swap word inside the block. `children` extends this from one cell to `c` consecutive cells of equal
modulus: decompose into the first cell and the rest (`decomp`), apply it to each, and move the
first swap word right past the rest (`swaps_locS`).
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

variable {P : Set ℕ}

/-- The uniform-tree statement for the ratio `K`. -/
def KUstmt (P : Set ℕ) (K : ℕ) : Prop :=
  ∀ (qs : List ℕ), (∀ q ∈ qs, q ∈ P' P) → qs.prod = K →
  ∀ (b : List Box) (o : ℕ) (t : List Move), IsPart b → o < b.length → LocS o (o + 1) t →
    PrimesIn P t → (∀ F, b[o]? = some F → Unif (real b t) o (o + 1 + growth t) ((K : ℤ) * F.m)) →
    growth t + 1 = K ∧ ∃ ρ : List ℕ, (∀ k ∈ ρ, o ≤ k ∧ k + 1 < o + 1 + growth t) ∧
      Eqv P b.length t (D o qs ++ swaps 0 ρ)

theorem ok_of_primesIn (hpos : ∀ p ∈ P' P, 2 ≤ p) : ∀ w : List Move, PrimesIn P w → ∀ m ∈ w, m.Ok
  | [], _, _, h => absurd h List.not_mem_nil
  | .split _ p :: w, ⟨hp, hw⟩, m, h => by
    rcases List.mem_cons.1 h with rfl | h
    · have := hpos p hp; show 0 < p; omega
    · exact ok_of_primesIn hpos w hw m h
  | .swap _ :: w, hw, m, h => by
    rcases List.mem_cons.1 h with rfl | h
    · trivial
    · exact ok_of_primesIn hpos w hw m h

theorem swaps_append (i : ℕ) (u v : List ℕ) : swaps i (u ++ v) = swaps i u ++ swaps i v := by
  simp [swaps]

theorem Ch_one (o : ℕ) (qs : List ℕ) : Ch o 1 qs = D o qs := by simp [Ch]

theorem Ch_succ_left (o c : ℕ) (qs : List ℕ) : Ch o (c + 1) qs = D o qs ++ Ch (o + qs.prod) c qs := by
  rw [add_comm c 1, Ch_add, Ch_one, one_mul]

theorem primesIn_swaps (σ : List ℕ) : PrimesIn P (swaps 0 σ) := primesIn_swaps_at 0 σ

section Children

variable (hB : BddAbove (P' P)) (hP2 : 2 ∉ P) (hpos : ∀ p ∈ P' P, 2 ≤ p)
include hB hP2 hpos

/-- **Children.** The uniform-tree statement on `c` consecutive cells of modulus `m`. -/
theorem children {K : ℕ} (hK : KUstmt P K) (qs : List ℕ) (hqs : ∀ q ∈ qs, q ∈ P' P)
    (hqK : qs.prod = K) (m : ℤ) : ∀ (c : ℕ) (b : List Box) (o : ℕ) (S : List Move), IsPart b →
    o + c ≤ b.length → LocS o (o + c) S → PrimesIn P S →
    (∀ j, o ≤ j → j < o + c → ∀ F, b[j]? = some F → F.m = m) →
    Unif (real b S) o (o + c + growth S) ((K : ℤ) * m) →
    growth S + c = c * K ∧ ∃ ρ : List ℕ, (∀ k ∈ ρ, o ≤ k ∧ k + 1 < o + c + growth S) ∧
      Eqv P b.length S (Ch o c qs ++ swaps 0 ρ)
  | 0, b, o, S, _, _, hS, _, _, _ => by
    have hS0 : S = [] := by
      rcases S with _ | ⟨_ | _, _⟩
      · rfl
      · obtain ⟨h1, h2, -⟩ := hS; omega
      · exact (show False from hS).elim
    subst hS0
    refine ⟨by simp [growth], [], by simp, ?_⟩
    rw [Ch_zero]
    exact Eqv.refl _ _
  | c + 1, b, o, S, hb, hc, hS, hpS, hm, hU => by
    have hqs1 : ∀ q ∈ qs, 1 ≤ q := fun q hq => by have := hpos q (hqs q hq); omega
    obtain ⟨A, B, hA, hB', hpA, hpB, hg, e⟩ :=
      decomp hB hP2 hpos o S b.length (o + 1) (o + c + 1) (by omega) (by omega) (by omega) hS hpS
    have hBlo : LocS o (o + c + 1 + growth A) B := locS_mono_lo (by omega) hB'
    have hAB : LocB o (o + c + 1) (A ++ B) :=
      (locB_append o (o + c + 1) A B).2 ⟨locB_of_locS (locS_mono hA (by omega)), locB_of_locS hBlo⟩
    have hpAB : PrimesIn P (A ++ B) := (primesIn_append A B).2 ⟨hpA, hpB⟩
    have eSAB : Eqv P b.length S (A ++ B) :=
      eqv_of_toH hpos o (hi := o + c + 1) (by omega) (locB_of_locS hS) hAB hpS hpAB
        (by rw [growth_append, hg]) e
    have hr : real b S = real (real b A) B := by
      rw [← real_append]
      exact eSAB.real_eq hpos hP2 (by omega) (valW_of_locB hpos o S b.length (o + c + 1)
        (by omega) (locB_of_locS hS) hpS) (valW_of_locB hpos o _ b.length (o + c + 1) (by omega)
        hAB hpAB) hb rfl
    have hlA : (real b A).length = b.length + growth A := by
      rw [length_real, levW_locB hpos o A b.length (o + 1) (by omega) (locB_of_locS hA) hpA]
    -- the first cell
    have hUA : ∀ F, b[o]? = some F → Unif (real b A) o (o + 1 + growth A) ((K : ℤ) * F.m) := by
      intro F hF j hj1 hj2 G hG
      rw [hm o le_rfl (by omega) F hF]
      refine hU j hj1 (by omega) G ?_
      rw [hr, real_get_left hpos B (real b A) (o + c + 1 + growth A) (locB_of_locS hB') hpB
        (by omega) j hj2]
      exact hG
    obtain ⟨hgA, ρA, hρA, eA⟩ := hK qs hqs hqK b o A hb (by omega) hA hpA hUA
    -- the other cells
    have hB1 : LocS (o + K) (o + K + c) B := by
      rw [show o + K + c = o + c + 1 + growth A by omega, show o + K = o + 1 + growth A by omega]
      exact hB'
    have hm1 : ∀ j, o + K ≤ j → j < o + K + c → ∀ F, (real b A)[j]? = some F → F.m = m := by
      intro j hj1 hj2 F hF
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + growth A := ⟨j - growth A, by omega⟩
      rw [real_get_right hpos A b (o + 1) (locB_of_locS hA) hpA (by omega) j' (by omega)] at hF
      exact hm j' (by omega) (by omega) F hF
    have hU1 : Unif (real (real b A) B) (o + K) (o + K + c + growth B) ((K : ℤ) * m) := by
      rw [← hr]; exact hU.mono (by omega) (by omega)
    obtain ⟨hgB, ρB, hρB, eB⟩ := children hK qs hqs hqK m c (real b A) (o + K) B
      (isPart_real hb A (ok_of_primesIn hpos A hpA)) (by omega) hB1 hpB hm1 hU1
    -- combine
    have hlD : levW b.length (D o qs) = (real b A).length := by
      rw [hlA, levW_locB hpos o (D o qs) b.length (o + 1) (by omega)
        (locB_of_locS (locS_D qs hqs1 o)) (primesIn_D qs hqs o)]
      have := growth_D qs hqs1 o
      omega
    rw [← hlD] at eB
    have eC := swaps_locS hB hP2 hpos (o + K) B ρA (levW b.length (D o qs)) (o + K + c)
      (by omega) hB1 hpB fun k hk => by have := hρA k hk; omega
    have e1 := eSAB.trans (eA.append_right B)
    have e2 := Eqv.append_left (D o qs) (eC.trans (eB.append_right (swaps 0 ρA)))
    refine ⟨by rw [← hg, add_one_mul]; omega, ρB ++ ρA, ?_, ?_⟩
    · intro k hk
      rcases List.mem_append.1 hk with hk | hk
      · have := hρB k hk; omega
      · have := hρA k hk; omega
    · refine e1.trans ((Eqv.of_eq (List.append_assoc _ _ _)).trans (e2.trans (Eqv.of_eq ?_)))
      rw [Ch_succ_left, hqK, swaps_append]
      simp only [List.append_assoc]

end Children

end GroupApproximation.ClassTransposition.Presentation
