import GroupApproximation.ClassTransposition.Presentation.Hats
import GroupApproximation.ClassTransposition.Presentation.ShiftFC

/-!
# Far commutation in `H P`

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, §3,
Lemma FC).

The families (b), (d) for distant boxes and (a) for distant swaps are far-commutation relations
`FC gH dT τ i υ j`: conjugating the generator of type `υ` at position `j` by the generator of
the finite type `τ ∈ {X p, π}` at position `i` raises the position by `dT τ`. The relators give
them at positions `i ∈ {1, 2}` and distances `wT τ`, `wT τ + 1` (`fc_base`). Lemma FC gives all
of them (`fc_all`).
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

variable {P : Set ℕ}

/-- The position shift of a type: `p - 1` for `X p`, `0` otherwise. -/
def dT : Ty P → ℕ
  | Sum.inl p => p.1 - 1
  | Sum.inr _ => 0

/-- The width of a type: `2` for `π`, `1` otherwise. -/
def wT : Ty P → ℕ
  | Sum.inr (Sum.inr false) => 2
  | _ => 1

/-- The finite types `X p` and `π`. -/
def finT (P : Set ℕ) : Set (Ty P) := {t | (∃ p hp, t = tX p hp) ∨ t = tPi}

theorem fc_iff {τ υ : Ty P} {i j : ℕ} :
    FC gH dT τ i υ j ↔ gH τ i * gH υ (j + dT τ) = gH υ j * gH τ i := by
  unfold FC
  constructor
  · intro h; rw [← h]; group
  · intro h
    calc (gH τ i)⁻¹ * gH υ j * gH τ i = (gH τ i)⁻¹ * (gH υ j * gH τ i) := by group
      _ = (gH τ i)⁻¹ * (gH τ i * gH υ (j + dT τ)) := by rw [h]
      _ = gH υ (j + dT τ) := by group

theorem dT_X (p : ℕ) (hp : p ∈ P' P) : dT (tX p hp) = p - 1 := rfl

theorem dT_pi : dT (tPi : Ty P) = 0 := rfl

/-- The numerical parameters of an instance (its code without the tag). -/
def Inst.params (x : Inst) : List ℕ :=
  [x.code.2.1, x.code.2.2.1, x.code.2.2.2.1, x.code.2.2.2.2.1, x.code.2.2.2.2.2]

/-- A valid instance whose parameters are at most the largest prime plus 8 holds. -/
theorem inst_small {x : Inst} (hv : x.Valid P) (h : ∀ c ∈ x.params, c ≤ sSup (P' P) + 8) :
    toH P x.lev x.sides.1 = toH P x.lev x.sides.2 := by
  refine inst_holds ?_ hv
  have h0 : x.code.1 < bnd P + 9 := by
    unfold bnd
    cases x <;> simp only [Inst.code] <;> omega
  simp only [Inst.params, List.forall_mem_cons] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h0, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold bnd <;> omega

theorem le_sSup_P' (hB : BddAbove (P' P)) {p : ℕ} (hp : p ∈ P' P) : p ≤ sSup (P' P) + 8 :=
  (le_csSup hB hp).trans (Nat.le_add_right _ _)

/-! ### The far-commutation instances as relations between generators -/

/-- (b) as a relation between generators, target not the tail. -/
theorem fsp_front {n i j p q : ℕ} (hij : i < j) (hj : j + 1 < n) (hp : p ∈ P' P)
    (hq : q ∈ P' P) (hp1 : 1 ≤ p) :
    toH P n [.split i p, .split (j + p - 1) q] = toH P n [.split j q, .split i p] ↔
      FC gH dT (tX p hp) (i + 1) (tX q hq) (j + 1) := by
  rw [toH_two, toH_two, lev_split p (by omega), lev_split q (by omega),
    hatH_split_front (by omega) hp, hatH_split_front (by omega) hq,
    hatH_split_front (by omega) hq, hatH_split_front (by omega) hp, fc_iff, dT_X,
    show j + 1 + (p - 1) = j + p - 1 + 1 by omega]

/-- (b) as a relation between generators, target the tail (split by an odd prime). -/
theorem fsp_tail {n i j p q : ℕ} (hij : i < j) (hj : j + 1 = n) (hp : p ∈ P' P)
    (hq : q ∈ P) (hq2 : q ≠ 2) (hp1 : 1 ≤ p) (hq1 : 1 ≤ q) :
    toH P n [.split i p, .split (j + p - 1) q] = toH P n [.split j q, .split i p] ↔
      FC gH dT (tX p hp) (i + 1) (tY q hq) (j + 1) := by
  rw [toH_two, toH_two, lev_split p (by omega), lev_split q (by omega),
    hatH_split_front (by omega) hp, hatH_split_tail (by omega) hq hq2,
    hatH_split_tail (by omega) hq hq2, hatH_split_front (by omega) hp, fc_iff, dT_X,
    show j + 1 + (p - 1) = j + p - 1 + 1 by omega]

/-- (b) with the binary tail split holds outright. -/
theorem fsp_tail_two {n i j p : ℕ} (hij : i < j) (hj : j + 1 = n) (hp : p ∈ P' P) (hp1 : 1 ≤ p) :
    toH P n [.split i p, .split (j + p - 1) 2] = toH P n [.split j 2, .split i p] := by
  rw [toH_two, toH_two, lev_split p (by omega), lev_split 2 (by omega),
    hatH_split_tail_two (show j + p - 1 + 1 = n + p - 1 by omega), hatH_split_tail_two hj,
    hatH_split_front (by omega) hp, hatH_split_front (by omega) hp, mul_one, one_mul]

/-- (d) for a split before the swapped pair, as a relation between generators. -/
theorem dl_front {n k i p : ℕ} (hik : i < k) (hk : k + 2 < n) (hp : p ∈ P' P) (hp1 : 1 ≤ p) :
    toH P n [.swap k, .split i p] = toH P n [.split i p, .swap (k + p - 1)] ↔
      FC gH dT (tX p hp) (i + 1) tPi (k + 1) := by
  rw [toH_two, toH_two, lev_swap, lev_split p (by omega), hatH_swap_front hk,
    hatH_split_front (by omega) hp, hatH_swap_front (by omega), fc_iff, dT_X,
    show k + 1 + (p - 1) = k + p - 1 + 1 by omega]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem dl_tail {n k i p : ℕ} (hik : i < k) (hk : k + 2 = n) (hp : p ∈ P' P) (hp1 : 1 ≤ p) :
    toH P n [.swap k, .split i p] = toH P n [.split i p, .swap (k + p - 1)] ↔
      FC gH dT (tX p hp) (i + 1) tRho (k + 1) := by
  rw [toH_two, toH_two, lev_swap, lev_split p (by omega), hatH_swap_tail hk,
    hatH_split_front (by omega) hp, hatH_swap_tail (by omega), fc_iff, dT_X,
    show k + 1 + (p - 1) = k + p - 1 + 1 by omega]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- (d) for a split after the swapped pair, as a relation between generators. -/
theorem dr_front {n k i p : ℕ} (hki : k + 1 < i) (hi : i + 1 < n) (hp : p ∈ P' P) (hp1 : 1 ≤ p) :
    toH P n [.swap k, .split i p] = toH P n [.split i p, .swap k] ↔
      FC gH dT tPi (k + 1) (tX p hp) (i + 1) := by
  rw [toH_two, toH_two, lev_swap, lev_split p (by omega), hatH_swap_front (by omega),
    hatH_split_front hi hp, hatH_swap_front (by omega), fc_iff, dT_pi, add_zero]

theorem dr_tail {n k i p : ℕ} (hki : k + 1 < i) (hi : i + 1 = n) (hp : p ∈ P) (hp2 : p ≠ 2)
    (hp1 : 1 ≤ p) :
    toH P n [.swap k, .split i p] = toH P n [.split i p, .swap k] ↔
      FC gH dT tPi (k + 1) (tY p hp) (i + 1) := by
  rw [toH_two, toH_two, lev_swap, lev_split p (by omega), hatH_swap_front (by omega),
    hatH_split_tail hi hp hp2, hatH_swap_front (by omega), fc_iff, dT_pi, add_zero]

theorem dr_tail_two {n k i : ℕ} (hki : k + 1 < i) (hi : i + 1 = n) :
    toH P n [.swap k, .split i 2] = toH P n [.split i 2, .swap k] := by
  rw [toH_two, toH_two, lev_swap, lev_split 2 (by omega), hatH_split_tail_two hi, mul_one,
    one_mul, hatH_swap_front (by omega), hatH_swap_front (by omega)]

/-- (a) for distant swaps, as a relation between generators. -/
theorem fsw_front {n k l : ℕ} (hkl : k + 2 ≤ l) (hl : l + 2 < n) :
    toH P n [.swap k, .swap l] = toH P n [.swap l, .swap k] ↔
      FC (gH (P := P)) dT tPi (k + 1) tPi (l + 1) := by
  rw [toH_two, toH_two, lev_swap, lev_swap, hatH_swap_front (by omega), hatH_swap_front hl,
    fc_iff, dT_pi, add_zero]

theorem fsw_tail {n k l : ℕ} (hkl : k + 2 ≤ l) (hl : l + 2 = n) :
    toH P n [.swap k, .swap l] = toH P n [.swap l, .swap k] ↔
      FC (gH (P := P)) dT tPi (k + 1) tRho (l + 1) := by
  rw [toH_two, toH_two, lev_swap, lev_swap, hatH_swap_front (by omega), hatH_swap_tail hl,
    fc_iff, dT_pi, add_zero]

/-! ### Lemma FC -/

theorem mem_P'_of_mem {q : ℕ} (hq : q ∈ P) : q ∈ P' P := Set.mem_insert_of_mem _ hq

theorem ne_two_of_mem (hP2 : 2 ∉ P) {q : ℕ} (hq : q ∈ P) : q ≠ 2 := fun e => hP2 (e ▸ hq)

theorem wT_pos (τ : Ty P) : 1 ≤ wT τ := by
  rcases τ with _ | _ | b
  · exact le_refl 1
  · exact le_refl 1
  · cases b
    · exact one_le_two
    · exact le_refl 1

section Base

variable (hB : BddAbove (P' P)) (hP2 : 2 ∉ P) (hpos : ∀ p ∈ P' P, 2 ≤ p)
include hB hP2 hpos

/-- The base far-commutation relations, from bounded instances. -/
theorem fc_base : ∀ τ ∈ finT P, ∀ i, (i = 1 ∨ i = 2) → ∀ υ k, k < 2 →
    FC gH dT τ i υ (i + wT τ + k) := by
  intro τ hτ i hi υ k hk
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rcases hτ with ⟨p, hp, rfl⟩ | rfl
  · -- `τ = X p`
    have hp1 := hpos p hp
    have hpS := le_sSup_P' hB hp
    obtain ⟨j, hj⟩ : ∃ j, j = i + 1 + k := ⟨_, rfl⟩
    rw [show i + 1 + wT (tX p hp) + k = j + 1 from by show i + 1 + 1 + k = j + 1; omega]
    rcases υ with ⟨q, hq⟩ | ⟨q, hq⟩ | b
    · have hqS := le_sSup_P' hB hq
      have h := inst_small (P := P) (x := .fsp (j + 2) i j p q)
        (by simp only [Inst.Valid]; exact ⟨by omega, by omega, hp, hq⟩)
        (by intro c hc
            simp only [Inst.params, Inst.code, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl | rfl | rfl | rfl <;> omega)
      exact (fsp_front (n := j + 2) (by omega) (by omega) hp hq (by omega)).1 h
    · have hq' := mem_P'_of_mem hq
      have hqS := le_sSup_P' hB hq'
      have h := inst_small (P := P) (x := .fsp (j + 1) i j p q)
        (by simp only [Inst.Valid]; exact ⟨by omega, by omega, hp, hq'⟩)
        (by intro c hc
            simp only [Inst.params, Inst.code, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl | rfl | rfl | rfl <;> omega)
      exact (fsp_tail (n := j + 1) (by omega) rfl hp hq (ne_two_of_mem hP2 hq) (by omega)
        (by have := hpos q hq'; omega)).1 h
    · cases b
      · have h := inst_small (P := P) (x := .dl (j + 3) j i p)
          (by simp only [Inst.Valid]; exact ⟨by omega, by omega, hp⟩)
          (by intro c hc
            simp only [Inst.params, Inst.code, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl | rfl | rfl | rfl <;> omega)
        exact (dl_front (n := j + 3) (by omega) (by omega) hp (by omega)).1 h
      · have h := inst_small (P := P) (x := .dl (j + 2) j i p)
          (by simp only [Inst.Valid]; exact ⟨by omega, by omega, hp⟩)
          (by intro c hc
            simp only [Inst.params, Inst.code, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl | rfl | rfl | rfl <;> omega)
        exact (dl_tail (n := j + 2) (by omega) rfl hp (by omega)).1 h
  · -- `τ = π`
    obtain ⟨j, hj⟩ : ∃ j, j = i + 2 + k := ⟨_, rfl⟩
    rw [show i + 1 + wT (tPi : Ty P) + k = j + 1 from by show i + 1 + 2 + k = j + 1; omega]
    rcases υ with ⟨q, hq⟩ | ⟨q, hq⟩ | b
    · have hqS := le_sSup_P' hB hq
      have h := inst_small (P := P) (x := .dr (j + 2) i j q)
        (by simp only [Inst.Valid]; exact ⟨by omega, by omega, hq⟩)
        (by intro c hc
            simp only [Inst.params, Inst.code, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl | rfl | rfl | rfl <;> omega)
      exact (dr_front (n := j + 2) (by omega) (by omega) hq (by have := hpos q hq; omega)).1 h
    · have hq' := mem_P'_of_mem hq
      have hqS := le_sSup_P' hB hq'
      have h := inst_small (P := P) (x := .dr (j + 1) i j q)
        (by simp only [Inst.Valid]; exact ⟨by omega, by omega, hq'⟩)
        (by intro c hc
            simp only [Inst.params, Inst.code, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl | rfl | rfl | rfl <;> omega)
      exact (dr_tail (n := j + 1) (by omega) rfl hq (ne_two_of_mem hP2 hq)
        (by have := hpos q hq'; omega)).1 h
    · cases b
      · have h := inst_small (P := P) (x := .fsw (j + 3) i j)
          (by simp only [Inst.Valid]; exact ⟨by omega, by omega⟩)
          (by intro c hc
            simp only [Inst.params, Inst.code, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl | rfl | rfl | rfl <;> omega)
        exact (fsw_front (n := j + 3) (by omega) (by omega)).1 h
      · have h := inst_small (P := P) (x := .fsw (j + 2) i j)
          (by simp only [Inst.Valid]; exact ⟨by omega, by omega⟩)
          (by intro c hc
            simp only [Inst.params, Inst.code, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl | rfl | rfl | rfl <;> omega)
        exact (fsw_tail (n := j + 2) (by omega) rfl).1 h

/-- **Lemma FC** in `H P`: all far-commutation relations. -/
theorem fc_all {τ : Ty P} (hτ : τ ∈ finT P) {i : ℕ} (hi : 1 ≤ i) (υ : Ty P) {j : ℕ}
    (hj : i + wT τ ≤ j) : FC gH dT τ i υ j :=
  fc_of_base (s := sH P) (fun υ _ hj => gH_succ υ hj) (υ₀ := tX 2 (two_mem P))
    (Or.inl ⟨2, two_mem P, rfl⟩) rfl rfl (fun τ _ => wT_pos τ)
    (fc_base hB hP2 hpos) hτ hi hj

end Base

end GroupApproximation.ClassTransposition.Presentation
