import GroupApproximation.ClassTransposition.Presentation.Eval
import GroupApproximation.ClassTransposition.Presentation.ListCrt

/-!
# The evaluation `H P →* Perm ℤ`

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, §1, §3).

Every valid instance of the families (a)–(d) has two valid sides with the same realization on the
comb (`inst_real`). So its relator evaluates to `1` (`lift_rel`), and the generators define a
homomorphism `evalH : H P →* Perm ℤ` with `evalH (toH P n w) = frac (comb _) (real (comb n) w)` for
valid words (`evalH_toH`).
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

variable {P : Set ℕ}

theorem exists_decomp {α : Type*} (b : List α) {i : ℕ} (h : i < b.length) :
    ∃ l E l', b = l ++ E :: l' ∧ l.length = i :=
  ⟨b.take i, b[i], b.drop (i + 1), by rw [← List.drop_eq_getElem_cons h, List.take_append_drop],
    by rw [List.length_take]; omega⟩

theorem valW_append (P : Set ℕ) : ∀ (n : ℕ) (u v : List Move),
    ValW P n (u ++ v) ↔ ValW P n u ∧ ValW P (levW n u) v
  | n, [], v => by simp [ValW]
  | n, m :: u, v => by
    rw [List.cons_append]
    show m.Val P n ∧ ValW P (m.lev n) (u ++ v) ↔ (m.Val P n ∧ ValW P (m.lev n) u) ∧ _
    rw [valW_append P (m.lev n) u v, levW_cons, and_assoc]

theorem valW_swaps (k L : ℕ) : ∀ w : List ℕ, (∀ t ∈ w, k + t + 1 < L) → ValW P L (swaps k w)
  | [], _ => trivial
  | t :: w, h => ⟨h t List.mem_cons_self, valW_swaps k L w fun t' ht' =>
      h t' (List.mem_cons_of_mem _ ht')⟩

theorem valW_layer {q : ℕ} (hq : q ∈ P' P) (hq1 : 1 ≤ q) : ∀ (p i L : ℕ), i + p ≤ L →
    ValW P L (layer i p q)
  | 0, _, _, _ => trivial
  | p + 1, i, L, h => by
    rw [layer_succ]
    refine ⟨⟨show i < L by omega, hq⟩, ?_⟩
    rw [lev_split q (by omega)]
    exact valW_layer hq hq1 p (i + q) (L + q - 1) (by omega)

theorem exists_decomp2 {α : Type*} (b : List α) {k : ℕ} (h : k + 1 < b.length) :
    ∃ l E F l', b = l ++ E :: F :: l' ∧ l.length = k := by
  obtain ⟨l, E, l', hb, hl⟩ := exists_decomp b (show k < b.length by omega)
  cases l' with
  | nil => subst hb; simp at h; omega
  | cons F l' => exact ⟨l, E, F, l', hb, hl⟩

section Rel

variable (hpos : ∀ p ∈ P' P, 2 ≤ p) (hP2 : 2 ∉ P)
include hpos hP2

theorem lift_eq_of_real {n : ℕ} {u v : List Move} (hn : 0 < n) (hu : ValW P n u)
    (hv : ValW P n v) (h : real (comb n) u = real (comb n) v) :
    FreeGroup.lift (evGen (P := P)) (toFree P n u) = FreeGroup.lift evGen (toFree P n v) := by
  have e : levW n u = levW n v := by
    have := congrArg List.length h
    rwa [length_real, length_real, length_comb] at this
  rw [lift_toFree hpos hP2 n u hn hu, lift_toFree hpos hP2 n v hn hv, h, e]

/-- Every valid relator evaluates to `1`. -/
theorem lift_rel {x : Inst} (hv : x.Valid P) : FreeGroup.lift (evGen (P := P)) (x.rel P) = 1 := by
  rw [Inst.rel, map_mul, map_inv, mul_inv_eq_one]
  cases x with
  | sq n k =>
    have hv : k + 2 ≤ n := hv
    refine lift_eq_of_real hpos hP2 (by omega) ⟨show k + 1 < n by omega, show k + 1 < n by omega,
      trivial⟩ trivial ?_
    show swapAt (swapAt (comb n) k) k = comb n
    exact swapAt_swapAt _ _
  | br n k =>
    have hv : k + 3 ≤ n := hv
    refine lift_eq_of_real hpos hP2 (by omega) ⟨show k + 1 < n by omega, show k + 1 + 1 < n by omega,
      show k + 1 < n by omega, trivial⟩ ⟨show k + 1 + 1 < n by omega, show k + 1 < n by omega,
      show k + 1 + 1 < n by omega, trivial⟩ ?_
    show swapAt (swapAt (swapAt (comb n) k) (k + 1)) k =
      swapAt (swapAt (swapAt (comb n) (k + 1)) k) (k + 1)
    exact swapAt_braid _ _ (by rw [length_comb]; omega)
  | fsw n k l =>
    obtain ⟨h1, h2⟩ : k + 2 ≤ l ∧ l + 2 ≤ n := hv
    refine lift_eq_of_real hpos hP2 (by omega) ⟨show k + 1 < n by omega, show l + 1 < n by omega,
      trivial⟩ ⟨show l + 1 < n by omega, show k + 1 < n by omega, trivial⟩ ?_
    show swapAt (swapAt (comb n) k) l = swapAt (swapAt (comb n) l) k
    exact swapAt_far _ _ _ h1
  | fsp n i j p q =>
    obtain ⟨h1, h2, hp, hq⟩ : i < j ∧ j < n ∧ p ∈ P' P ∧ q ∈ P' P := hv
    have hp1 := hpos p hp
    have hq1 := hpos q hq
    refine lift_eq_of_real hpos hP2 (by omega) ⟨⟨by omega, hp⟩, ?_⟩ ⟨⟨by omega, hq⟩, ?_⟩ ?_
    · rw [lev_split p (by omega)]; exact ⟨⟨by omega, hq⟩, trivial⟩
    · rw [lev_split q (by omega)]; exact ⟨⟨by omega, hp⟩, trivial⟩
    · show splitAt (splitAt (comb n) i p) (j + p - 1) q = splitAt (splitAt (comb n) j q) i p
      exact splitAt_splitAt_far p _ i j q h1
  | dl n k i p =>
    obtain ⟨h1, h2, hp⟩ : i < k ∧ k + 2 ≤ n ∧ p ∈ P' P := hv
    have hp1 := hpos p hp
    refine lift_eq_of_real hpos hP2 (by omega)
      ⟨show k + 1 < n by omega, ⟨show i < n by omega, hp⟩, trivial⟩
      ⟨⟨by omega, hp⟩, ?_⟩ ?_
    · rw [lev_split p (by omega)]; exact ⟨show k + p - 1 + 1 < n + p - 1 by omega, trivial⟩
    · show splitAt (swapAt (comb n) k) i p = swapAt (splitAt (comb n) i p) (k + p - 1)
      exact splitAt_swapAt_left p _ k i h1
  | dr n k i p =>
    obtain ⟨h1, h2, hp⟩ : k + 1 < i ∧ i < n ∧ p ∈ P' P := hv
    have hp1 := hpos p hp
    refine lift_eq_of_real hpos hP2 (by omega)
      ⟨show k + 1 < n by omega, ⟨show i < n by omega, hp⟩, trivial⟩
      ⟨⟨by omega, hp⟩, ?_⟩ ?_
    · rw [lev_split p (by omega)]; exact ⟨show k + 1 < n + p - 1 by omega, trivial⟩
    · show splitAt (swapAt (comb n) k) i p = swapAt (splitAt (comb n) i p) k
      exact splitAt_swapAt_right p _ k i h1
  | dk n k p =>
    obtain ⟨h1, hp⟩ : k + 2 ≤ n ∧ p ∈ P' P := hv
    have hp1 := hpos p hp
    refine lift_eq_of_real hpos hP2 (by omega)
      ⟨show k + 1 < n by omega, ⟨show k < n by omega, hp⟩, trivial⟩
      ⟨⟨by omega, hp⟩, ?_⟩ ?_
    · rw [lev_split p (by omega)]
      exact valW_swaps k _ _ fun t ht => by rw [List.mem_range] at ht; omega
    · obtain ⟨l, E, F, l', hb, hl⟩ := exists_decomp2 (comb n) (k := k) (by rw [length_comb]; omega)
      show splitAt (swapAt (comb n) k) k p = real (splitAt (comb n) (k + 1) p) (swaps k (List.range p))
      rw [hb, ← hl]
      exact splitAt_swapAt_self l l' E F p
  | dk1 n k p =>
    obtain ⟨h1, hp⟩ : k + 2 ≤ n ∧ p ∈ P' P := hv
    have hp1 := hpos p hp
    refine lift_eq_of_real hpos hP2 (by omega)
      ⟨show k + 1 < n by omega, ⟨show k + 1 < n by omega, hp⟩, trivial⟩
      ⟨⟨by omega, hp⟩, ?_⟩ ?_
    · rw [lev_split p (by omega)]
      exact valW_swaps k _ _ fun t ht => by rw [List.mem_reverse, List.mem_range] at ht; omega
    · obtain ⟨l, E, F, l', hb, hl⟩ := exists_decomp2 (comb n) (k := k) (by rw [length_comb]; omega)
      show splitAt (swapAt (comb n) k) (k + 1) p =
        real (splitAt (comb n) k p) (swaps k (List.range p).reverse)
      rw [hb, ← hl]
      exact splitAt_swapAt_succ l l' E F p
  | cx n i p q =>
    obtain ⟨h1, hp, hq, -⟩ : i < n ∧ p ∈ P' P ∧ q ∈ P' P ∧ p ≠ q := hv
    have hp1 := hpos p hp
    have hq1 := hpos q hq
    refine lift_eq_of_real hpos hP2 (by omega) ⟨⟨h1, hp⟩, ?_⟩
      ((valW_append P n _ _).2 ⟨⟨⟨h1, hq⟩, ?_⟩, ?_⟩) ?_
    · rw [lev_split p h1]; exact valW_layer hq (by omega) p i _ (by omega)
    · rw [lev_split q h1]; exact valW_layer hp (by omega) q i _ (by omega)
    · rw [levW_cons, lev_split q h1, levW_layer (by omega : 1 ≤ p) q i _ (by omega)]
      refine valW_swaps i _ _ fun t ht => ?_
      have h3 := (crt_spec (by omega : 0 < p) (by omega : 0 < q)).1 t ht
      have h4 := mul_pred_add (q := q) (show 1 ≤ p by omega)
      generalize p * q = M at h3 h4 ⊢
      generalize q * (p - 1) = R at h3 h4 ⊢
      omega
    · obtain ⟨l, E, l', hb, hl⟩ := exists_decomp (comb n) (i := i) (by rw [length_comb]; exact h1)
      rw [hb, ← hl]
      exact real_cx (by omega) (by omega) E l l'

end Rel

/-- The evaluation of `H P` in the permutations of `ℤ`. -/
noncomputable def evalH (hpos : ∀ p ∈ P' P, 2 ≤ p) (hP2 : 2 ∉ P) : H P →* Perm ℤ :=
  PresentedGroup.toGroup (f := evGen) fun r hr => by
    obtain ⟨x, -, hv, rfl⟩ := hr
    exact lift_rel hpos hP2 hv

theorem evalH_mk (hpos : ∀ p ∈ P' P, 2 ≤ p) (hP2 : 2 ∉ P) (x : FreeGroup (Gen P)) :
    evalH hpos hP2 (PresentedGroup.mk _ x) = FreeGroup.lift evGen x := rfl

theorem evalH_toH (hpos : ∀ p ∈ P' P, 2 ≤ p) (hP2 : 2 ∉ P) {n : ℕ} {w : List Move} (hn : 0 < n)
    (hw : ValW P n w) : evalH hpos hP2 (toH P n w) = frac (comb (levW n w)) (real (comb n) w) :=
  lift_toFree hpos hP2 n w hn hw

end GroupApproximation.ClassTransposition.Presentation
