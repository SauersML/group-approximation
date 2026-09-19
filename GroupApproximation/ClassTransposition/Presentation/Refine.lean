import GroupApproximation.ClassTransposition.Presentation.KU

/-!
# Refining to a uniform partition

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, Fact O
steps O1–O2).

The moduli of a realization from `[ℤ]` are products of primes of `P ∪ {2}` (`isPN_real`). If every
box of a list divides `M` with such a ratio, a split word refines every box to modulus `M`
(`refine_to`). Two ordered partitions of modulus `M` list the same boxes (`perm_of_unif`).
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

variable {P : Set ℕ}

/-- `m` is a product of primes of `P ∪ {2}`. -/
def IsPN (P : Set ℕ) (m : ℤ) : Prop := ∃ l : List ℕ, (∀ q ∈ l, q ∈ P' P) ∧ m = ((l.prod : ℕ) : ℤ)

theorem isPN_one : IsPN P 1 := ⟨[], by simp, by simp⟩

theorem IsPN.mul {a b : ℤ} (ha : IsPN P a) (hb : IsPN P b) : IsPN P (a * b) := by
  obtain ⟨l1, h1, rfl⟩ := ha
  obtain ⟨l2, h2, rfl⟩ := hb
  refine ⟨l1 ++ l2, fun q hq => ?_, by rw [List.prod_append, Nat.cast_mul]⟩
  rcases List.mem_append.1 hq with hq | hq
  exacts [h1 q hq, h2 q hq]

theorem isPN_prod : ∀ l : List ℤ, (∀ x ∈ l, IsPN P x) → IsPN P l.prod
  | [], _ => isPN_one
  | x :: l, h => by
    rw [List.prod_cons]
    exact (h x List.mem_cons_self).mul (isPN_prod l fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem mem_splitAt : ∀ (b : List Box) (i p : ℕ) (X : Box), X ∈ splitAt b i p →
    X ∈ b ∨ ∃ E ∈ b, X ∈ kids E p
  | [], _, _, X, h => by simp [splitAt] at h
  | E :: b, 0, p, X, h => by
    rcases List.mem_append.1 h with h | h
    · exact Or.inr ⟨E, List.mem_cons_self, h⟩
    · exact Or.inl (List.mem_cons_of_mem _ h)
  | E :: b, i + 1, p, X, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl List.mem_cons_self
    · rcases mem_splitAt b i p X h with h | ⟨E', hE', h⟩
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr ⟨E', List.mem_cons_of_mem _ hE', h⟩

theorem isPN_real : ∀ (w : List Move) (b : List Box), PrimesIn P w → (∀ F ∈ b, IsPN P F.m) →
    ∀ F ∈ real b w, IsPN P F.m
  | [], _, _, h => h
  | .split i p :: w, b, ⟨hp, hw⟩, h => isPN_real w (splitAt b i p) hw fun X hX => by
      rcases mem_splitAt b i p X hX with hX | ⟨E, hE, hX⟩
      · exact h X hX
      · rw [kids_m hX]
        exact (show IsPN P (p : ℤ) from ⟨[p], by simpa using hp, by simp⟩).mul (h E hE)
  | .swap k :: w, b, hw, h => isPN_real w (swapAt b k) hw fun X hX =>
      h X ((swapAt_perm b k).mem_iff.1 hX)

theorem comb_one : comb 1 = [univ] := rfl

/-- Every box of the realization of a valid word from `[ℤ]` has a smooth modulus. -/
theorem isPN_real_one (hpos : ∀ p ∈ P' P, 2 ≤ p) {w : List Move} (hw : ValW P 1 w) :
    ∀ F ∈ real (comb 1) w, IsPN P F.m :=
  isPN_real w (comb 1) (locB_of_valW hpos 1 w hw).2 fun F hF => by
    rw [comb_one, List.mem_singleton] at hF
    rw [hF]
    exact isPN_one

/-- The product of the moduli of `b` is a smooth multiple of each of them. -/
theorem ratio_prod {b : List Box} (h : ∀ F ∈ b, IsPN P F.m) (F : Box) (hF : F ∈ b) :
    ∃ l : List ℕ, (∀ q ∈ l, q ∈ P' P) ∧ (b.map (·.m)).prod = F.m * ((l.prod : ℕ) : ℤ) := by
  have hm : F.m ∈ b.map (·.m) := List.mem_map.2 ⟨F, hF, rfl⟩
  obtain ⟨l, hl, he⟩ := isPN_prod ((b.map (·.m)).erase F.m) fun x hx => by
    obtain ⟨G, hG, rfl⟩ := List.mem_map.1 (List.mem_of_mem_erase hx)
    exact h G hG
  exact ⟨l, hl, by rw [← List.prod_erase hm, he]⟩

/-! ### The refinement -/

/-- `F` refines to modulus `M` by at most `n` primes of `P ∪ {2}`. -/
def RefTo (P : Set ℕ) (M : ℤ) (n : ℕ) (F : Box) : Prop :=
  ∃ l : List ℕ, (∀ q ∈ l, q ∈ P' P) ∧ l.length ≤ n ∧ M = F.m * ((l.prod : ℕ) : ℤ)

theorem exists_bound {M : ℤ} : ∀ b : List Box,
    (∀ F ∈ b, ∃ l : List ℕ, (∀ q ∈ l, q ∈ P' P) ∧ M = F.m * ((l.prod : ℕ) : ℤ)) →
    ∃ n, ∀ F ∈ b, RefTo P M n F
  | [], _ => ⟨0, fun F hF => absurd hF List.not_mem_nil⟩
  | F :: b, h => by
    obtain ⟨n, hn⟩ := exists_bound b fun G hG => h G (List.mem_cons_of_mem _ hG)
    obtain ⟨l, hl, hM⟩ := h F List.mem_cons_self
    refine ⟨max n l.length, fun G hG => ?_⟩
    rcases List.mem_cons.1 hG with rfl | hG
    · exact ⟨l, hl, le_max_right _ _, hM⟩
    · obtain ⟨l', hl', hle, hM'⟩ := hn G hG
      exact ⟨l', hl', le_trans hle (le_max_left _ _), hM'⟩

theorem real_map_up (F : Box) : ∀ (c : List Move) (b : List Box),
    real (F :: b) (c.map Move.up) = F :: real b c
  | [], _ => rfl
  | .split i p :: c, b => real_map_up F c (splitAt b i p)
  | .swap k :: c, b => real_map_up F c (swapAt b k)

theorem valW_map_up : ∀ (c : List Move) (n : ℕ), ValW P n c → ValW P (n + 1) (c.map Move.up)
  | [], _, _ => trivial
  | .split i p :: c, n, ⟨⟨h1, hp⟩, hc⟩ => by
    refine ⟨⟨show i + 1 < n + 1 by omega, hp⟩, ?_⟩
    show ValW P ((Move.split i p).up.lev (n + 1)) (c.map Move.up)
    rw [lev_up]
    exact valW_map_up c _ hc
  | .swap k :: c, n, ⟨h1, hc⟩ => by
    refine ⟨show k + 1 + 1 < n + 1 by omega, ?_⟩
    show ValW P ((Move.swap k).up.lev (n + 1)) (c.map Move.up)
    rw [lev_up]
    exact valW_map_up c _ hc

/-- **Refinement.** A split word refines every box to modulus `M`. -/
theorem refine_to {M : ℤ} (n : ℕ) : ∀ (b : List Box), (∀ F ∈ b, RefTo P M n F) →
    ∃ c : List Move, ValW P b.length c ∧ ∀ G ∈ real b c, G.m = M := by
  induction n with
  | zero =>
    intro b h
    refine ⟨[], trivial, fun G hG => ?_⟩
    obtain ⟨l, -, hl, hM⟩ := h G hG
    rw [List.length_eq_zero_iff.1 (show l.length = 0 by omega)] at hM
    simpa using hM.symm
  | succ n ih =>
    intro b
    induction b with
    | nil => intro _; exact ⟨[], trivial, fun G hG => absurd hG List.not_mem_nil⟩
    | cons F b ihb =>
      intro h
      obtain ⟨c, hc, hcM⟩ := ihb fun G hG => h G (List.mem_cons_of_mem _ hG)
      obtain ⟨l, hlP, hln, hM⟩ := h F List.mem_cons_self
      rcases l with _ | ⟨q, l⟩
      · refine ⟨c.map Move.up, valW_map_up c _ hc, fun G hG => ?_⟩
        rw [real_map_up] at hG
        rcases List.mem_cons.1 hG with rfl | hG
        · simpa using hM.symm
        · exact hcM G hG
      · have hq := hlP q List.mem_cons_self
        obtain ⟨c', hc', hc'M⟩ := ih (kids F q ++ real b c) fun G hG => by
          rcases List.mem_append.1 hG with hG | hG
          · refine ⟨l, fun x hx => hlP x (List.mem_cons_of_mem _ hx), by simpa using hln, ?_⟩
            rw [kids_m hG, hM, List.prod_cons, Nat.cast_mul]
            ring
          · exact ⟨[], by simp, Nat.zero_le _, by rw [hcM G hG]; simp⟩
        refine ⟨c.map Move.up ++ .split 0 q :: c', ?_, fun G hG => hc'M G ?_⟩
        · refine (valW_append P _ _ _).2 ⟨valW_map_up c _ hc, ?_⟩
          rw [List.length_cons, levW_up]
          refine ⟨⟨by omega, hq⟩, ?_⟩
          have e : (kids F q ++ real b c).length = levW b.length c + 1 + q - 1 := by
            rw [List.length_append, length_kids, length_real]; omega
          rw [lev_split (i := 0) (n := levW b.length c + 1) q (by omega), ← e]
          exact hc'
        · rw [real_append, real_map_up] at hG
          exact hG

/-! ### Uniform partitions -/

theorem mem_of_unif {l : List Box} {M : ℤ} (hl : IsPart l) (hM : ∀ G ∈ l, G.m = M) (G : Box) :
    G ∈ l ↔ G.m = M := by
  refine ⟨hM G, fun hG => ?_⟩
  obtain ⟨G', hG', hmem⟩ := hl.2 G.r
  have e1 : G'.m = G.m := (hM G' hG').trans hG.symm
  have e2 : G'.r = G.r := by
    have h : G.r % G'.m = G'.r := hmem
    rw [e1, Int.emod_eq_of_lt G.hr G.hrm] at h
    exact h.symm
  have e3 : G' = G := Box.ext e2 e1
  rwa [← e3]

/-- Two ordered partitions of modulus `M` list the same boxes. -/
theorem perm_of_unif {l l' : List Box} {M : ℤ} (hl : IsPart l) (hl' : IsPart l')
    (hM : ∀ G ∈ l, G.m = M) (hM' : ∀ G ∈ l', G.m = M) : l.Perm l' :=
  (List.perm_ext_iff_of_nodup (nodup_of_disj hl.1) (nodup_of_disj hl'.1)).2 fun G => by
    rw [mem_of_unif hl hM, mem_of_unif hl' hM']

end GroupApproximation.ClassTransposition.Presentation
