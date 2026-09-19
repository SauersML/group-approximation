import GroupApproximation.Leavitt.LeavittSimplicity
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Field.ZMod

/-!
# The centre of the universal binary Leavitt algebra

Proposition `prop:simple` of the manuscript quotes two facts about
`R = L_{𝔽₂}(1,2)` from the literature:

* purely infinite simplicity (Abrams--Aranda Pino), used in the form
  "every nonzero `x` admits `a`, `b` with `a x b = 1`"; and
* "the centre of `R` is the base field" (Aranda Pino--Crow,
  Corollary 4.3), used only to conclude `Z(R)^× = 𝔽₂^× = {1}`.

The first is already proved in `LeavittSimplicity.lean`
(`BinaryLeavitt.exists_mul_mul_eq_one`).  This file proves the second, for
every field `k`, from the monomial normal form and nothing else:

  `Subalgebra.center k (L_k(1,2)) = ⊥`   (`BinaryLeavitt.center_eq_bot`).

## The argument

Fix a central `z` and write it, using
`BinaryLeavitt.exists_monomial_representation`, as a finite `k`-combination
of monomials `s_α t_β`.  Let `r` bound every `|α|` and every `|β|`, and let
`W = 0^r 1` be the kill word already used by the simplicity proof.  Since
`t_W s_W = 1` and `z` is central,

  `t_W z s_W = z t_W s_W = z`,

so `z` is unchanged by the sandwich.  On the other hand the sandwich
annihilates every monomial except the diagonal runs of zeros: for
`|α|, |β| ≤ r`,

  `t_W (s_α t_β) s_W = 1`  if `α = β = 0^a`, and `0` otherwise

(`BinaryLeavitt.killWord_sandwich_monomial`, proved here only in the weaker
"`0` or `1`" form, which is all that is needed).  Indeed `t_W s_α = 0`
unless `α` is a prefix of `W`, which for `|α| ≤ r` forces `α = 0^a`; the
remaining product is `t_{β 0^{r-a} 1} s_{0^r 1}`, and two words `0^m 1`,
`0^n 1` are incomparable as soon as `m ≠ n`.  So `z` is a `k`-multiple of
`1`.

No basis theorem, no grading and no gauge action are used, so the argument
runs over an arbitrary field -- in particular over `𝔽₂`, where the units of
the centre are then trivial (`BinaryLeavitt.central_units_trivial`), which
is exactly the input Proposition `prop:simple` takes from
Aranda Pino--Crow.
-/

namespace GroupApproximation

namespace BinaryLeavitt

/-! ### Prefix combinatorics of the kill words `0^r 1` -/

theorem killWord_zero : killWord 0 = [1] := by
  unfold killWord
  rw [List.replicate_zero, List.nil_append]

theorem killWord_succ (r : ℕ) : killWord (r + 1) = 0 :: killWord r := by
  unfold killWord
  rw [List.replicate_succ, List.cons_append]

/-- Splitting off a zero prefix of `0^r 1`. -/
theorem killWord_eq_replicate_append (a r : ℕ) (h : a ≤ r) :
    killWord r = List.replicate a 0 ++ killWord (r - a) := by
  unfold killWord
  rw [← List.append_assoc, ← List.replicate_add,
    show a + (r - a) = r from by omega]

/-- Prefixing zeros lengthens the kill word. -/
theorem replicate_append_killWord (b m : ℕ) :
    List.replicate b (0 : Fin 2) ++ killWord m = killWord (b + m) := by
  unfold killWord
  rw [← List.append_assoc, ← List.replicate_add]

/-- A word of length at most `r` which is a prefix of `0^r 1` is a run of
zeros: the `1` sits beyond position `r`. -/
theorem eq_replicate_of_prefix_killWord :
    ∀ (α : List (Fin 2)) (r : ℕ), α <+: killWord r → α.length ≤ r →
      α = List.replicate α.length 0 := by
  intro α
  induction α with
  | nil =>
      intro _ _ _
      simp
  | cons i α ih =>
      intro r hpre hlen
      cases r with
      | zero =>
          rw [List.length_cons] at hlen
          omega
      | succ r =>
          rw [killWord_succ] at hpre
          obtain ⟨u, hu⟩ := hpre
          rw [List.cons_append] at hu
          injection hu with hi htail
          rw [List.length_cons] at hlen
          have hα := ih r ⟨u, htail⟩ (by omega)
          rw [hi, List.length_cons, List.replicate_succ]
          exact congrArg (List.cons 0) hα

/-- Two kill words of different lengths are incomparable: they disagree at
the position of the earlier `1`. -/
theorem killWord_not_prefix_killWord :
    ∀ (m n : ℕ), m ≠ n → ¬ killWord m <+: killWord n := by
  intro m
  induction m with
  | zero =>
      intro n hne hpre
      cases n with
      | zero => exact hne rfl
      | succ n =>
          rw [killWord_zero, killWord_succ] at hpre
          obtain ⟨u, hu⟩ := hpre
          rw [List.cons_append] at hu
          injection hu with h1 _h2
          exact absurd h1 (by decide)
  | succ m ih =>
      intro n hne hpre
      cases n with
      | zero =>
          rw [killWord_zero, killWord_succ] at hpre
          obtain ⟨u, hu⟩ := hpre
          rw [List.cons_append] at hu
          injection hu with h1 _h2
          exact absurd h1 (by decide)
      | succ n =>
          rw [killWord_succ, killWord_succ] at hpre
          obtain ⟨u, hu⟩ := hpre
          rw [List.cons_append] at hu
          injection hu with _h1 h2
          exact ih n (by omega) ⟨u, h2⟩

/-! ### The sandwich which isolates the scalar part -/

/-- Every monomial divides the identity from both sides, explicitly:
`t_α (s_α t_β) s_β = 1`.  This is the free half of purely infinite
simplicity; the general statement is
`BinaryLeavitt.exists_mul_mul_eq_one`. -/
theorem wordS_wordT_unit_sandwich {A : Type*} [Ring A] (L : LeavittFamily A)
    (α β : List (Fin 2)) :
    L.wordT α * (L.wordS α * L.wordT β) * L.wordS β = 1 := by
  calc
    L.wordT α * (L.wordS α * L.wordT β) * L.wordS β
        = (L.wordT α * L.wordS α) * (L.wordT β * L.wordS β) := by
          simp only [mul_assoc]
    _ = 1 := by
          rw [L.wordT_mul_wordS_self, L.wordT_mul_wordS_self, one_mul]

/-- **The kill-word sandwich is a scalar on monomials.**  For `|α|, |β| ≤ r`
the element `t_W (s_α t_β) s_W`, with `W = 0^r 1`, is `1` when
`α = β = 0^a` and `0` in every other case.  Only the dichotomy is recorded,
which is what the centre computation consumes. -/
theorem killWord_sandwich_monomial {A : Type*} [Ring A] (L : LeavittFamily A)
    (r : ℕ) (α β : List (Fin 2)) (hα : α.length ≤ r) (hβ : β.length ≤ r) :
    L.wordT (killWord r) * (L.wordS α * L.wordT β) * L.wordS (killWord r) = 0 ∨
      L.wordT (killWord r) * (L.wordS α * L.wordT β) *
        L.wordS (killWord r) = 1 := by
  by_cases hαW : α <+: killWord r
  · -- `α` is a prefix of `W`, hence a run of zeros
    have hαrep : α = List.replicate α.length 0 :=
      eq_replicate_of_prefix_killWord α r hαW hα
    have hWsplit : killWord r = α ++ killWord (r - α.length) := by
      rw [killWord_eq_replicate_append α.length r hα, ← hαrep]
    have hcollapse :
        L.wordT (killWord r) * L.wordS α =
          L.wordT (killWord (r - α.length)) := by
      rw [hWsplit]
      exact L.wordT_append_mul_wordS α (killWord (r - α.length))
    have hmain :
        L.wordT (killWord r) * (L.wordS α * L.wordT β) *
            L.wordS (killWord r) =
          L.wordT (β ++ killWord (r - α.length)) * L.wordS (killWord r) := by
      calc
        L.wordT (killWord r) * (L.wordS α * L.wordT β) *
            L.wordS (killWord r)
            = (L.wordT (killWord r) * L.wordS α) * L.wordT β *
                L.wordS (killWord r) := by
              simp only [mul_assoc]
        _ = (L.wordT (killWord (r - α.length)) * L.wordT β) *
              L.wordS (killWord r) := by
              rw [hcollapse]
        _ = L.wordT (β ++ killWord (r - α.length)) *
              L.wordS (killWord r) := by
              rw [L.wordT_append]
    by_cases hβrep : β = List.replicate β.length 0
    · -- `β` is a run of zeros: the two kill words survive or cancel by length
      have hβW : β ++ killWord (r - α.length) =
          killWord (β.length + (r - α.length)) := by
        rw [hβrep, List.length_replicate]
        exact replicate_append_killWord β.length (r - α.length)
      rw [hmain, hβW]
      by_cases hcase : β.length = α.length
      · right
        rw [show β.length + (r - α.length) = r from by omega]
        exact L.wordT_mul_wordS_self (killWord r)
      · left
        have hne : β.length + (r - α.length) ≠ r := by omega
        exact L.wordT_mul_wordS_of_incomparable _ _
          (killWord_not_prefix_killWord _ _ hne)
          (killWord_not_prefix_killWord _ _ (Ne.symm hne))
    · -- `β` carries a `1` at a position where `W` carries a `0`
      left
      rw [hmain]
      have hβnotpre : ¬ β <+: killWord r := fun hpre ↦
        hβrep (eq_replicate_of_prefix_killWord β r hpre hβ)
      refine L.wordT_mul_wordS_of_incomparable _ _ ?_ ?_
      · intro hcon
        exact hβnotpre
          ((List.prefix_append β (killWord (r - α.length))).trans hcon)
      · intro hcon
        obtain ⟨t, ht⟩ := hcon
        have hβpre : β <+: killWord r ++ t := by
          rw [ht]
          exact List.prefix_append β (killWord (r - α.length))
        have hlenle : β.length ≤ (killWord r).length := by
          rw [killWord_length]
          omega
        exact hβnotpre ((List.isPrefix_append_of_length hlenle).mp hβpre)
  · -- `α` is incomparable with `W`, so the sandwich already dies on the left
    left
    have hWα : ¬ killWord r <+: α := by
      intro hcon
      have hlenle := hcon.length_le
      rw [killWord_length] at hlenle
      omega
    have h0 : L.wordT (killWord r) * L.wordS α = 0 :=
      L.wordT_mul_wordS_of_incomparable (killWord r) α hWα hαW
    calc
      L.wordT (killWord r) * (L.wordS α * L.wordT β) * L.wordS (killWord r)
          = (L.wordT (killWord r) * L.wordS α) *
              (L.wordT β * L.wordS (killWord r)) := by
            simp only [mul_assoc]
      _ = 0 := by rw [h0, zero_mul]

/-! ### The centre -/

/-- **Every central element of `L_k(1,2)` is a scalar** (Aranda Pino--Crow,
Corollary 4.3, proved here from the monomial normal form). -/
theorem eq_smul_one_of_central (k : Type) [Field k]
    {z : BinaryLeavittAlgebra k}
    (hz : ∀ y : BinaryLeavittAlgebra k, z * y = y * z) :
    ∃ c : k, z = c • 1 := by
  obtain ⟨n, co, al, be, hrep⟩ := exists_monomial_representation k z
  set L := family k
  obtain ⟨r, hal, hbe⟩ : ∃ r : ℕ,
      (∀ i : Fin n, (al i).length ≤ r) ∧ (∀ i : Fin n, (be i).length ≤ r) := by
    refine ⟨Finset.univ.sup (fun i : Fin n ↦ max (al i).length (be i).length),
      fun i ↦ ?_, fun i ↦ ?_⟩
    · calc
        (al i).length ≤ max (al i).length (be i).length := le_max_left _ _
        _ ≤ Finset.univ.sup
            (fun i : Fin n ↦ max (al i).length (be i).length) :=
          Finset.le_sup (f := fun i : Fin n ↦
            max (al i).length (be i).length) (Finset.mem_univ i)
    · calc
        (be i).length ≤ max (al i).length (be i).length := le_max_right _ _
        _ ≤ Finset.univ.sup
            (fun i : Fin n ↦ max (al i).length (be i).length) :=
          Finset.le_sup (f := fun i : Fin n ↦
            max (al i).length (be i).length) (Finset.mem_univ i)
  -- centrality makes the kill-word sandwich fix `z`
  have hfix :
      L.wordT (killWord r) * z * L.wordS (killWord r) = z := by
    calc
      L.wordT (killWord r) * z * L.wordS (killWord r)
          = L.wordT (killWord r) * (z * L.wordS (killWord r)) :=
            mul_assoc _ _ _
      _ = L.wordT (killWord r) * (L.wordS (killWord r) * z) := by
            rw [hz]
      _ = L.wordT (killWord r) * L.wordS (killWord r) * z :=
            (mul_assoc _ _ _).symm
      _ = z := by rw [L.wordT_mul_wordS_self, one_mul]
  -- and distributes over the monomial representation
  have hexp :
      L.wordT (killWord r) * z * L.wordS (killWord r) =
        ∑ i : Fin n, co i • (L.wordT (killWord r) *
          (L.wordS (al i) * L.wordT (be i)) * L.wordS (killWord r)) := by
    rw [hrep, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_smul_comm, smul_mul_assoc]
  -- every sandwiched monomial is a scalar
  have hd : ∀ i : Fin n, ∃ d : k,
      L.wordT (killWord r) * (L.wordS (al i) * L.wordT (be i)) *
        L.wordS (killWord r) = d • (1 : BinaryLeavittAlgebra k) := by
    intro i
    rcases killWord_sandwich_monomial L r (al i) (be i) (hal i) (hbe i) with
      h | h
    · refine ⟨0, ?_⟩
      rw [zero_smul]
      exact h
    · refine ⟨1, ?_⟩
      rw [one_smul]
      exact h
  choose d hdspec using hd
  refine ⟨∑ i : Fin n, co i * d i, ?_⟩
  calc
    z = L.wordT (killWord r) * z * L.wordS (killWord r) := hfix.symm
    _ = ∑ i : Fin n, co i • (L.wordT (killWord r) *
          (L.wordS (al i) * L.wordT (be i)) * L.wordS (killWord r)) := hexp
    _ = ∑ i : Fin n, (co i * d i) • (1 : BinaryLeavittAlgebra k) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hdspec i, smul_smul]
    _ = (∑ i : Fin n, co i * d i) • (1 : BinaryLeavittAlgebra k) := by
          rw [Finset.sum_smul]

/-- **The centre of `L_k(1,2)` is the base field** (Aranda Pino--Crow,
Corollary 4.3). -/
theorem center_eq_bot (k : Type) [Field k] :
    Subalgebra.center k (BinaryLeavittAlgebra k) = ⊥ := by
  refine le_antisymm ?_ ?_
  · rw [SetLike.le_def]
    intro z hz
    obtain ⟨c, hc⟩ := eq_smul_one_of_central k
      (fun y ↦ (Subalgebra.mem_center_iff.mp hz y).symm)
    refine Algebra.mem_bot.mpr ⟨c, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one]
    exact hc.symm
  · rw [SetLike.le_def]
    intro z hz
    obtain ⟨c, rfl⟩ := Algebra.mem_bot.mp hz
    exact Subalgebra.mem_center_iff.mpr fun b ↦ (Algebra.commutes c b).symm

/-- A central unit of `L_k(1,2)` is a nonzero scalar. -/
theorem central_unit_eq_smul_one (k : Type) [Field k]
    (u : (BinaryLeavittAlgebra k)ˣ)
    (hu : ∀ y : BinaryLeavittAlgebra k,
      (u : BinaryLeavittAlgebra k) * y = y * (u : BinaryLeavittAlgebra k)) :
    ∃ c : k, c ≠ 0 ∧ (u : BinaryLeavittAlgebra k) = c • 1 := by
  obtain ⟨c, hc⟩ := eq_smul_one_of_central k hu
  refine ⟨c, ?_, hc⟩
  intro hzero
  rw [hzero, zero_smul] at hc
  have hone : (1 : BinaryLeavittAlgebra k) = 0 := by
    have hmul := u.mul_inv
    rw [hc, zero_mul] at hmul
    exact hmul.symm
  exact one_ne_zero hone

/-- **The central units of `L_{𝔽₂}(1,2)` are trivial**: `Z(R)^× = 𝔽₂^× = 1`.
This is the only consequence of the centre computation that Proposition
`prop:simple` of the manuscript uses. -/
theorem central_units_trivial (u : (BinaryLeavittAlgebra (ZMod 2))ˣ)
    (hu : ∀ y : BinaryLeavittAlgebra (ZMod 2),
      (u : BinaryLeavittAlgebra (ZMod 2)) * y =
        y * (u : BinaryLeavittAlgebra (ZMod 2))) :
    u = 1 := by
  obtain ⟨c, hc0, hc⟩ := central_unit_eq_smul_one (ZMod 2) u hu
  have hc1 : c = 1 := by
    have hall : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    exact hall c hc0
  apply Units.ext
  rw [hc, hc1, one_smul, Units.val_one]

end BinaryLeavitt

end GroupApproximation
