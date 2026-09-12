import GroupApproximation.Leavitt.AryDivision
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# The centre of `L_k(1,d)` is `k`, for every field and every `d ≥ 2`

`non_mf_groups_exist.tex`, proof of Theorem `thm:headline`, line 1146:

> So `λ` lies in `Z(R) = 𝔽₂`~\cite[Corollary~4.3]{ArandaCrow}, and `N = 1`.

At the printed instance `R = L_{𝔽₂}(1,2)` that clause is already closed in the
tree by `BinaryLeavitt.center_eq_bot`, which computes the centre of `L_k(1,2)`
for every field `k`.  This module proves the same for every arity: the centre
of `L_k(1,d)` is the base field, for every field `k` and every `d ≥ 2`.  That
is Aranda Pino--Crow, Corollary 4.3 (the centre of a simple Leavitt path
algebra), specialised to the `d`-rose, proved here from the monomial normal
form rather than cited.

## The argument

A central `z` is fixed by every sandwich `t_W z s_W` with `t_W s_W = 1`, so it
is fixed by the sandwich with the annihilating word `W = i₀^r i₁` of
`AryKillWord`, where `r` bounds the lengths of all the monomials occurring in a
fixed monomial representation of `z`.  That sandwich sends each monomial
`s_α t_β` to `0` or to `1`, so `z` is a scalar.

The dichotomy `killWord_sandwich_monomial` is the arity-`d` form of
`BinaryLeavitt.killWord_sandwich_monomial`.  It holds over an arbitrary ring
carrying a complete matrix family with two distinct indices, so it is stated
for `CompleteMatrixFamily` rather than for the Leavitt algebra.

## Where `2 ≤ d` is load-bearing

The annihilating word needs two distinct letters, exactly as in
`Leavitt/AryKillWord.lean`.  The hypothesis is not merely convenient: at
`d = 1`, `L_k(1,1) ≅ k[x, x⁻¹]` is commutative, so its centre is all of it and
the conclusion is false.
-/

namespace GroupApproximation

/-! ### Prefix combinatorics of the annihilating words `i₀^r i₁`

`Leavitt/AryKillWord.lean` proves the one fact its own division argument needs.
The centre computation needs three more, all elementary. -/

namespace AryKillWord

variable {ι : Type*}

/-- Prefixing letters `i₀` lengthens the annihilating word. -/
theorem replicate_append_killWord (i₀ i₁ : ι) (a m : ℕ) :
    List.replicate a i₀ ++ killWord i₀ i₁ m = killWord i₀ i₁ (a + m) := by
  unfold killWord
  rw [← List.append_assoc, ← List.replicate_add]

/-- Splitting off a run of `i₀` from the front of `i₀^r i₁`. -/
theorem killWord_eq_replicate_append (i₀ i₁ : ι) {a r : ℕ} (h : a ≤ r) :
    killWord i₀ i₁ r = List.replicate a i₀ ++ killWord i₀ i₁ (r - a) := by
  rw [replicate_append_killWord, show a + (r - a) = r from by omega]

/-- A word of length at most `r` which is a prefix of `i₀^r i₁` is a run of
`i₀`: the letter `i₁` sits beyond position `r`. -/
theorem eq_replicate_of_prefix_killWord {i₀ i₁ : ι} {α : List ι} {r : ℕ}
    (hpre : α <+: killWord i₀ i₁ r) (hlen : α.length ≤ r) :
    α = List.replicate α.length i₀ := by
  have hpre₀ : α <+: List.replicate r i₀ ++ [i₁] := hpre
  have hle : α.length ≤ (List.replicate r i₀).length := by
    rw [List.length_replicate]
    exact hlen
  have hpre₁ : α <+: List.replicate r i₀ :=
    (List.isPrefix_append_of_length hle).mp hpre₀
  refine List.eq_replicate_iff.mpr ⟨rfl, fun b hb ↦ ?_⟩
  exact List.eq_of_mem_replicate (hpre₁.subset hb)

/-- Two annihilating words of different lengths are incomparable: they disagree
at the position of the earlier `i₁`. -/
theorem killWord_not_prefix_killWord {i₀ i₁ : ι} (hne : i₁ ≠ i₀) {m n : ℕ}
    (hmn : m ≠ n) : ¬ killWord i₀ i₁ m <+: killWord i₀ i₁ n := by
  intro hpre
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · have hm1 : m < (killWord i₀ i₁ m).length := by
      rw [killWord_length]
      omega
    have hm2 : m < (killWord i₀ i₁ n).length := by
      rw [killWord_length]
      omega
    have hagree : (killWord i₀ i₁ m)[m]'hm1 = (killWord i₀ i₁ n)[m]'hm2 :=
      hpre.getElem hm1
    have hleft : (killWord i₀ i₁ m)[m]'hm1 = i₁ := by
      unfold killWord
      rw [List.getElem_append_right (by simp)]
      simp
    have hright : (killWord i₀ i₁ n)[m]'hm2 = i₀ := by
      unfold killWord
      rw [List.getElem_append_left (by
        rw [List.length_replicate]
        omega)]
      simp
    rw [hleft, hright] at hagree
    exact hne hagree
  · have hlen := hpre.length_le
    rw [killWord_length, killWord_length] at hlen
    omega

end AryKillWord

/-! ### The kill-word sandwich is a scalar on monomials -/

namespace CompleteMatrixFamily

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The kill-word sandwich is `0` or `1` on every monomial.**

For `|α|, |β| ≤ r` and `W = i₀^r i₁` with `i₁ ≠ i₀`, the element
`t_W (s_α t_β) s_W` is `1` when `α` and `β` are runs of `i₀` of the same
length, and `0` in every other case.  Only the dichotomy is recorded, which is
what the centre computation consumes.

This is `BinaryLeavitt.killWord_sandwich_monomial` at arbitrary arity; the
binary file's `by decide` on `Fin 2` becomes the hypothesis `i₁ ≠ i₀`. -/
theorem killWord_sandwich_monomial (F : CompleteMatrixFamily A ι) {i₀ i₁ : ι}
    (hne : i₁ ≠ i₀) (r : ℕ) (α β : List ι) (hα : α.length ≤ r)
    (hβ : β.length ≤ r) :
    F.wordT (AryKillWord.killWord i₀ i₁ r) * (F.wordS α * F.wordT β) *
        F.wordS (AryKillWord.killWord i₀ i₁ r) = 0 ∨
      F.wordT (AryKillWord.killWord i₀ i₁ r) * (F.wordS α * F.wordT β) *
        F.wordS (AryKillWord.killWord i₀ i₁ r) = 1 := by
  by_cases hαW : α <+: AryKillWord.killWord i₀ i₁ r
  · -- `α` is a prefix of `W`, hence a run of `i₀`
    have hαrep : α = List.replicate α.length i₀ :=
      AryKillWord.eq_replicate_of_prefix_killWord hαW hα
    have hWsplit : AryKillWord.killWord i₀ i₁ r
        = α ++ AryKillWord.killWord i₀ i₁ (r - α.length) := by
      rw [AryKillWord.killWord_eq_replicate_append i₀ i₁ hα, ← hαrep]
    have hcollapse :
        F.wordT (AryKillWord.killWord i₀ i₁ r) * F.wordS α
          = F.wordT (AryKillWord.killWord i₀ i₁ (r - α.length)) := by
      conv_lhs => rw [hWsplit]
      exact F.wordT_append_mul_wordS α _
    have hmain :
        F.wordT (AryKillWord.killWord i₀ i₁ r) * (F.wordS α * F.wordT β) *
            F.wordS (AryKillWord.killWord i₀ i₁ r)
          = F.wordT (β ++ AryKillWord.killWord i₀ i₁ (r - α.length)) *
              F.wordS (AryKillWord.killWord i₀ i₁ r) := by
      calc F.wordT (AryKillWord.killWord i₀ i₁ r) * (F.wordS α * F.wordT β) *
            F.wordS (AryKillWord.killWord i₀ i₁ r)
          = (F.wordT (AryKillWord.killWord i₀ i₁ r) * F.wordS α) * F.wordT β *
              F.wordS (AryKillWord.killWord i₀ i₁ r) := by
            simp only [mul_assoc]
        _ = (F.wordT (AryKillWord.killWord i₀ i₁ (r - α.length)) * F.wordT β) *
              F.wordS (AryKillWord.killWord i₀ i₁ r) := by
            rw [hcollapse]
        _ = F.wordT (β ++ AryKillWord.killWord i₀ i₁ (r - α.length)) *
              F.wordS (AryKillWord.killWord i₀ i₁ r) := by
            rw [F.wordT_append]
    by_cases hβrep : β = List.replicate β.length i₀
    · -- `β` is a run of `i₀`: the two kill words survive or cancel by length
      have hβW : β ++ AryKillWord.killWord i₀ i₁ (r - α.length)
          = AryKillWord.killWord i₀ i₁ (β.length + (r - α.length)) := by
        conv_lhs => rw [hβrep]
        exact AryKillWord.replicate_append_killWord i₀ i₁ _ _
      rw [hmain, hβW]
      by_cases hcase : β.length = α.length
      · right
        rw [show β.length + (r - α.length) = r from by omega]
        exact F.wordT_mul_wordS_self (AryKillWord.killWord i₀ i₁ r)
      · left
        have hne' : β.length + (r - α.length) ≠ r := by omega
        exact F.wordT_mul_wordS_of_incomparable _ _
          (AryKillWord.killWord_not_prefix_killWord hne hne')
          (AryKillWord.killWord_not_prefix_killWord hne (Ne.symm hne'))
    · -- `β` carries some letter other than `i₀` inside the first `r` positions
      left
      rw [hmain]
      have hβnotpre : ¬ β <+: AryKillWord.killWord i₀ i₁ r := fun hpre ↦
        hβrep (AryKillWord.eq_replicate_of_prefix_killWord hpre hβ)
      refine F.wordT_mul_wordS_of_incomparable _ _ ?_ ?_
      · intro hcon
        exact hβnotpre
          ((List.prefix_append β
            (AryKillWord.killWord i₀ i₁ (r - α.length))).trans hcon)
      · intro hcon
        obtain ⟨t, ht⟩ := hcon
        have hβpre : β <+: AryKillWord.killWord i₀ i₁ r ++ t := by
          rw [ht]
          exact List.prefix_append β _
        have hlenle : β.length ≤ (AryKillWord.killWord i₀ i₁ r).length := by
          rw [AryKillWord.killWord_length]
          omega
        exact hβnotpre ((List.isPrefix_append_of_length hlenle).mp hβpre)
  · -- `α` is incomparable with `W`, so the sandwich already dies on the left
    left
    have hWα : ¬ AryKillWord.killWord i₀ i₁ r <+: α := by
      intro hcon
      have hlenle := hcon.length_le
      rw [AryKillWord.killWord_length] at hlenle
      omega
    have h0 : F.wordT (AryKillWord.killWord i₀ i₁ r) * F.wordS α = 0 :=
      F.wordT_mul_wordS_of_incomparable _ _ hWα hαW
    calc F.wordT (AryKillWord.killWord i₀ i₁ r) * (F.wordS α * F.wordT β) *
          F.wordS (AryKillWord.killWord i₀ i₁ r)
        = (F.wordT (AryKillWord.killWord i₀ i₁ r) * F.wordS α) *
            (F.wordT β * F.wordS (AryKillWord.killWord i₀ i₁ r)) := by
          simp only [mul_assoc]
      _ = 0 := by rw [h0, zero_mul]

end CompleteMatrixFamily

/-! ### The centre of `L_k(1,d)` -/

namespace AryLeavitt

variable (k : Type*) [Field k] (d : ℕ)

/-- **Every central element of `L_k(1,d)` is a scalar**, for every field `k` and
every `d ≥ 2` (Aranda Pino--Crow, Corollary 4.3, proved here from the monomial
normal form). -/
theorem eq_smul_one_of_central (hd : 2 ≤ d) {z : AryLeavittAlgebra k d}
    (hz : ∀ y : AryLeavittAlgebra k d, z * y = y * z) :
    ∃ c : k, z = c • 1 := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨n, co, al, be, hrep⟩ := exists_monomial_representation k d z
  set L := family k d
  obtain ⟨i₀, i₁, hne⟩ : ∃ i₀ i₁ : Fin d, i₁ ≠ i₀ := by
    refine ⟨0, ⟨1, hd⟩, ?_⟩
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  obtain ⟨r, hal, hbe⟩ : ∃ r : ℕ,
      (∀ i : Fin n, (al i).length ≤ r) ∧ (∀ i : Fin n, (be i).length ≤ r) := by
    refine ⟨Finset.univ.sup (fun i : Fin n ↦ max (al i).length (be i).length),
      fun i ↦ ?_, fun i ↦ ?_⟩
    · exact le_trans (le_max_left _ _)
        (Finset.le_sup (f := fun i : Fin n ↦
          max (al i).length (be i).length) (Finset.mem_univ i))
    · exact le_trans (le_max_right _ _)
        (Finset.le_sup (f := fun i : Fin n ↦
          max (al i).length (be i).length) (Finset.mem_univ i))
  -- centrality makes the kill-word sandwich fix `z`
  have hfix :
      L.wordT (AryKillWord.killWord i₀ i₁ r) * z *
        L.wordS (AryKillWord.killWord i₀ i₁ r) = z := by
    calc L.wordT (AryKillWord.killWord i₀ i₁ r) * z *
          L.wordS (AryKillWord.killWord i₀ i₁ r)
        = L.wordT (AryKillWord.killWord i₀ i₁ r) *
            (z * L.wordS (AryKillWord.killWord i₀ i₁ r)) := mul_assoc _ _ _
      _ = L.wordT (AryKillWord.killWord i₀ i₁ r) *
            (L.wordS (AryKillWord.killWord i₀ i₁ r) * z) := by rw [hz]
      _ = L.wordT (AryKillWord.killWord i₀ i₁ r) *
            L.wordS (AryKillWord.killWord i₀ i₁ r) * z := (mul_assoc _ _ _).symm
      _ = z := by rw [L.wordT_mul_wordS_self, one_mul]
  -- and distributes over the monomial representation
  have hexp :
      L.wordT (AryKillWord.killWord i₀ i₁ r) * z *
          L.wordS (AryKillWord.killWord i₀ i₁ r) =
        ∑ i : Fin n, co i • (L.wordT (AryKillWord.killWord i₀ i₁ r) *
          (L.wordS (al i) * L.wordT (be i)) *
            L.wordS (AryKillWord.killWord i₀ i₁ r)) := by
    rw [hrep, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_smul_comm, smul_mul_assoc]
  -- every sandwiched monomial is a scalar
  have hdicho : ∀ i : Fin n, ∃ c : k,
      L.wordT (AryKillWord.killWord i₀ i₁ r) *
          (L.wordS (al i) * L.wordT (be i)) *
            L.wordS (AryKillWord.killWord i₀ i₁ r) =
        c • (1 : AryLeavittAlgebra k d) := by
    intro i
    rcases L.killWord_sandwich_monomial hne r (al i) (be i) (hal i) (hbe i) with
      h | h
    · exact ⟨0, by rw [zero_smul]; exact h⟩
    · exact ⟨1, by rw [one_smul]; exact h⟩
  choose c hc using hdicho
  refine ⟨∑ i : Fin n, co i * c i, ?_⟩
  calc z = L.wordT (AryKillWord.killWord i₀ i₁ r) * z *
          L.wordS (AryKillWord.killWord i₀ i₁ r) := hfix.symm
    _ = ∑ i : Fin n, co i • (L.wordT (AryKillWord.killWord i₀ i₁ r) *
          (L.wordS (al i) * L.wordT (be i)) *
            L.wordS (AryKillWord.killWord i₀ i₁ r)) := hexp
    _ = ∑ i : Fin n, (co i * c i) • (1 : AryLeavittAlgebra k d) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hc i, smul_smul]
    _ = (∑ i : Fin n, co i * c i) • (1 : AryLeavittAlgebra k d) := by
          rw [Finset.sum_smul]

/-- **The centre of `L_k(1,d)` is the base field**, for every field `k` and
every `d ≥ 2` (Aranda Pino--Crow, Corollary 4.3).

At `k = 𝔽₂`, `d = 2` this is the printed `Z(R) = 𝔽₂`; that instance is also
available directly as `BinaryLeavitt.center_eq_bot`. -/
theorem center_eq_bot (hd : 2 ≤ d) :
    Subalgebra.center k (AryLeavittAlgebra k d) = ⊥ := by
  refine le_antisymm ?_ ?_
  · rw [SetLike.le_def]
    intro z hz
    obtain ⟨c, hc⟩ := eq_smul_one_of_central k d hd
      (fun y ↦ (Subalgebra.mem_center_iff.mp hz y).symm)
    refine Algebra.mem_bot.mpr ⟨c, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one]
    exact hc.symm
  · rw [SetLike.le_def]
    intro z hz
    obtain ⟨c, rfl⟩ := Algebra.mem_bot.mp hz
    exact Subalgebra.mem_center_iff.mpr fun b ↦ (Algebra.commutes c b).symm

end AryLeavitt

/-! ### The printed sentence -/

/-- **Printed:** "So `λ` lies in `Z(R) = 𝔽₂`~\cite[Corollary 4.3]{ArandaCrow}"
(`non_mf_groups_exist.tex` line 1146), at the full generality of the cited
corollary for the `d`-rose: the centre of `L_k(1,d)` is `k`, for every field
and every `d ≥ 2`. -/
def AryLeavittCentreIsBaseField : Prop :=
  ∀ (k : Type) [Field k] (d : ℕ), 2 ≤ d →
    Subalgebra.center k (AryLeavitt.AryLeavittAlgebra k d) = ⊥

/-- Closed proof of the printed centre computation, at every arity. -/
theorem manuscriptSentence_leavittCentreIsBaseField :
    AryLeavittCentreIsBaseField := by
  intro k _ d hd
  exact AryLeavitt.center_eq_bot k d hd

end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.AryLeavitt.eq_smul_one_of_central
#audit_axioms GroupApproximation.AryLeavitt.center_eq_bot
#audit_closed_axioms GroupApproximation.manuscriptSentence_leavittCentreIsBaseField
