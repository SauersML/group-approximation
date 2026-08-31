import GroupApproximation.GGT.HullSCRelatorSeparation2ThroughBase

/-!
# Finite avoidance for genuinely cyclic through-base windows

If an exponent list is split as `pre ++ n :: post`, a forward cyclic window
which starts at `n` and crosses the unique base letter reads a suffix of
`post`, followed by the base letter, followed by a prefix of `pre`.  The older
through-base predicate used `post` on both sides and therefore did not describe
such a cyclic window.  This file gives the finite bad set needed to preserve
the correct `post`/`pre` predicate when a new exponent is prepended.
-/

namespace GroupApproximation
namespace HullSC

universe u

section CyclicThroughBase

variable {G : Type u} [Group G]

/-- The source-faithful through-base clause for a cyclic exponent list. -/
def CyclicThroughBaseAvoidance (D : GGT.RelGenSet G Bool) (a : Bool → G)
    (baseLetter : G) (W : ℕ) (ms : List ℕ) : Prop :=
  ∀ pre post : List ℕ, ∀ n : ℕ, ms = pre ++ n :: post →
    ∀ s b₀ b₁ : Bool, ∀ r₀ r₁ : ℕ, r₀ ≤ W → r₁ ≤ W →
      a s ^ n *
          GGT.RelLetter.listVal
            (blockWord (a false) (a true) b₀ (post.take r₀)) *
          baseLetter *
          GGT.RelLetter.listVal
            (blockWord (a false) (a true) b₁ (pre.take r₁))
        ∉ D.fam (!s)

/-- Powers of a newly prepended exponent which would destroy a cyclic
through-base window starting at an exponent already in `ms`. -/
def cyclicThroughBasePrefixBadPow (D : GGT.RelGenSet G Bool) (a : Bool → G)
    (ms : List ℕ) (W : ℕ) (baseLetter : G) : Set G :=
  ⋃ k : Fin ms.length, ⋃ s : Bool, ⋃ b₀ : Bool, ⋃ b₁ : Bool,
    ⋃ r₀ ∈ Set.Iic W, ⋃ r₁ ∈ Set.Iic W,
      (fun m : ℕ => a b₁ ^ m) ''
        {m : ℕ |
          a s ^ ms[k] *
              GGT.RelLetter.listVal
                (blockWord (a false) (a true) b₀
                  ((ms.drop (k + 1)).take r₀)) *
              baseLetter * a b₁ ^ m *
              GGT.RelLetter.listVal
                (blockWord (a false) (a true) (!b₁)
                  ((ms.take k).take r₁))
            ∈ D.fam (!s)}

/-- The obstruction set is finite.  In the only delicate case the new power
belongs to the target peripheral subgroup.  The old cyclic clause with an
empty right prefix says that the fixed left context is outside that subgroup,
which is precisely the hypothesis of the two-sided finite-power lemma. -/
theorem finite_cyclicThroughBasePrefixBadPow
    {D : GGT.RelGenSet G Bool} (hemb : D.IsHyperbolicallyEmbedded)
    {a : Bool → G}
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hmem : ∀ s : Bool, a s ∈ D.fam s) (ms : List ℕ)
    (W : ℕ) (baseLetter : G)
    (hold : CyclicThroughBaseAvoidance D a baseLetter W ms) :
    (cyclicThroughBasePrefixBadPow D a ms W baseLetter).Finite := by
  refine Set.finite_iUnion fun k => Set.finite_iUnion fun s =>
    Set.finite_iUnion fun b₀ => Set.finite_iUnion fun b₁ => ?_
  refine (Set.finite_Iic W).biUnion ?_
  intro r₀ hr₀
  refine (Set.finite_Iic W).biUnion ?_
  intro r₁ hr₁
  refine Set.Finite.image _ ?_
  let A : G :=
    a s ^ ms[k] *
        GGT.RelLetter.listVal
          (blockWord (a false) (a true) b₀
            ((ms.drop (k + 1)).take r₀)) * baseLetter
  let B : G :=
    GGT.RelLetter.listVal
      (blockWord (a false) (a true) (!b₁) ((ms.take k).take r₁))
  have hsplit : ms = ms.take k ++ ms[k] :: ms.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons k.isLt, ← List.take_append_drop k ms]
  have hmid : ¬ (b₁ = !s ∧ A ∈ D.fam (!s)) := by
    rintro ⟨hbs, hA⟩
    have hnot := hold (ms.take k) (ms.drop (k + 1)) ms[k] hsplit s b₀ b₁
      r₀ 0 hr₀ (Nat.zero_le _)
    apply hnot
    simpa only [List.take_zero, blockWord_nil, GGT.RelLetter.listVal_nil,
      mul_one, A] using hA
  have hpow : ∀ n : ℕ, a b₁ ^ n ∈ D.fam b₁ :=
    fun n => pow_mem (hmem b₁) n
  simpa only [A, B, mul_assoc] using
    (finite_mul_pow_mul_mem_fam hemb hmid (hinj b₁) hpow)

/-- Avoiding the obstruction set makes every old split survive after a new
exponent is prepended. -/
theorem cyclicThroughBaseAvoidance_cons
    {D : GGT.RelGenSet G Bool} {a : Bool → G} {baseLetter : G}
    {ms : List ℕ} {W m : ℕ}
    (hold : CyclicThroughBaseAvoidance D a baseLetter W ms)
    (hnewHead : ∀ s b₀ b₁ : Bool, ∀ r₀ : ℕ, r₀ ≤ W →
      a s ^ m *
          GGT.RelLetter.listVal
            (blockWord (a false) (a true) b₀ (ms.take r₀)) *
          baseLetter *
          GGT.RelLetter.listVal
            (blockWord (a false) (a true) b₁ ([] : List ℕ))
        ∉ D.fam (!s))
    (hbad : ∀ b : Bool,
      a b ^ m ∉ cyclicThroughBasePrefixBadPow D a ms W baseLetter) :
    CyclicThroughBaseAvoidance D a baseLetter W (m :: ms) := by
  intro pre post n hsplit s b₀ b₁ r₀ r₁ hr₀ hr₁
  cases pre with
  | nil =>
      rw [List.nil_append, List.cons.injEq] at hsplit
      obtain ⟨hmn, hmspost⟩ := hsplit
      subst hmn
      subst hmspost
      simpa only [List.take_nil] using hnewHead s b₀ b₁ r₀ hr₀
  | cons x pre' =>
      rw [List.cons_append, List.cons.injEq] at hsplit
      have htail : ms = pre' ++ n :: post := hsplit.2
      cases r₁ with
      | zero =>
          simpa only [List.take_zero, blockWord_nil,
            GGT.RelLetter.listVal_nil, mul_one] using
            hold pre' post n htail s b₀ b₁ r₀ 0 hr₀ (Nat.zero_le _)
      | succ r =>
          have hr : r ≤ W := by omega
          have hpreLen : pre'.length < ms.length := by
            rw [htail, List.length_append, List.length_cons]
            omega
          let k : Fin ms.length := ⟨pre'.length, hpreLen⟩
          have hkval : ms[k] = n := by
            simp [k, htail]
          have hkdrop : ms.drop (k + 1) = post := by
            simp [k, htail]
          have hktake : ms.take k = pre' := by
            simp [k, htail]
          intro hc
          apply hbad b₁
          refine Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨s,
            Set.mem_iUnion.mpr ⟨b₀, Set.mem_iUnion.mpr ⟨b₁, ?_⟩⟩⟩⟩
          refine Set.mem_biUnion hr₀ (Set.mem_biUnion hr ?_)
          refine ⟨m, ?_, rfl⟩
          have hab : (if b₁ then a true else a false) = a b₁ := by
            cases b₁ <;> rfl
          simpa only [hkval, hkdrop, hktake, List.take_succ_cons,
            blockWord_cons, RelWord.listVal_cons, hab, mul_assoc]
            using hc

end CyclicThroughBase

end HullSC
end GroupApproximation
