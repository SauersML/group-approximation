import GroupApproximation.GGT.OsinTheorem54SepEnum

/-!
# Splitting a Λ-indexed family of index sets at two thresholds

The counting in Osin's Lemma 4.9 is bookkeeping about one family of subsets of
`ℕ`: the penetration indices of a fixed geodesic, one set per `λ`.  This module
carries that bookkeeping and nothing else --- no geodesic, no coset, no group.

Two facts are proved.

* Any set of naturals splits at two thresholds `m`, `m'` into what lies below
  `m`, what lies between, and what lies above `m'`, and the three counts add up
  to at least the whole.  No relation between `m` and `m'` is needed: if
  `m' < m` the middle piece is empty.
* If the family is DISJOINT --- no index belongs to two members --- and the
  middle piece can only hold `m` and `m'`, then the middle contributes at most
  `2` **in total over `Λ`**, not `2` per `λ`.  That is where Osin's global
  defect of two comes from, and it is why the Λ-sum in `sep_le_dist_enlargedY`
  can carry the constant `3 = 1 + 2` rather than something proportional to the
  size of the family.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe w

variable {Λ : Type w}

/-- **A set of naturals splits at two thresholds.** -/
theorem ncard_le_split (A : Set ℕ) (hA : A.Finite) (m m' : ℕ) :
    A.ncard ≤ (A ∩ {n | n < m}).ncard + (A ∩ {n | m ≤ n ∧ n ≤ m'}).ncard
      + (A ∩ {n | m' < n}).ncard := by
  have hsub : A ⊆ (A ∩ {n | n < m}) ∪
      ((A ∩ {n | m ≤ n ∧ n ≤ m'}) ∪ (A ∩ {n | m' < n})) := by
    intro x hx
    rcases Nat.lt_or_ge x m with h1 | h1
    · exact Or.inl ⟨hx, h1⟩
    · rcases Nat.lt_or_ge m' x with h2 | h2
      · exact Or.inr (Or.inr ⟨hx, h2⟩)
      · exact Or.inr (Or.inl ⟨hx, h1, h2⟩)
  have hf1 : (A ∩ {n | n < m}).Finite := hA.inter_of_left _
  have hf2 : (A ∩ {n | m ≤ n ∧ n ≤ m'}).Finite := hA.inter_of_left _
  have hf3 : (A ∩ {n | m' < n}).Finite := hA.inter_of_left _
  calc A.ncard
      ≤ ((A ∩ {n | n < m}) ∪
          ((A ∩ {n | m ≤ n ∧ n ≤ m'}) ∪ (A ∩ {n | m' < n}))).ncard :=
        Set.ncard_le_ncard hsub (hf1.union (hf2.union hf3))
    _ ≤ (A ∩ {n | n < m}).ncard +
          ((A ∩ {n | m ≤ n ∧ n ≤ m'}) ∪ (A ∩ {n | m' < n})).ncard :=
        Set.ncard_union_le _ _
    _ ≤ (A ∩ {n | n < m}).ncard +
          ((A ∩ {n | m ≤ n ∧ n ≤ m'}).ncard + (A ∩ {n | m' < n}).ncard) :=
        Nat.add_le_add_left (Set.ncard_union_le _ _) _
    _ = (A ∩ {n | n < m}).ncard + (A ∩ {n | m ≤ n ∧ n ≤ m'}).ncard
          + (A ∩ {n | m' < n}).ncard := by
        omega

/-- **A disjoint family meets one index at most once, in total.** -/
theorem sum_ncard_inter_singleton_le_one [Fintype Λ] (A : Λ → Set ℕ)
    (hdisj : ∀ (lam mu : Λ) (n : ℕ), n ∈ A lam → n ∈ A mu → lam = mu) (t : ℕ) :
    (∑ lam : Λ, (A lam ∩ {t}).ncard) ≤ 1 := by
  classical
  by_cases hex : ∃ lam : Λ, t ∈ A lam
  · obtain ⟨lam0, hlam0⟩ := hex
    have hzero : ∀ lam ∈ (Finset.univ : Finset Λ), lam ≠ lam0 →
        (A lam ∩ {t}).ncard = 0 := by
      intro lam _ hne
      have hempty : A lam ∩ {t} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.mpr ?_
        rintro x ⟨hx, hxt⟩
        have hxt' : x = t := hxt
        subst hxt'
        exact hne (hdisj lam lam0 x hx hlam0)
      rw [hempty, Set.ncard_empty]
    rw [Finset.sum_eq_single_of_mem lam0 (Finset.mem_univ lam0) hzero]
    calc (A lam0 ∩ {t}).ncard
        ≤ ({t} : Set ℕ).ncard :=
          Set.ncard_le_ncard Set.inter_subset_right (Set.finite_singleton t)
      _ = 1 := Set.ncard_singleton t
  · have hzero : (∑ lam : Λ, (A lam ∩ {t}).ncard) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro lam _
      have hempty : A lam ∩ {t} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.mpr ?_
        rintro x ⟨hx, hxt⟩
        have hxt' : x = t := hxt
        subst hxt'
        exact hex ⟨lam, hx⟩
      rw [hempty, Set.ncard_empty]
    omega

/-- **The middle piece costs two, in total over `Λ`.** -/
theorem sum_ncard_middle_le_two [Fintype Λ] (A : Λ → Set ℕ)
    (hfin : ∀ lam : Λ, (A lam).Finite)
    (hdisj : ∀ (lam mu : Λ) (n : ℕ), n ∈ A lam → n ∈ A mu → lam = mu)
    {m m' : ℕ}
    (hmid : ∀ (lam : Λ) (n : ℕ), n ∈ A lam → m ≤ n → n ≤ m' → n = m ∨ n = m') :
    (∑ lam : Λ, (A lam ∩ {n | m ≤ n ∧ n ≤ m'}).ncard) ≤ 2 := by
  have hstep : ∀ lam : Λ, (A lam ∩ {n | m ≤ n ∧ n ≤ m'}).ncard
      ≤ (A lam ∩ {m}).ncard + (A lam ∩ {m'}).ncard := by
    intro lam
    have hsub : A lam ∩ {n | m ≤ n ∧ n ≤ m'} ⊆ (A lam ∩ {m}) ∪ (A lam ∩ {m'}) := by
      rintro x ⟨hx, hx1, hx2⟩
      rcases hmid lam x hx hx1 hx2 with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    have hfm : (A lam ∩ {m}).Finite := (hfin lam).inter_of_left _
    have hfm' : (A lam ∩ {m'}).Finite := (hfin lam).inter_of_left _
    calc (A lam ∩ {n | m ≤ n ∧ n ≤ m'}).ncard
        ≤ ((A lam ∩ {m}) ∪ (A lam ∩ {m'})).ncard :=
          Set.ncard_le_ncard hsub (hfm.union hfm')
      _ ≤ (A lam ∩ {m}).ncard + (A lam ∩ {m'}).ncard :=
          Set.ncard_union_le _ _
  have hsum : (∑ lam : Λ, (A lam ∩ {n | m ≤ n ∧ n ≤ m'}).ncard)
      ≤ (∑ lam : Λ, (A lam ∩ {m}).ncard) + ∑ lam : Λ, (A lam ∩ {m'}).ncard := by
    calc (∑ lam : Λ, (A lam ∩ {n | m ≤ n ∧ n ≤ m'}).ncard)
        ≤ ∑ lam : Λ, ((A lam ∩ {m}).ncard + (A lam ∩ {m'}).ncard) :=
          Finset.sum_le_sum (fun lam _ => hstep lam)
      _ = (∑ lam : Λ, (A lam ∩ {m}).ncard) + ∑ lam : Λ, (A lam ∩ {m'}).ncard :=
          Finset.sum_add_distrib
  have h1 := sum_ncard_inter_singleton_le_one A hdisj m
  have h2 := sum_ncard_inter_singleton_le_one A hdisj m'
  omega

end OsinComponents
end GGT
end GroupApproximation
