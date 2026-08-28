import GroupApproximation.GGT.HullSCUnionGeometryLineal

/-!
# Prefixes of a normal form

The lineal branch of the crossing estimate bounds the conjugator by
`2·sylLength c ≤ |k|` and then needs: *there are at most that many candidates*,
because `c` is a prefix of `t` and prefixes are ordered by syllable count.  This
module supplies that.

`IsSyllablePrefix c t` says the normal form of `c` is an initial segment of the
normal form of `t`.  It is a *predicate*, not a construction: nothing here builds
an element out of `List.take`, which would need the `ne_one` and `IsChain`
invariants of a reduced word restricted to a take.  The two facts the count needs
hold for the predicate directly:

* `eq_of_isSyllablePrefix_of_length_eq` --- two prefixes of the same word with
  the same syllable count are equal, because both are the same `take`;
* `finite_syllablePrefix` --- so the prefixes of `t` with syllable count at most
  `n` form a finite set of cardinality at most `n + 1`, by injecting them into
  `Finset.range (n+1)` along `sylLength`.

That is one of the two finite sets `finite_of_conj_decomposition` consumes.

## The peel invariant, and what it does not settle

The next step is to iterate `conj_peel` and carry the invariant

    t = c · t' ,   t‾ = c‾ ++ t'‾ ,   sylLength c = j ,
    t⁻¹ k t = t'⁻¹ (c⁻¹ k c) t' ,

whose second clause gives `IsSyllablePrefix c t` outright.  Establishing it at
`j+1` means computing the normal form of `c · of u`, where `u` is the next
syllable of `t`; that is `toList_equiv_mul_of_seam`, whose hypothesis --- the last
syllable of `c` and `u` lie in different factors --- is the third component of
`List.isChain_append` applied to `t‾ = c‾ ++ (⟨i,u⟩ :: t''‾)`.  So the invariant
is reachable with the API in hand.

What the invariant does *not* settle is the terminating case.  Running the peel
until `conj_seam_cases` gives its first branch leaves `|t'| ≤ |t⁻¹kt|/2`, hence
`|c|` close to `|t|` --- and the lineal bound of
`two_mul_wordNorm_le_conj_conjugator` says a conjugator in a *no-cancellation*
decomposition of `k` has `2|c| ≤ |k|`, which is small.  The two are consistent
only because the decomposition `k = c · (c⁻¹kc) · c⁻¹` at the stopping stage is
not seam-free; which seam survives, and what that forces on `c⁻¹kc`, is the
clause still owed.
-/

namespace GroupApproximation
namespace HullSCUnionGeometry

open Monoid Monoid.CoprodI
open GroupApproximation.FreeProductCyclic

section Prefix

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
  [∀ i, DecidableEq (G i)]

/-- **`c` is a syllable prefix of `t`**: the normal form of `c` is an initial
segment of the normal form of `t`. -/
def IsSyllablePrefix (c t : CoprodI G) : Prop :=
  (Word.equiv c).toList <+: (Word.equiv t).toList

theorem isSyllablePrefix_one (t : CoprodI G) :
    IsSyllablePrefix (1 : CoprodI G) t := by
  have h : (Word.equiv (1 : CoprodI G)).toList = [] := by
    rw [equiv_one]; rfl
  show (Word.equiv (1 : CoprodI G)).toList <+: (Word.equiv t).toList
  rw [h]
  simp

theorem isSyllablePrefix_self (t : CoprodI G) : IsSyllablePrefix t t :=
  List.prefix_rfl

/-- A prefix has no more syllables than the word. -/
theorem sylLength_le_of_isSyllablePrefix {c t : CoprodI G}
    (h : IsSyllablePrefix c t) : sylLength c ≤ sylLength t :=
  List.IsPrefix.length_le h

/-- **A prefix is determined by its syllable count.**  Both prefixes are the
`take` of the same list at the same length, so their normal forms agree, and
`Word.equiv` is injective. -/
theorem eq_of_isSyllablePrefix_of_sylLength_eq {c₁ c₂ t : CoprodI G}
    (h₁ : IsSyllablePrefix c₁ t) (h₂ : IsSyllablePrefix c₂ t)
    (hlen : sylLength c₁ = sylLength c₂) : c₁ = c₂ := by
  have e₁ := List.prefix_iff_eq_take.mp h₁
  have e₂ := List.prefix_iff_eq_take.mp h₂
  refine Word.equiv.injective (Word.ext ?_)
  rw [e₁, e₂]
  exact congrArg (fun m => (Word.equiv t).toList.take m) hlen

/-- **There are at most `n + 1` prefixes of syllable count at most `n`.**

This is the first of the two finite sets `finite_of_conj_decomposition`
consumes, and it is obtained without enumerating any ball: the prefixes inject
into `Finset.range (n+1)` along their syllable count. -/
theorem finite_syllablePrefix (t : CoprodI G) (n : ℕ) :
    {c : CoprodI G | IsSyllablePrefix c t ∧ sylLength c ≤ n}.Finite ∧
      {c : CoprodI G | IsSyllablePrefix c t ∧ sylLength c ≤ n}.ncard ≤ n + 1 := by
  classical
  have hinj : Set.InjOn sylLength
      {c : CoprodI G | IsSyllablePrefix c t ∧ sylLength c ≤ n} := by
    intro a ha b hb hab
    exact eq_of_isSyllablePrefix_of_sylLength_eq ha.1 hb.1 hab
  have hmaps : ∀ c ∈ {c : CoprodI G | IsSyllablePrefix c t ∧ sylLength c ≤ n},
      sylLength c ∈ (↑(Finset.range (n + 1)) : Set ℕ) := by
    intro c hc
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le hc.2
  have himg : sylLength '' {c : CoprodI G | IsSyllablePrefix c t ∧ sylLength c ≤ n}
      ⊆ (↑(Finset.range (n + 1)) : Set ℕ) := by
    rintro y ⟨c, hc, rfl⟩
    exact hmaps c hc
  refine ⟨Set.Finite.of_finite_image
    (Set.Finite.subset (Finset.finite_toSet _) himg) hinj, ?_⟩
  calc {c : CoprodI G | IsSyllablePrefix c t ∧ sylLength c ≤ n}.ncard
      ≤ (↑(Finset.range (n + 1)) : Set ℕ).ncard :=
        Set.ncard_le_ncard_of_injOn sylLength hmaps hinj (Finset.finite_toSet _)
    _ = (Finset.range (n + 1)).card := Set.ncard_coe_finset _
    _ = n + 1 := Finset.card_range _

end Prefix

end HullSCUnionGeometry
end GroupApproximation
