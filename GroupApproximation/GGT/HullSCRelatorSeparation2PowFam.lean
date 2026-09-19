import GroupApproximation.GGT.HullSCRelatorSeparation2Cross

/-!
# How often a power of one element lands in the other subgroup

The windowed same-side exclusion asks whether an alternating product of block
letters can lie in `H_λ`.  Stripping the first letter, which is in `H_λ`, leaves
a product whose leftmost letter is a power of the *other* element, so the
question at each step is: for a fixed tail `G`, for how many exponents `n` is
`a_{¬λ}^n · G` in `H_λ`?

The answer is: finitely many, and it needs nothing but local finiteness.

* `finite_pow_mem_fam` -- `{d : a^d ∈ H_λ}` is finite when `a` lies in the other
  member of the family.  A power of `a` lying in `H_λ` too is at d̂_λ-distance
  one (`HullSC.mem_relBall_one_of_mem_fam_ne`), the ball of radius one is
  finite, and the powers are pairwise distinct.
* `finite_pow_mul_mem_fam` -- so `{n : a^n · G ∈ H_λ}` is finite for any fixed
  `G`: two of its elements differ by an exponent of the first kind, since
  `(a^n G)(a^{n'} G)⁻¹ = a^{n - n'}`, so the whole set sits in a translate of a
  finite set together with an initial segment.

These are the two finiteness facts the greedy design consumes when it has to
avoid, at each step, the exponents that would make some window close up.  Both
are stated for a general index type, since neither uses that there are two
subgroups.
-/

namespace GroupApproximation
namespace HullSC

universe u w

section PowFam

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A power of one element lies in another member of the family only finitely
often.** -/
theorem finite_pow_mem_fam {D : GGT.RelGenSet G Λ} (hemb : D.IsHyperbolicallyEmbedded)
    {a : G} {lam mu : Λ} (hne : mu ≠ lam)
    (hinj : Function.Injective (fun n : ℕ => a ^ n))
    (hmem : ∀ n : ℕ, a ^ n ∈ D.fam mu) :
    {d : ℕ | a ^ d ∈ D.fam lam}.Finite := by
  refine Set.Finite.subset
    (Set.Finite.preimage (fun _ _ _ _ hxy => hinj hxy) (hemb.locallyFinite lam 1))
    ?_
  intro d hd
  exact mem_relBall_one_of_mem_fam_ne hne (hmem d) hd

/-- **With a tail fixed, only finitely many exponents close the window.**

Two exponents that both close it differ by one of the exponents above: the tails
cancel between `a^n · G` and `a^{n'} · G`. -/
theorem finite_pow_mul_mem_fam {D : GGT.RelGenSet G Λ} {lam : Λ} {a G₀ : G}
    (hfin : {d : ℕ | a ^ d ∈ D.fam lam}.Finite) :
    {n : ℕ | a ^ n * G₀ ∈ D.fam lam}.Finite := by
  rcases Set.eq_empty_or_nonempty {n : ℕ | a ^ n * G₀ ∈ D.fam lam} with hemp | ⟨n₀, hn₀⟩
  · rw [hemp]
    exact Set.finite_empty
  · refine Set.Finite.subset
      ((Set.finite_Iio n₀).union (hfin.image (fun d => n₀ + d))) ?_
    intro n hn
    rcases Nat.lt_or_ge n n₀ with hlt | hge
    · exact Set.mem_union_left _ hlt
    refine Set.mem_union_right _ ⟨n - n₀, ?_, ?_⟩
    · have hsplit : a ^ n = a ^ (n - n₀) * a ^ n₀ := by
        rw [← pow_add, show n - n₀ + n₀ = n from by omega]
      have hprod : a ^ (n - n₀) = (a ^ n * G₀) * (a ^ n₀ * G₀)⁻¹ := by
        rw [mul_inv_rev, hsplit]
        simp [mul_assoc]
      show a ^ (n - n₀) ∈ D.fam lam
      rw [hprod]
      exact mul_mem hn (inv_mem hn₀)
    · show n₀ + (n - n₀) = n
      omega

end PowFam

end HullSC
end GroupApproximation
