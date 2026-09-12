import GroupApproximation.GGT.HullSCRelatorSeparationBall

/-!
# Choosing the exponents of Hull's relator so that its blocks cannot be shifted

M. Hull, *Small cancellation in acylindrically hyperbolic groups*, Groups
Geom. Dyn. 10 (2016) 1077-1119, §6, after Olshanskii.

`HullSC.RelatorSeparation` leaves the exponents `m₁, …, m_k` of
`v = p · h^{m₁} ⋯ h^{m_k}` free, subject only to depth, and that freedom is the
design space.  `HullSC.exists_deep_relator_exponents` uses it for depth alone.
This module uses it for the property Olshanskii's argument actually consumes:

> no two distinct blocks of the relator are carried onto one another by short
> elements on either side — for `i ≠ j` in `ms` there are no `x, x'` in the
> relative ball of radius `eps` with `x · h^{m_i} · x' = h^{m_j}`, and none with
> `x · h^{m_i} · x' = (h^{m_j})⁻¹` either.

The second, mirrored clause is what a match between the relator and its formal
inverse consumes, and it is deliberately stated for distinct exponents only:
at `i = j` the mirrored match is the genuine translation the exclusion clause
carves out.

That this can be arranged is not a hypothesis: it is `exists_separated_exponents`
and it is proved.  The mechanism is that `GGT.RelGenSet.relBall` is *finite*
(`GGT.RelGenSet.IsHyperbolicallyEmbedded.locallyFinite`), so for a block already
chosen the set of elements a short two-sided translate can reach it from is
finite, while the powers of a loxodromic element are all distinct
(`HullSC.injective_pow_of_not_isOfFinOrder`).  So each new exponent has only
finitely many forbidden values and can always be taken beyond them.  This is the
same counting that makes depth free, run against a larger finite set.

The exponents are chosen greedily, one at a time against the list already built,
which is why `exists_pow_separated` is an induction over the list rather than a
single application of a finiteness lemma: the forbidden set grows with the list,
and folding it into the avoided set `K` at each step keeps the count finite
without ever forming a union indexed by the list.

What this buys is in `GGT/HullSCRelatorSeparationBlock.lean`: with these
exponents, an `eps`-match between two blocks of the relator forces the two
exponents to be equal, so the blocks of a long matched prefix are aligned one to
one.  That is the combinatorial half of Olshanskii's separation.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-- A member of a list of naturals is at most the sum of the list.  This is what
makes each new exponent larger than all the old ones, hence the list without
repetitions. -/
theorem le_sum_of_mem_nat {ms : List ℕ} {m : ℕ} (h : m ∈ ms) : m ≤ ms.sum := by
  induction ms with
  | nil => simp at h
  | cons b t ih =>
      rw [List.sum_cons]
      rcases List.mem_cons.mp h with rfl | h'
      · omega
      · have hle := ih h'
        omega

section Gaps

variable {G : Type u} [Group G]

/-- **One more deep power, separated from every power already chosen.**

Given a list `js` of exponents already fixed and a finite set `K` to escape,
there is an arbitrarily large `m` with `h^m` and its inverse outside `K` and
with no short two-sided translate carrying `h^m` to any `h^j`, `j ∈ js`, or the
other way round.

The induction is over `js`, and it works by *enlarging the avoided set*: at the
head `j₀` the two forbidden families are the images of `T × T` under
`(x,x') ↦ x⁻¹ h^{j₀} x'⁻¹` and `(x,x') ↦ x h^{j₀} x'`, both finite because `T`
is, and both are folded into `K` before the tail is treated.  So the finiteness
count is done once per exponent and never over a union indexed by the whole
list. -/
theorem exists_pow_separated {a : G}
    (hinj : Function.Injective (fun n : ℕ => a ^ n)) {T : Set G} (hT : T.Finite) :
    ∀ (js : List ℕ) (K : Set G), K.Finite → ∀ n₀ : ℕ,
      ∃ m : ℕ, n₀ ≤ m ∧ a ^ m ∉ K ∧ (a ^ m)⁻¹ ∉ K ∧
        ∀ j ∈ js, ∀ x ∈ T, ∀ x' ∈ T,
          x * a ^ m * x' ≠ a ^ j ∧ x * a ^ j * x' ≠ a ^ m ∧
            x * a ^ m * x' ≠ (a ^ j)⁻¹ ∧ x * a ^ j * x' ≠ (a ^ m)⁻¹ := by
  intro js
  induction js with
  | nil =>
      intro K hK n₀
      obtain ⟨m, hm, h1, h2⟩ := exists_deep_pow hinj hK n₀
      refine ⟨m, hm, h1, h2, ?_⟩
      intro j hj
      simp at hj
  | cons j₀ t ih =>
      intro K hK n₀
      have hK1 : (Set.image2 (fun x x' : G => x⁻¹ * a ^ j₀ * x'⁻¹) T T).Finite :=
        Set.Finite.image2 _ hT hT
      have hK2 : (Set.image2 (fun x x' : G => x * a ^ j₀ * x') T T).Finite :=
        Set.Finite.image2 _ hT hT
      have hK3 : (Set.image2 (fun x x' : G => x⁻¹ * (a ^ j₀)⁻¹ * x'⁻¹) T T).Finite :=
        Set.Finite.image2 _ hT hT
      obtain ⟨m, hm, h1, h2, hrest⟩ :=
        ih (K ∪ Set.image2 (fun x x' : G => x⁻¹ * a ^ j₀ * x'⁻¹) T T
              ∪ Set.image2 (fun x x' : G => x * a ^ j₀ * x') T T
              ∪ Set.image2 (fun x x' : G => x⁻¹ * (a ^ j₀)⁻¹ * x'⁻¹) T T)
          (((hK.union hK1).union hK2).union hK3) n₀
      refine ⟨m, hm, ?_, ?_, ?_⟩
      · exact fun hc => h1 (Set.mem_union_left _ (Set.mem_union_left _
          (Set.mem_union_left _ hc)))
      · exact fun hc => h2 (Set.mem_union_left _ (Set.mem_union_left _
          (Set.mem_union_left _ hc)))
      · intro j hj x hx x' hx'
        rcases List.mem_cons.mp hj with hje | hj'
        · rw [hje]
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro hc
            refine h1 (Set.mem_union_left _ (Set.mem_union_left _
              (Set.mem_union_right _ (Set.mem_image2.mpr ⟨x, hx, x', hx', ?_⟩))))
            show x⁻¹ * a ^ j₀ * x'⁻¹ = a ^ m
            rw [← hc, mul_assoc x (a ^ m) x', inv_mul_cancel_left,
              mul_inv_cancel_right]
          · intro hc
            exact h1 (Set.mem_union_left _ (Set.mem_union_right _
              (Set.mem_image2.mpr ⟨x, hx, x', hx', hc⟩)))
          · intro hc
            refine h1 (Set.mem_union_right _
              (Set.mem_image2.mpr ⟨x, hx, x', hx', ?_⟩))
            show x⁻¹ * (a ^ j₀)⁻¹ * x'⁻¹ = a ^ m
            rw [← hc, mul_assoc x (a ^ m) x', inv_mul_cancel_left,
              mul_inv_cancel_right]
          · intro hc
            exact h2 (Set.mem_union_left _ (Set.mem_union_right _
              (Set.mem_image2.mpr ⟨x, hx, x', hx', hc⟩)))
        · exact hrest j hj' x hx x' hx'

/-- **Arbitrarily long lists of deep, pairwise separated exponents.**

`ms` is as long as asked, has no repeated exponent, every `h^m` and its inverse
escape `K`, and no two distinct exponents of the list are carried onto one
another -- or onto one another's *inverse* -- by elements of `T` on either side.
Every clause is free, at every length: the exponents are added one at a time by
`exists_pow_separated`, each beyond the sum of those already chosen, which is
what keeps the list without repetitions.

The mirrored clause is what a match between the relator and its formal inverse
consumes, and it is stated for *distinct* exponents only.  That restriction is
forced twice over: at `i = j` the mirrored match is the genuine global
translation Olshanskii's exclusion carves out, so forbidding it would be wrong;
and at `i = j` the exponent occurs on both sides of the equation, so the
forbidden set is not a fixed finite set and the greedy count does not reach
it. -/
theorem exists_separated_exponents {a : G}
    (hinj : Function.Injective (fun n : ℕ => a ^ n)) {K : Set G} (hK : K.Finite)
    {T : Set G} (hT : T.Finite) (L : ℕ) :
    ∃ ms : List ℕ, L ≤ ms.length ∧ ms.Nodup ∧
      (∀ m ∈ ms, a ^ m ∉ K ∧ (a ^ m)⁻¹ ∉ K) ∧
      ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ x ∈ T, ∀ x' ∈ T,
        x * a ^ i * x' ≠ a ^ j ∧ x * a ^ i * x' ≠ (a ^ j)⁻¹ := by
  induction L with
  | zero =>
      refine ⟨[], Nat.zero_le _, List.nodup_nil, ?_, ?_⟩
      · intro m hm
        simp at hm
      · intro i hi
        simp at hi
  | succ L ih =>
      obtain ⟨ms, hlen, hnodup, hdeep, hsep⟩ := ih
      obtain ⟨m, hm, h1, h2, hnew⟩ :=
        exists_pow_separated hinj hT ms K hK (ms.sum + 1)
      have hnotmem : m ∉ ms := by
        intro hmem
        have hle : m ≤ ms.sum := le_sum_of_mem_nat hmem
        omega
      refine ⟨m :: ms, ?_, List.nodup_cons.mpr ⟨hnotmem, hnodup⟩, ?_, ?_⟩
      · rw [List.length_cons]
        omega
      · intro i hi
        rcases List.mem_cons.mp hi with rfl | hi'
        · exact ⟨h1, h2⟩
        · exact hdeep i hi'
      · intro i hi j hj hij x hx x' hx'
        rcases List.mem_cons.mp hi with rfl | hi'
        · rcases List.mem_cons.mp hj with rfl | hj'
          · exact absurd rfl hij
          · exact ⟨(hnew j hj' x hx x' hx').1,
              (hnew j hj' x hx x' hx').2.2.1⟩
        · rcases List.mem_cons.mp hj with rfl | hj'
          · exact ⟨(hnew i hi' x hx x' hx').2.1,
              (hnew i hi' x hx x' hx').2.2.2⟩
          · exact hsep i hi' j hj' hij x hx x' hx'

end Gaps

/-! ## The design, for Hull's relator -/

/-- **Hull's relator can be given deep, pairwise separated exponents, at every
length.**

This is `HullSC.exists_deep_relator_exponents` with the separation clause added,
and it costs nothing beyond it: the relative ball of radius `eps` is finite for
the same reason the ball of radius `rho` is, namely that `E.H` is
hyperbolically embedded, and `E.lox` has infinite order because it is
loxodromic.

So the estimate is free to fix the exponents by this recipe, and
`GGT/HullSCRelatorSeparationBlock.lean` reads the separation clause off it. -/
theorem exists_separated_relator_exponents {G : Type u} [Group G]
    {A : HullGeneratingSet G} {N : Subgroup G} (E : HypEmbeddedCore A N)
    (rho eps L : ℕ) :
    ∃ ms : List ℕ, L ≤ ms.length ∧ ms.Nodup ∧
      (∀ m ∈ ms, E.lox ^ m ∉ E.rel.relBall () rho ∧
        (E.lox ^ m)⁻¹ ∉ E.rel.relBall () rho) ∧
      ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ x ∈ E.rel.relBall () eps,
        ∀ x' ∈ E.rel.relBall () eps,
          x * E.lox ^ i * x' ≠ E.lox ^ j ∧
            x * E.lox ^ i * x' ≠ (E.lox ^ j)⁻¹ :=
  exists_separated_exponents
    (injective_pow_of_not_isOfFinOrder
      (not_isOfFinOrder_of_isLoxodromic E.lox_isLoxodromic))
    (E.embedded.locallyFinite () rho) (E.embedded.locallyFinite () eps) L

end HullSC
end GroupApproximation
