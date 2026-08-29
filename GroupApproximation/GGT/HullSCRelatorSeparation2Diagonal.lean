import GroupApproximation.GGT.HullSCRelatorSeparation2Power

/-!
# The diagonal of the separation, and the leaf it rests on

The design excludes `x · a^i · x' = a^j` for `i ≠ j`.  The aligned case of step
(c) needs the **diagonal** `i = j`: that no short pair carries a deep power onto
itself.  This module adds it, and it also says exactly what it costs, because
the clause is not free and not always true.

Solving the equation shows why.  `x · a^i · x' = a^i` determines `x'` as
`a^{-i} x⁻¹ a^i`, so for a *fixed pair* `(x, x')` two exponents can satisfy it
only if `x` commutes with the difference of powers -- `commute_of_diagonal`.
There are two consequences, and they are the whole content:

* if no nontrivial element of the relative `eps`-ball commutes with any positive
  power of `a`, each pair allows at most one exponent, so the exponents to avoid
  are finitely many and the greedy design avoids them
  (`finite_diagonalBad`, `exists_separated_relator_exponents₂_diagonal`);
* if some nontrivial `x` in the ball does commute with `a^i`, then
  `x · a^i · x⁻¹ = a^i` outright (`diagonal_fails_of_commute`), and the clause is
  false at that exponent whatever the design does.

So the hypothesis is necessary, not decorative, and it is the leaf this rests
on:

> **(no short commuting element)** for each index `s`, no `x ≠ 1` of
> `D.relBall s eps` commutes with a positive power of `a s` --
> equivalently `E(a s) ∩ D.relBall s eps = 1`.

It is a statement about the elementary closure of a loxodromic meeting a
relative ball, which is where acylindricity acts; passing to a high power of
`a s` does **not** establish it, since `E(a^M) = E(a)`, and that is why
`GGT/HullSCRelatorSeparation2Power.lean` is not enough on its own.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u

section Diagonal

variable {G : Type u} [Group G]

/-- **Two exponents with one pair of short sides force a commutation.**

From `x · a^i · x' = a^i` the element `x'` is `a^{-i} x⁻¹ a^i`; equating the two
determinations at `i` and `i + d` makes `x'`, hence `x`, commute with `a^d`. -/
theorem commute_of_diagonal {a x x' : G} {i d : ℕ}
    (hi : x * a ^ i * x' = a ^ i)
    (hj : x * a ^ (i + d) * x' = a ^ (i + d)) : Commute x (a ^ d) := by
  have hA : x * a ^ i = a ^ i * x'⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    exact hi
  have h : a ^ i * x'⁻¹ * a ^ d * x' = a ^ i * a ^ d := by
    rw [← hA]
    rw [pow_add, ← mul_assoc] at hj
    exact hj
  rw [mul_assoc, mul_assoc] at h
  have hcancel : x'⁻¹ * (a ^ d * x') = a ^ d := mul_left_cancel h
  have h2 : a ^ d * x' = x' * a ^ d := by
    have h3 := congrArg (fun g : G => x' * g) hcancel
    simpa [mul_assoc] using h3
  have hx : x = a ^ i * x'⁻¹ * (a ^ i)⁻¹ := by
    rw [← hA, mul_inv_cancel_right]
  have hc' : Commute (a ^ d) x' := h2
  have hai : Commute (a ^ d) (a ^ i) := Commute.pow_pow_self a d i
  have hfin : Commute (a ^ d) x := by
    rw [hx]
    exact (hai.mul_right hc'.inv_right).mul_right hai.inv_right
  exact hfin.symm

/-- **At most one exponent per pair**, when `x` commutes with no power. -/
theorem diagonal_exponent_unique {a x x' : G}
    (hnc : ∀ d : ℕ, 0 < d → ¬ Commute x (a ^ d)) {i j : ℕ}
    (hi : x * a ^ i * x' = a ^ i) (hj : x * a ^ j * x' = a ^ j) : i = j := by
  by_contra hne
  rcases Nat.lt_or_ge i j with h | h
  · refine hnc (j - i) (by omega) (commute_of_diagonal hi ?_)
    rw [show i + (j - i) = j from by omega]
    exact hj
  · refine hnc (i - j) (by omega) (commute_of_diagonal hj ?_)
    rw [show j + (i - j) = i from by omega]
    exact hi

/-- **The exponents the diagonal forbids.** -/
def diagonalBad (a : G) (T : Set G) : Set ℕ :=
  {i : ℕ | ∃ x ∈ T, ∃ x' ∈ T, x ≠ 1 ∧ x * a ^ i * x' = a ^ i}

/-- **They are finitely many**, under the leaf: each pair of short sides
contributes at most one. -/
theorem finite_diagonalBad {a : G} {T : Set G} (hT : T.Finite)
    (hnc : ∀ x ∈ T, x ≠ 1 → ∀ d : ℕ, 0 < d → ¬ Commute x (a ^ d)) :
    (diagonalBad a T).Finite := by
  have hsub : diagonalBad a T ⊆
      ⋃ x ∈ T, ⋃ x' ∈ T, {i : ℕ | x ≠ 1 ∧ x * a ^ i * x' = a ^ i} := by
    rintro i ⟨x, hx, x', hx', hx1, heq⟩
    exact Set.mem_biUnion hx (Set.mem_biUnion hx' ⟨hx1, heq⟩)
  refine Set.Finite.subset ?_ hsub
  refine hT.biUnion ?_
  intro x hx
  refine hT.biUnion ?_
  intro x' hx'
  refine Set.Subsingleton.finite ?_
  rintro i ⟨hi1, hi2⟩ j ⟨-, hj2⟩
  exact diagonal_exponent_unique (hnc x hx hi1) hi2 hj2

/-- **Why the leaf is necessary.**  A nontrivial short element commuting with
`a^i` solves the diagonal at `i`, whatever exponent the design chooses. -/
theorem diagonal_fails_of_commute {a x : G} {i : ℕ} (hc : Commute x (a ^ i)) :
    x * a ^ i * x⁻¹ = a ^ i := by
  rw [hc.eq, mul_inv_cancel_right]

end Diagonal

section Design

variable {G : Type u} [Group G]

/-- **The exponent design with the diagonal excluded.**

The deep clause is enlarged rather than the construction changed: the powers of
`a s` at the forbidden exponents form a finite set of group elements, so
adjoining them to what the design already avoids gives the diagonal clause by
injectivity of the power map.  The separation clause off the diagonal and the
deep clause across indices are as in
`HullSC.exists_separated_relator_exponents₂_cross`. -/
theorem exists_separated_relator_exponents₂_diagonal {D : GGT.RelGenSet G Bool}
    (hemb : D.IsHyperbolicallyEmbedded) {a : Bool → G}
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (rho eps L : ℕ)
    (hnc : ∀ s : Bool, ∀ x ∈ D.relBall s eps, x ≠ 1 → ∀ d : ℕ, 0 < d →
      ¬ Commute x (a s ^ d)) :
    ∃ ms : List ℕ, L ≤ ms.length ∧ ms.Nodup ∧
      (∀ m ∈ ms, ∀ s t : Bool, a s ^ m ∉ D.relBall t rho ∧
        (a s ^ m)⁻¹ ∉ D.relBall t rho) ∧
      (∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ s : Bool, ∀ x ∈ D.relBall s eps,
        ∀ x' ∈ D.relBall s eps,
          x * a s ^ i * x' ≠ a s ^ j ∧ x * a s ^ i * x' ≠ (a s ^ j)⁻¹) ∧
      ∀ i ∈ ms, ∀ s : Bool, ∀ x ∈ D.relBall s eps, ∀ x' ∈ D.relBall s eps,
        x ≠ 1 → x * a s ^ i * x' ≠ a s ^ i := by
  have hbad : ∀ s : Bool,
      (((fun i : ℕ => a s ^ i) ''
        diagonalBad (a s) (D.relBall s eps))).Finite :=
    fun s => Set.Finite.image _
      (finite_diagonalBad (hemb.locallyFinite s eps) (hnc s))
  have hKfin : ((D.relBall false rho ∪ D.relBall true rho)
      ∪ ((fun i : ℕ => a false ^ i) '' diagonalBad (a false) (D.relBall false eps)
        ∪ (fun i : ℕ => a true ^ i) ''
          diagonalBad (a true) (D.relBall true eps))).Finite :=
    ((hemb.locallyFinite false rho).union
      (hemb.locallyFinite true rho)).union ((hbad false).union (hbad true))
  obtain ⟨ms, hlen, hnodup, hdeep, hsep⟩ :=
    exists_separated_exponents_family hinj hKfin
      ((hemb.locallyFinite false eps).union (hemb.locallyFinite true eps)) L
  refine ⟨ms, hlen, hnodup, ?_, ?_, ?_⟩
  · intro m hm s t
    have h := hdeep m hm s
    cases t with
    | false =>
        exact ⟨fun hc => h.1 (Set.mem_union_left _ (Set.mem_union_left _ hc)),
          fun hc => h.2 (Set.mem_union_left _ (Set.mem_union_left _ hc))⟩
    | true =>
        exact ⟨fun hc => h.1 (Set.mem_union_left _ (Set.mem_union_right _ hc)),
          fun hc => h.2 (Set.mem_union_left _ (Set.mem_union_right _ hc))⟩
  · intro i hi j hj hij s x hx x' hx'
    have hxT : x ∈ D.relBall false eps ∪ D.relBall true eps := by
      cases s with
      | false => exact Set.mem_union_left _ hx
      | true => exact Set.mem_union_right _ hx
    have hx'T : x' ∈ D.relBall false eps ∪ D.relBall true eps := by
      cases s with
      | false => exact Set.mem_union_left _ hx'
      | true => exact Set.mem_union_right _ hx'
    exact hsep i hi j hj hij s x hxT x' hx'T
  · intro i hi s x hx x' hx' hx1 heq
    have hmem : a s ^ i ∈ (fun n : ℕ => a s ^ n) ''
        diagonalBad (a s) (D.relBall s eps) :=
      ⟨i, ⟨x, hx, x', hx', hx1, heq⟩, rfl⟩
    refine (hdeep i hi s).1 ?_
    refine Set.mem_union_right _ ?_
    cases s with
    | false => exact Set.mem_union_left _ hmem
    | true => exact Set.mem_union_right _ hmem

end Design

end HullSC
end GroupApproximation
