import GroupApproximation.GGT.OsinTheorem54SepFourGonCorner

/-!
# The rigidity clause reduces to the isolated-component bound

A consumer's `hgeo` says a short conjugation carrying one deep peripheral power
onto another puts both conjugators in `H_s`:

  `x * a s ^ i * x' = a s ^ j`, with `x`, `x'` short over the base and
  `a s ^ i`, `a s ^ j` outside `D.relBall s rho`, forces `x, x' ∈ D.fam s`.

That is not an independent geometric assumption.  The equation IS a closed
quadrilateral --- `x · a^i · x' · (a^j)⁻¹` --- with the two deep powers as its
long sides and the two short conjugators as its short ones, which is exactly the
configuration `exists_other_component_of_deep` is about.

## The argument

Each deep power is a single letter `comp s (a s ^ ·)`, hence a one-letter
component of the quadrilateral, because `a s ∈ D.fam s` makes its powers
peripheral.  The `q`-side component is deep by hypothesis, so it is connected to
another component; the two short sides are spelled by base letters and carry
none (`not_isCompStart_fourGon_first`, `_third`), so the match lands on the
opposite side with a connector `h ∈ D.fam s`.

The matched vertex of the opposite side is either `1` or `a s ^ j`, both in
`D.fam s`, and the `q`-vertex is `1`; so the naming equation reads
`listVal px * h = 1` or `= a s ^ j`, and either way `listVal px ∈ D.fam s`
because `D.fam s` is a subgroup.  `x'` then falls out of the consumer's own
equation.

This is the one place in the chain where the start-to-start connector's
unboundedness costs nothing: the conclusion is a MEMBERSHIP, not a bound.

Conditional on `IsolatedComponentBound` as a leading binder and on nothing else.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u

variable {G : Type u} [Group G]

omit [Group G] in
/-- A single peripheral letter is a one-letter component. -/
theorem isComp_singleton (s : Bool) (g : G) :
    IsComp s [RelLetter.comp s g] 0 1 := by
  refine ⟨by omega, by simp, ?_, ?_, ?_⟩
  · intro t ht1 ht2 ht
    have ht0 : t = 0 := by omega
    subst ht0
    exact rfl
  · intro t ht
    omega
  · intro hk
    simp at hk

/-- The far vertex of a one-letter word is its letter's value. -/
theorem vertex_singleton_one (s : Bool) (g : G) :
    vertex (1 : G) [RelLetter.comp s g] 1 = g := by
  rw [vertex_cons_succ, vertex_zero, one_mul]
  rfl

/-- **The rigidity clause, over the bound.**

`x` is `listVal px` and `x'` is `listVal rx`; the caller supplies the two short
words, which its `wordNorm D.base ≤ eps` hypothesis provides, and the polygon
hypothesis for the quadrilateral they form. -/
theorem mem_fam_of_conj_of_deep (D : RelGenSet G Bool)
    (hbound : IsolatedComponentBound (IsQuasiGeodesicPolygon D) D)
    {a : Bool → G} (hmem : ∀ t : Bool, a t ∈ D.fam t) (s : Bool)
    {mu b : ℝ} (hmu : 1 ≤ mu) (hb : 0 ≤ b) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n rho i j : ℕ) (px rx : List (RelLetter G Bool)),
      (∀ c ∈ px, ∃ y : G, c = RelLetter.base y) →
      (∀ c ∈ rx, ∃ y : G, c = RelLetter.base y) →
      0 < rx.length →
      RelLetter.listVal px * a s ^ i * RelLetter.listVal rx = a s ^ j →
      IsQuasiGeodesicPolygon D mu b n 1
        (px ++ [RelLetter.comp s (a s ^ i)] ++ rx ++
          revWord [RelLetter.comp s (a s ^ j)]) →
      C * n ≤ rho →
      a s ^ i ∉ D.relBall s rho →
        RelLetter.listVal px ∈ D.fam s ∧ RelLetter.listVal rx ∈ D.fam s := by
  obtain ⟨C, hCpos, hC⟩ := exists_other_component_of_deep D hbound s hmu hb
  refine ⟨C, hCpos, ?_⟩
  intro n rho i j px rx hpx hrx hrxne heq hpoly hrho hdeep
  have hai : a s ^ i ∈ D.fam s := pow_mem (hmem s) i
  have haj : a s ^ j ∈ D.fam s := pow_mem (hmem s) j
  have hvq : RelLetter.listVal [RelLetter.comp s (a s ^ i)] = a s ^ i := by
    simp [listVal_singleton, RelLetter.val]
  have hvs : RelLetter.listVal [RelLetter.comp s (a s ^ j)] = a s ^ j := by
    simp [listVal_singleton, RelLetter.val]
  have hclose : RelLetter.listVal [RelLetter.comp s (a s ^ j)]
      = RelLetter.listVal px * RelLetter.listVal [RelLetter.comp s (a s ^ i)]
        * RelLetter.listVal rx := by
    rw [hvq, hvs]
    exact heq.symm
  have hspan : (vertex (1 : G) [RelLetter.comp s (a s ^ i)] 0)⁻¹ *
      vertex (1 : G) [RelLetter.comp s (a s ^ i)] 1 ∉ D.relBall s rho := by
    rw [vertex_zero, vertex_singleton_one, inv_one, one_mul]
    exact hdeep
  have hpx' : RelLetter.listVal px ∈ D.fam s := by
    rcases hC n rho px [RelLetter.comp s (a s ^ i)] rx
        [RelLetter.comp s (a s ^ j)] hclose hpx hrx hpoly 0 1
        (isComp_singleton s (a s ^ i)) (Or.inr hrxne) hrho hspan with
      ⟨i', hi', hne, hstart', -⟩ | ⟨j', hjle, -, h, hh, hconn⟩
    · exfalso
      have hi'1 : i' = 1 := by
        simp only [List.length_singleton] at hi'
        omega
      subst hi'1
      exact not_isCompStart_fourGon_third px [RelLetter.comp s (a s ^ i)] rx
        [RelLetter.comp s (a s ^ j)] s hrx hrxne (by simpa using hstart')
    · rw [vertex_zero, mul_one] at hconn
      rcases Nat.lt_or_ge j' 1 with hj0 | hj1
      · have : j' = 0 := by omega
        subst this
        rw [vertex_zero] at hconn
        have : RelLetter.listVal px = h⁻¹ := mul_eq_one_iff_eq_inv.mp hconn
        rw [this]
        exact inv_mem hh
      · have hj' : j' = 1 := by
          simp only [List.length_singleton] at hjle
          omega
        subst hj'
        rw [vertex_singleton_one] at hconn
        have : RelLetter.listVal px = a s ^ j * h⁻¹ := by
          rw [← hconn]; group
        rw [this]
        exact mul_mem haj (inv_mem hh)
  refine ⟨hpx', ?_⟩
  have : RelLetter.listVal rx
      = (a s ^ i)⁻¹ * (RelLetter.listVal px)⁻¹ * a s ^ j := by
    rw [← heq]; group
  rw [this]
  exact mul_mem (mul_mem (inv_mem hai) (inv_mem hpx')) haj

end OsinComponents
end GGT
end GroupApproximation
