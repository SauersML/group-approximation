import GroupApproximation.GGT.OsinTheorem54SepRigidityReduction

/-!
# The rigidity clause over the six-side form of the bound

`GGT/OsinTheorem54SepFourGonSide.lean` carries Osin's Lemma 4.2 in the form
`DGOIsolatedComponentCut` consumes and fp-geometry proves: the bound asserted
only for `n ≤ 6`.  This module states the rigidity clause over it.

The unrestricted variants that stood here and in
`GGT/OsinTheorem54SepRigidityReduction.lean` are gone.  They carried
`IsolatedComponentBound`, which asserts the bound at EVERY number of sides and
is nowhere proved; once their only consumer switched to the six-side form there
was no reason to keep a strictly stronger hypothesis in the tree, where the next
caller might reach for it by accident.  Nothing is lost in the other direction:
the unrestricted hypothesis gives the six-side one by ignoring the restriction,
which is a one-line adapter if a caller ever holds it.

What stays here is the reduction itself, and the two lemmas it runs on ---
`isComp_singleton` and `vertex_singleton_one` --- are next door.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u

variable {G : Type u} [Group G]

/-- **The rigidity clause, over the bound AT one pair of constants.**

The body lives here; `mem_fam_of_conj_of_deep_six` and
`mem_fam_of_conj_of_deep_one` differ from it only in which spelling of the
isolated-component bound they are handed.

A short conjugation carrying one deep peripheral power onto another puts both
conjugators in `H_s`.  The equation IS a closed quadrilateral --- `x · a^i · x'
· (a^j)⁻¹` --- with the two deep powers as its long sides and the two short
conjugators as its short ones, and each power is a single peripheral letter,
hence a one-letter component; the deep side is therefore matched to another
component of the quadrilateral, and the short sides carry none, so the match
lands on the opposite side with a connector in `H_s`.

The matched vertex of the opposite side is `1` or `a s ^ j`, both in `H_s`, and
the `q`-vertex is `1`; so the naming equation puts `listVal px` in `H_s`, and
`x'` falls out of the caller's own equation.  This is the one place where the
start-to-start connector's unboundedness costs nothing: the conclusion is a
MEMBERSHIP, not a bound. -/
theorem mem_fam_of_conj_of_deep_of_bound (D : RelGenSet G Bool)
    {a : Bool → G} (hmem : ∀ t : Bool, a t ∈ D.fam t) (s : Bool) (mu b : ℝ)
    (hbnd : ∃ C : ℕ, 0 < C ∧
      ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Bool)),
        IsQuasiGeodesicPolygon D mu b n v u →
        ∀ (nu : Bool) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
          (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n)) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n rho i j : ℕ), n ≤ 6 →
      ∀ px rx : List (RelLetter G Bool),
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
  obtain ⟨C, hCpos, hC⟩ := exists_other_component_of_deep_of_bound D s mu b hbnd
  refine ⟨C, hCpos, ?_⟩
  intro n rho i j hn px rx hpx hrx hrxne heq hpoly hrho hdeep
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
    rcases hC n rho hn px [RelLetter.comp s (a s ^ i)] rx
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
      · have hj0' : j' = 0 := by omega
        subst hj0'
        rw [vertex_zero] at hconn
        have hpxh : RelLetter.listVal px = h⁻¹ := mul_eq_one_iff_eq_inv.mp hconn
        rw [hpxh]
        exact inv_mem hh
      · have hj' : j' = 1 := by
          simp only [List.length_singleton] at hjle
          omega
        subst hj'
        rw [vertex_singleton_one] at hconn
        have hpxh : RelLetter.listVal px = a s ^ j * h⁻¹ := by
          rw [← hconn]; group
        rw [hpxh]
        exact mul_mem haj (inv_mem hh)
  refine ⟨hpx', ?_⟩
  have hrxval : RelLetter.listVal rx
      = (a s ^ i)⁻¹ * (RelLetter.listVal px)⁻¹ * a s ^ j := by
    rw [← heq]; group
  rw [hrxval]
  exact mul_mem (mul_mem (inv_mem hai) (inv_mem hpx')) haj

/-- **The same, over the bound at every pair of constants.** -/
theorem mem_fam_of_conj_of_deep_six (D : RelGenSet G Bool)
    (hbound : ∀ mu b : ℝ, 1 ≤ mu → 0 ≤ b → ∃ C : ℕ, 0 < C ∧
      ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Bool)),
        IsQuasiGeodesicPolygon D mu b n v u →
        ∀ (nu : Bool) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
          (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    {a : Bool → G} (hmem : ∀ t : Bool, a t ∈ D.fam t) (s : Bool)
    {mu b : ℝ} (hmu : 1 ≤ mu) (hb : 0 ≤ b) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n rho i j : ℕ), n ≤ 6 →
      ∀ px rx : List (RelLetter G Bool),
      (∀ c ∈ px, ∃ y : G, c = RelLetter.base y) →
      (∀ c ∈ rx, ∃ y : G, c = RelLetter.base y) →
      0 < rx.length →
      RelLetter.listVal px * a s ^ i * RelLetter.listVal rx = a s ^ j →
      IsQuasiGeodesicPolygon D mu b n 1
        (px ++ [RelLetter.comp s (a s ^ i)] ++ rx ++
          revWord [RelLetter.comp s (a s ^ j)]) →
      C * n ≤ rho →
      a s ^ i ∉ D.relBall s rho →
        RelLetter.listVal px ∈ D.fam s ∧ RelLetter.listVal rx ∈ D.fam s :=
  mem_fam_of_conj_of_deep_of_bound D hmem s mu b (hbound mu b hmu hb)

/-- **The same, over the bound at `μ = 1`**, which is what
`OsinTheorem54SepSixBound.sixBound_one_of_fourPointHyperbolic` proves. -/
theorem mem_fam_of_conj_of_deep_one (D : RelGenSet G Bool)
    (hbound : ∀ b : ℝ, 0 ≤ b → ∃ C : ℕ, 0 < C ∧
      ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Bool)),
        IsQuasiGeodesicPolygon D 1 b n v u →
        ∀ (nu : Bool) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
          (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    {a : Bool → G} (hmem : ∀ t : Bool, a t ∈ D.fam t) (s : Bool) (b : ℝ)
    (hb : 0 ≤ b) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n rho i j : ℕ), n ≤ 6 →
      ∀ px rx : List (RelLetter G Bool),
      (∀ c ∈ px, ∃ y : G, c = RelLetter.base y) →
      (∀ c ∈ rx, ∃ y : G, c = RelLetter.base y) →
      0 < rx.length →
      RelLetter.listVal px * a s ^ i * RelLetter.listVal rx = a s ^ j →
      IsQuasiGeodesicPolygon D 1 b n 1
        (px ++ [RelLetter.comp s (a s ^ i)] ++ rx ++
          revWord [RelLetter.comp s (a s ^ j)]) →
      C * n ≤ rho →
      a s ^ i ∉ D.relBall s rho →
        RelLetter.listVal px ∈ D.fam s ∧ RelLetter.listVal rx ∈ D.fam s :=
  mem_fam_of_conj_of_deep_of_bound D hmem s 1 b (hbound b hb)

end OsinComponents
end GGT
end GroupApproximation
