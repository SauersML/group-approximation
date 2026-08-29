import GroupApproximation.GGT.OsinTheorem54SepRigidityReduction

/-!
# The deep-component lemmas over the six-side form of the bound

`GGT/OsinTheorem54SepFourGonSide.lean` and
`GGT/OsinTheorem54SepRigidityReduction.lean` carry Osin's Lemma 4.2 as
`IsolatedComponentBound`, which asserts the bound at EVERY number of sides.
`GGT/DGOIsolatedComponentCut.lean` consumes a weaker hypothesis: the same bound
restricted to `n ≤ 6`, which is all its cut argument needs and --- this is the
point --- all that is proved anywhere in this repository.

This module restates the two deep-component lemmas over that weaker hypothesis,
so that a consumer's chain rests on the six-side form alone.  Nothing else
changes: the conclusions gain the restriction `n ≤ 6`, which every caller
already satisfies, the quadrilateral being a four-gon.

`six_form_of_isolatedComponentBound` is the trivial weakening in the other
direction, for a caller that still holds the unrestricted hypothesis: it turns
that into the six-side form in one application, so the older lemmas and these
can be fed from the same place while the switch is made.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G]

section General

variable {Λ : Type w}

/-- **The unrestricted bound gives the six-side form.**  The one direction that
holds: a hypothesis about all `n` covers `n ≤ 6`. -/
theorem six_form_of_isolatedComponentBound (D : RelGenSet G Λ)
    (hbound : IsolatedComponentBound (IsQuasiGeodesicPolygon D) D) :
    ∀ mu b : ℝ, 1 ≤ mu → 0 ≤ b → ∃ C : ℕ, 0 < C ∧
      ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
        IsQuasiGeodesicPolygon D mu b n v u →
        ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
          (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n) := by
  intro mu b hmu hb
  obtain ⟨C, hCpos, hC⟩ := hbound mu b hmu hb
  exact ⟨C, hCpos, fun n _ v u hpoly nu i k hcomp hiso =>
    hC n v u hpoly nu i k hcomp hiso⟩

/-- **A deep component of one long side is connected to another component of
the quadrilateral**, over the six-side form of the bound.

Word for word `exists_other_component_of_deep`, with the leading binder
weakened and the resulting restriction `n ≤ 6` carried into the conclusion. -/
theorem exists_other_component_of_deep_six (D : RelGenSet G Λ)
    (hbound : ∀ mu b : ℝ, 1 ≤ mu → 0 ≤ b → ∃ C : ℕ, 0 < C ∧
      ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
        IsQuasiGeodesicPolygon D mu b n v u →
        ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
          (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (lam : Λ) {mu b : ℝ} (hmu : 1 ≤ mu) (hb : 0 ≤ b) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n rho : ℕ), n ≤ 6 →
      ∀ p q r s : List (RelLetter G Λ),
      RelLetter.listVal s
          = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r →
      (∀ a ∈ p, ∃ x : G, a = RelLetter.base x) →
      (∀ a ∈ r, ∃ x : G, a = RelLetter.base x) →
      IsQuasiGeodesicPolygon D mu b n 1 (p ++ q ++ r ++ revWord s) →
      ∀ i k : ℕ, IsComp lam q i k → (k < q.length ∨ 0 < r.length) →
        C * n ≤ rho →
        (vertex (1 : G) q i)⁻¹ * vertex (1 : G) q k ∉ D.relBall lam rho →
          (∃ i' : ℕ, i' ≤ q.length ∧ i' ≠ i ∧
              IsCompStart lam (p ++ q ++ r ++ revWord s) (p.length + i') ∧
              ∃ h : G, h ∈ D.fam lam ∧
                vertex (1 : G) q i * h = vertex (1 : G) q i')
            ∨ (∃ j : ℕ, j ≤ s.length ∧
              IsCompStart lam (p ++ q ++ r ++ revWord s)
                (p.length + q.length + r.length + (s.length - j)) ∧
              ∃ h : G, h ∈ D.fam lam ∧
                RelLetter.listVal p * vertex (1 : G) q i * h
                  = vertex (1 : G) s j) := by
  obtain ⟨C, hCpos, hC⟩ := hbound mu b hmu hb
  refine ⟨C, hCpos, ?_⟩
  intro n rho hn p q r s hclose hp hr hpoly i k hcomp hk hrho hdeep
  have hbridge := isComp_fourGon_of_isComp_side p q r s lam hp hr hcomp hk
  have hiq : i ≤ q.length := by
    obtain ⟨hik, hkl, -, -, -⟩ := hcomp
    omega
  have hkl : k ≤ q.length := by
    obtain ⟨-, hkl, -, -, -⟩ := hcomp
    exact hkl
  refine exists_other_component_of_isComp_side D lam p q r s hclose hp hr
    hcomp hk ?_
  intro hiso
  have hspan := hC n hn 1 (p ++ q ++ r ++ revWord s) hpoly lam (p.length + i)
    (p.length + k) hbridge hiso
  rw [span_fourGon_side p q r s hiq hkl] at hspan
  exact hdeep (relBall_mono_radius D lam hrho hspan)

end General

/-- **The rigidity clause, over the six-side form of the bound.**

Word for word `mem_fam_of_conj_of_deep`, with the leading binder weakened.  The
restriction `n ≤ 6` is no restriction on the caller: the polygon it supplies is
the quadrilateral `x · a^i · x' · (a^j)⁻¹`. -/
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
        RelLetter.listVal px ∈ D.fam s ∧ RelLetter.listVal rx ∈ D.fam s := by
  obtain ⟨C, hCpos, hC⟩ := exists_other_component_of_deep_six D hbound s hmu hb
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

end OsinComponents
end GGT
end GroupApproximation
