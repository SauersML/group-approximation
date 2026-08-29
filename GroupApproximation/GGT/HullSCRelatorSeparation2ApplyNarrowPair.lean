import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyMatch
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyNarrow
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyNarrowGap

/-!
# The two entry points, with no bound carried

Both sides of the isolated-component bound now stand on four-point
hyperbolicity of the RELATIVE Cayley graph `Γ(G, X ⊔ ℋ)` --- the object
hyperbolic embeddedness is defined against, not `Γ(G, X)`.  These are the two
entry points in that shape, so that the wrapper above them names `hδ` and
nothing else geometric.

* `exists_deep_match_hyp` --- the match side, through
  `GGT.OsinComponents.exists_other_component_of_deep_six_hyp`.  The constant the
  tower supplies does not depend on the index, so the maximum over `Bool` is a
  formality; it is kept only so that this and the `hbound` version have the same
  shape.
* `exists_eps_matchedPair_hyp` --- the gap side, through
  `GGT.OsinComponents.two_block_conj_named_hyp`, with the polygon's two
  configuration clauses discharged from the two same-side exclusions on the way
  past.

Both fix `mu = 1` and `b` natural, which is what the block-count route gives and
what the tower proves; the multiplicative case is not reachable and is not
wanted.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u

section Entry

variable {G : Type u} [Group G]

/-- **The match side, with four-point hyperbolicity in place of the bound.** -/
theorem exists_deep_match_hyp (D : RelGenSet G Bool)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (bn : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ∃ C : ℕ, 0 < C ∧
      ∀ (lam : Bool) (rho : ℕ) (p q r s : List (RelLetter G Bool)) (i : ℕ),
        C * 4 ≤ rho →
        RelLetter.listVal s = RelLetter.listVal p * RelLetter.listVal q
            * RelLetter.listVal r →
        (∀ x ∈ p, ∃ g : G, x = RelLetter.base g) →
        (∀ x ∈ r, ∃ g : G, x = RelLetter.base g) →
        0 < r.length →
        IsQuasiGeodesicPolygon D 1 (bn : ℝ) 4 1 (p ++ q ++ r ++ revWord s) →
        IsComp lam q i (i + 1) →
        (vertex (1 : G) q i)⁻¹ * vertex (1 : G) q (i + 1)
          ∉ D.relBall lam rho →
        (∀ i' : ℕ, i' ≤ q.length → i' ≠ i →
          (vertex (1 : G) q i)⁻¹ * vertex (1 : G) q i' ∉ D.fam lam) →
        ∃ j : ℕ, 0 < j ∧ j ≤ s.length ∧
          (∃ x : G, s[j - 1]? = some (RelLetter.comp lam x)) ∧
          ∃ h : G, h ∈ D.fam lam ∧
            RelLetter.listVal p * vertex (1 : G) q i * h
              = vertex (1 : G) s j := by
  obtain ⟨C₀, h₀, hC₀⟩ :=
    exists_other_component_of_deep_six_hyp D false hsymm bn hδ
  obtain ⟨C₁, h₁, hC₁⟩ :=
    exists_other_component_of_deep_six_hyp D true hsymm bn hδ
  refine ⟨max C₀ C₁, lt_of_lt_of_le h₀ (Nat.le_max_left C₀ C₁), ?_⟩
  intro lam rho p q r s i hrho hclose hp hr hr0 hpoly hcomp hdeep hqside
  have hrho₀ : C₀ * 4 ≤ rho :=
    le_trans (Nat.mul_le_mul (Nat.le_max_left C₀ C₁) (le_refl 4)) hrho
  have hrho₁ : C₁ * 4 ≤ rho :=
    le_trans (Nat.mul_le_mul (Nat.le_max_right C₀ C₁) (le_refl 4)) hrho
  have hdisj : (∃ i' : ℕ, i' ≤ q.length ∧ i' ≠ i ∧
        IsCompStart lam (p ++ q ++ r ++ revWord s) (p.length + i') ∧
        ∃ h : G, h ∈ D.fam lam ∧
          vertex (1 : G) q i * h = vertex (1 : G) q i')
      ∨ (∃ j : ℕ, j ≤ s.length ∧
        IsCompStart lam (p ++ q ++ r ++ revWord s)
          (p.length + q.length + r.length + (s.length - j)) ∧
        ∃ h : G, h ∈ D.fam lam ∧
          RelLetter.listVal p * vertex (1 : G) q i * h
            = vertex (1 : G) s j) := by
    cases lam with
    | false =>
        exact hC₀ 4 rho (by omega) p q r s hclose hp hr hpoly i (i + 1) hcomp
          (Or.inr hr0) hrho₀ hdeep
    | true =>
        exact hC₁ 4 rho (by omega) p q r s hclose hp hr hpoly i (i + 1) hcomp
          (Or.inr hr0) hrho₁ hdeep
  obtain ⟨j, hj0, hj, hstart, hconn⟩ :=
    cross_of_notSameSide D lam p q r s hqside hdisj
  exact ⟨j, hj0, hj,
    exists_comp_of_isCompStart_rev p q r s lam hj0 hj hstart, hconn⟩

/-- **The gap side, with four-point hyperbolicity in place of the bound.** -/
theorem exists_eps_matchedPair_hyp (D : RelGenSet G Bool)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (bn : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ∃ eps : ℕ, 0 < eps ∧
      ∀ (lam : Bool) (p q r s : List (RelLetter G Bool)) (i j : ℕ),
        RelLetter.listVal s = RelLetter.listVal p * RelLetter.listVal q
            * RelLetter.listVal r →
        (∀ a ∈ p ++ q ++ r ++ revWord s, D.IsLetter a) →
        (∀ a ∈ p, ∃ x : G, a = RelLetter.base x) →
        (∀ a ∈ r, ∃ x : G, a = RelLetter.base x) →
        0 < p.length →
        (∀ t : ℕ, t < 4 → ∀ x y : ℕ, fourGonCut p q r s t ≤ x → x ≤ y →
          y ≤ fourGonCut p q r s (t + 1) →
          ((y - x : ℕ) : ℝ) / 1 - (bn : ℝ)
            ≤ ((wordDist D.alphabet.carrier
                (vertex (1 : G) (p ++ q ++ r ++ revWord s) x)
                (vertex (1 : G) (p ++ q ++ r ++ revWord s) y) : ℕ) : ℝ)) →
        IsComp lam q i (i + 1) → (i + 1 < q.length ∨ 0 < r.length) →
        IsComp lam s j (j + 1) → (j + 1 < s.length ∨ 0 < r.length) →
        Connected D.fam lam 1 (p ++ q ++ r ++ revWord s) (p.length + i)
            (p.length + q.length + r.length + (s.length - (j + 1))) →
        (∀ i' : ℕ, i' ≤ q.length → i' ≠ i →
          (vertex (1 : G) q i)⁻¹ * vertex (1 : G) q i' ∉ D.fam lam) →
        (∀ m : ℕ, m ≤ s.length → m ≠ j + 1 →
          (vertex (1 : G) s (j + 1))⁻¹ * vertex (1 : G) s m ∉ D.fam lam) →
        ((vertex (1 : G) s j)⁻¹ * (RelLetter.listVal p * vertex (1 : G) q i)
            ∈ D.relBall lam eps) ∧
          ((RelLetter.listVal p * vertex (1 : G) q (i + 1))⁻¹ *
            vertex (1 : G) s (j + 1) ∈ D.relBall lam eps) := by
  obtain ⟨C, hC0, hC⟩ := two_block_conj_named_hyp D hsymm bn hδ
  refine ⟨C * 4, by omega, ?_⟩
  intro lam p q r s i j hclose hlet hp hr hp0 hqg hcompq hkq hcomps hlq hmatch
    hqside hsside
  have hiq : i + 1 ≤ q.length := hcompq.2.1
  have hi : i ≤ q.length := by omega
  have hl : j + 1 ≤ s.length := hcomps.2.1
  exact hC lam p q r s i (i + 1) j (j + 1) hclose hlet hp hr hp0 hqg hcompq hkq
    hcomps hlq hmatch
    (innermost_of_sideExclusions D lam p q r s hclose hr hi hl hmatch hqside
      hsside)
    (otherArc_of_sideExclusions D lam p q r s hclose hp hi hl hmatch hqside
      hsside)

end Entry

end OsinComponents
end GGT
end GroupApproximation
