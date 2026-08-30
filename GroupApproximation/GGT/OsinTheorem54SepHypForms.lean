import GroupApproximation.GGT.OsinTheorem54SepSixBound
import GroupApproximation.GGT.OsinTheorem54SepTwoBlockRot
import GroupApproximation.GGT.OsinTheorem54SepDeepSixForm

/-!
# The §4.2 binder, discharged

`OsinTheorem54SepSixBound.sixBound_one_of_fourPointHyperbolic` proves Osin's
Lemma 4.2 at `μ = 1` outright, from symmetry of the base and four-point
hyperbolicity of `Γ(G, X ⊔ ℋ)`.  This module feeds it to the three theorems of
the chain that carried the bound as a hypothesis, so that each of them becomes a
statement about a hyperbolic relative graph and nothing else.

There is no content here.  Each theorem is its `_one` form with the binder
filled in, and the `_one` forms are their `_of_bound` and `_of_cut` bodies with
one spelling of the bound chosen.  What matters is what the signatures no longer
say: no consumer below this line has to carry `IsolatedComponentBound`, in any
spelling, and the only geometric input left in the two-block chain is that the
relative graph is hyperbolic.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A deep component of a long side is connected to another component of the
quadrilateral**, from hyperbolicity alone. -/
theorem exists_other_component_of_deep_of_hyperbolic (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) (lam : Λ)
    (b : ℝ) (hb : 0 ≤ b) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n rho : ℕ), n ≤ 6 →
      ∀ p q r s : List (RelLetter G Λ),
      RelLetter.listVal s
          = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r →
      (∀ a ∈ p, ∃ x : G, a = RelLetter.base x) →
      (∀ a ∈ r, ∃ x : G, a = RelLetter.base x) →
      IsQuasiGeodesicPolygon D 1 b n 1 (p ++ q ++ r ++ revWord s) →
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
                  = vertex (1 : G) s j) :=
  exists_other_component_of_deep_one D
    (sixBound_one_of_fourPointHyperbolic D hsymm hδ) lam b hb

/-- **The rigidity clause, from hyperbolicity alone.** -/
theorem mem_fam_of_conj_of_deep_of_hyperbolic (D : RelGenSet G Bool)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
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
  mem_fam_of_conj_of_deep_one D (sixBound_one_of_fourPointHyperbolic D hsymm hδ)
    hmem s b hb

/-- **Both gaps of a matched pair of blocks are short, from hyperbolicity
alone.**  The end of the line: `hsymm` and a hyperbolic relative graph. -/
theorem two_block_conj_of_hyperbolic (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) (b : ℝ)
    (hb : 0 ≤ b) :
    ∃ C : ℕ, 0 < C ∧
      ∀ (lam : Λ) (p q r s : List (RelLetter G Λ)) (i k j l : ℕ),
        RelLetter.listVal s = RelLetter.listVal p * RelLetter.listVal q
            * RelLetter.listVal r →
        (∀ a ∈ p ++ q ++ r ++ revWord s, D.IsLetter a) →
        (∀ a ∈ p, ∃ x : G, a = RelLetter.base x) →
        (∀ a ∈ r, ∃ x : G, a = RelLetter.base x) →
        0 < p.length →
        (∀ t : ℕ, t < 4 → ∀ x y : ℕ, fourGonCut p q r s t ≤ x → x ≤ y →
          y ≤ fourGonCut p q r s (t + 1) →
          ((y - x : ℕ) : ℝ) / 1 - b
            ≤ ((wordDist D.alphabet.carrier
                (vertex (1 : G) (p ++ q ++ r ++ revWord s) x)
                (vertex (1 : G) (p ++ q ++ r ++ revWord s) y) : ℕ) : ℝ)) →
        IsComp lam q i k → (k < q.length ∨ 0 < r.length) →
        IsComp lam s j l → (l < s.length ∨ 0 < r.length) →
        Connected D.fam lam 1 (p ++ q ++ r ++ revWord s) (p.length + i)
            (p.length + q.length + r.length + (s.length - l)) →
        (∀ t : ℕ, p.length + i < t →
          t < p.length + q.length + r.length + (s.length - l) →
          IsCompStart lam (p ++ q ++ r ++ revWord s) t →
          ¬ Connected D.fam lam 1 (p ++ q ++ r ++ revWord s)
            (p.length + i) t) →
        (∀ o : ℕ,
          (p.length + q.length + r.length + (s.length - l) < o
              ∧ o < (p ++ q ++ r ++ revWord s).length)
            ∨ o < p.length + i →
          IsCompStart lam (p ++ q ++ r ++ revWord s) o →
          ¬ Connected D.fam lam 1 (p ++ q ++ r ++ revWord s)
            (p.length + q.length + r.length + (s.length - l)) o) →
        ((vertex (1 : G) s j)⁻¹ * (RelLetter.listVal p * vertex (1 : G) q i)
            ∈ D.relBall lam (C * 4)) ∧
          ((RelLetter.listVal p * vertex (1 : G) q k)⁻¹ * vertex (1 : G) s l
            ∈ D.relBall lam (C * 4)) :=
  two_block_conj_named_one D (sixBound_one_of_fourPointHyperbolic D hsymm hδ)
    hsymm b hb

end OsinComponents
end GGT
end GroupApproximation
