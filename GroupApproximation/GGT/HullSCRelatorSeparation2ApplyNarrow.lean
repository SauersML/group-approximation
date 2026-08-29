import GroupApproximation.GGT.DGOPolygonBaseCaseTower
import GroupApproximation.GGT.OsinTheorem54SepFourGonSide

/-!
# The isolated-component bound at one pair of constants

`GGT.OsinComponents.exists_other_component_of_deep_six` carries the bound as
`∀ mu b : ℝ, 1 ≤ mu → 0 ≤ b → ∃ C, …` and spends it at exactly one pair --- the
pair it is separately handed.  The quantifier therefore buys nothing, and it is
precisely what fp-geometry's tower cannot supply: the tower proves the bound at
`mu = 1` and NATURAL `b`, and at `mu > 1` a quasi-geodesic polygon is a weaker
object, so no casting reaches it.

`exists_other_component_of_deep_six_at` is the same theorem with the binder
narrowed to that one pair, and the same proof; `hmu` and `hb` disappear, having
existed only to feed the quantifier.  `exists_other_component_of_deep_six_hyp`
then discharges it outright from four-point hyperbolicity of `Γ(G, X ⊔ ℋ)`, so
that `hδ` stands where the bound stood.

Note which graph `hδ` is about: the RELATIVE Cayley graph `Γ(G, X ⊔ ℋ)`, the
object hyperbolic embeddedness is defined against, not `Γ(G, X)`.

## What this does not reach

The other consumer of the bound in this chain is
`GGT.OsinComponents.two_block_conj_named`, and narrowing it bottoms out in
`DGOIsolatedComponentCut.connector_mem_relBall`, whose proof is some two hundred
and fifty lines.  That one is not a transcription worth making blind, so the
gap-side of the chain still carries the `∀`-form; only the match-side is
discharged here.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The deep-component step, with the bound taken at one pair of
constants.**  `GGT.OsinComponents.exists_other_component_of_deep_six` verbatim,
except that the bound is not quantified over pairs it never uses. -/
theorem exists_other_component_of_deep_six_at (D : RelGenSet G Λ) (lam : Λ)
    (mu b : ℝ)
    (hbound : ∃ C : ℕ, 0 < C ∧
      ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
        IsQuasiGeodesicPolygon D mu b n v u →
        ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
          (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n)) :
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
  obtain ⟨C, hCpos, hC⟩ := hbound
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

/-- **The deep-component step, from four-point hyperbolicity.**

The bound is no longer a hypothesis: fp-geometry's tower proves it at `mu = 1`
and every natural `b`, which is the pair this chain uses, so what stands in its
place is `hδ` --- four-point hyperbolicity of the RELATIVE Cayley graph
`Γ(G, X ⊔ ℋ)`. -/
theorem exists_other_component_of_deep_six_hyp (D : RelGenSet G Λ) (lam : Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (bn : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n rho : ℕ), n ≤ 6 →
      ∀ p q r s : List (RelLetter G Λ),
      RelLetter.listVal s
          = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r →
      (∀ a ∈ p, ∃ x : G, a = RelLetter.base x) →
      (∀ a ∈ r, ∃ x : G, a = RelLetter.base x) →
      IsQuasiGeodesicPolygon D 1 (bn : ℝ) n 1 (p ++ q ++ r ++ revWord s) →
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
  exists_other_component_of_deep_six_at D lam 1 (bn : ℝ)
    ⟨15 * (25 * (δ + bn + 1)), by omega,
      isolatedComponentBound_of_fourPointHyperbolic_at D hsymm bn hδ⟩

end OsinComponents
end GGT
end GroupApproximation
