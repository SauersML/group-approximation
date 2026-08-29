import GroupApproximation.GGT.HullSCRelatorSeparation2ApplySide

/-!
# The polygon at a matched pair, with its configuration clauses discharged

`GGT.OsinComponents.two_block_conj_named` bounds both gaps of a matched pair and
carries two clauses about the configuration.
`GGT/HullSCRelatorSeparation2ApplySide.lean` proves both from the two same-side
exclusions, so a caller holding those need never meet the clauses at all.  This
module is that composition, at the granularity the alternating relator works in:
components spanning a single letter, so `k = i + 1` and `l = j + 1`.

What is left in front of it is the design's business rather than the polygon's:
the two same-side exclusions, which `HullSC.index_close_of_connected` reduces to
the design's window clause, and the quadrilateral's own quasi-geodesicity.  What
comes out is the two gaps by name, in a relative ball whose radius is fixed
before any of the data --- which is what lets the design be run at it.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The two gaps of a matched pair of single-letter components, by name.**

Every hypothesis is either the quadrilateral's own or the design's; the two
configuration clauses of `two_block_conj_named` are discharged here from the two
same-side exclusions and do not reach the caller. -/
theorem exists_eps_matchedPair (D : RelGenSet G Λ)
    (hbound : ∀ mu b : ℝ, 1 ≤ mu → 0 ≤ b → ∃ C : ℕ, 0 < C ∧
      ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
        IsQuasiGeodesicPolygon D mu b n v u →
        ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
          (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (mu b : ℝ) (hmu : 1 ≤ mu)
    (hb : 0 ≤ b) :
    ∃ eps : ℕ, 0 < eps ∧
      ∀ (lam : Λ) (p q r s : List (RelLetter G Λ)) (i j : ℕ),
        RelLetter.listVal s = RelLetter.listVal p * RelLetter.listVal q
            * RelLetter.listVal r →
        (∀ a ∈ p ++ q ++ r ++ revWord s, D.IsLetter a) →
        (∀ a ∈ p, ∃ x : G, a = RelLetter.base x) →
        (∀ a ∈ r, ∃ x : G, a = RelLetter.base x) →
        0 < p.length →
        (∀ t : ℕ, t < 4 → ∀ x y : ℕ, fourGonCut p q r s t ≤ x → x ≤ y →
          y ≤ fourGonCut p q r s (t + 1) →
          ((y - x : ℕ) : ℝ) / mu - b
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
  obtain ⟨C, hC0, hC⟩ := two_block_conj_named D hbound hsymm mu b hmu hb
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

end OsinComponents
end GGT
end GroupApproximation
