import GroupApproximation.GGT.OsinTheorem54SepClosingEdge
import GroupApproximation.GGT.OsinTheorem54SepGeodesicSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Un-coning cyclic peripherals, step 2: a closing jump across an avoiding path is short

The geometric lemmas of the un-coning argument all have one shape.  Three geodesic words `p`, `q`,
`r` read from `1` spell a path from `1` to a point `h` of the coset `H_λ`, and none of their
`λ`-letters is read at a vertex of `H_λ`: the path never travels inside that coset.  Closing it by
the single `λ`-letter `h⁻¹` gives a quadrilateral of geodesic sides in which the closing letter is
an isolated component (`OsinComponents.isIsolated_closing_of_avoidsFrom`), so Proposition 4.2 of
Dahmani–Guirardel–Osin bounds its span: `h⁻¹` lies in the `d̂_λ`-ball of radius `4C`.

This is how the entrances and exits of two geodesics into a common coset of a cyclic member are
compared when the third side of the triangle does not reach that coset, and how a short connector
crossing a coset is compared with the sides of a triangle.

* `avoidsFrom_append_iff` — avoidance of a concatenation is avoidance of each piece from its own
  starting vertex;
* `closingJump_inv_mem_relBall` — the bound.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents

universe u w

namespace Uncone

variable {G : Type u} [Group G] {Λ : Type w}

/-- **Avoidance of a concatenation.**  A path read from `p` avoids `Γ_{H_λ}` exactly when its first
piece does, read from `p`, and its second piece does, read from the endpoint of the first. -/
theorem avoidsFrom_append_iff (H : Λ → Subgroup G) (lam : Λ) :
    ∀ (u₁ u₂ : List (RelLetter G Λ)) (p : G),
      AvoidsFrom H lam (u₁ ++ u₂) p ↔
        AvoidsFrom H lam u₁ p ∧ AvoidsFrom H lam u₂ (p * RelLetter.listVal u₁) := by
  intro u₁
  induction u₁ with
  | nil =>
      intro u₂ p
      simp [AvoidsFrom, RelLetter.listVal_nil]
  | cons a t ih =>
      intro u₂ p
      simp only [List.cons_append, AvoidsFrom, ih, OsinComponents.listVal_cons, mul_assoc,
        and_assoc]

/-- **A closing jump across an avoiding path is short.**

Let `p`, `q`, `r` be geodesic words read from `1`, spelling together `h ∈ H_λ`, such that the path
`p ++ q ++ r` read from `1` avoids `Γ_{H_λ}`.  Then `h⁻¹` lies in the `d̂_λ`-ball of radius `4C`,
where `C` is the constant of the isolated-component bound for `(1,0)`-quasi-geodesic polygons with
at most six sides. -/
theorem closingJump_inv_mem_relBall (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {C : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (lam : Λ) {p q r : List (RelLetter G Λ)}
    (hp : IsGeodesicWord D 1 (RelLetter.listVal p) p)
    (hq : IsGeodesicWord D 1 (RelLetter.listVal q) q)
    (hr : IsGeodesicWord D 1 (RelLetter.listVal r) r)
    {h : G} (hh : h ∈ D.fam lam)
    (hval : RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r = h)
    (hav : AvoidsFrom D.fam lam (p ++ q ++ r) 1) :
    h⁻¹ ∈ D.relBall lam (C * 4) := by
  by_cases h1 : h = 1
  · rw [h1, inv_one]
    exact one_mem_relBall D lam _
  have hd1 : wordDist D.alphabet.carrier 1 h = 1 := by
    have hle : wordDist D.alphabet.carrier 1 h ≤ 1 := by
      rw [wordDist_one_left]
      exact wordNorm_le_one_of_mem (Or.inr (Set.mem_iUnion.mpr ⟨lam, hh⟩))
    have hne : wordDist D.alphabet.carrier 1 h ≠ 0 := by
      intro h0
      exact h1 ((wordDist_eq_zero_iff D.alphabet.symmetricGenerating 1 h).mp h0).symm
    omega
  have hvals : RelLetter.listVal [RelLetter.comp lam h] = h := by
    rw [listVal_singleton]
    rfl
  have hsGeod : IsGeodesicWord D 1 (RelLetter.listVal [RelLetter.comp lam h])
      [RelLetter.comp lam h] := by
    refine ⟨?_, one_mul _, ?_⟩
    · intro a ha
      rw [List.eq_of_mem_singleton ha]
      exact hh
    · rw [List.length_singleton, hvals, hd1]
  have hclose : RelLetter.listVal [RelLetter.comp lam h]
      = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r := by
    rw [hvals, hval]
  have hpoly := isQuasiGeodesicPolygon_fourGon_of_geodesic D hsymm p q r
    [RelLetter.comp lam h] hp hq hr hsGeod hclose
  have hrev : revWord [RelLetter.comp lam h] = [RelLetter.comp lam h⁻¹] := rfl
  rw [hrev] at hpoly
  have hlet : ∀ a ∈ p ++ q ++ r, D.IsLetter a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · exact hp.1 a ha
      · exact hq.1 a ha
    · exact hr.1 a ha
  have hvalt : RelLetter.listVal (p ++ q ++ r) = h := by
    rw [listVal_append, listVal_append, hval]
  have hiso := isIsolated_closing_of_avoidsFrom D lam hh hlet hvalt hav
  obtain ⟨k, hk⟩ := hiso.1
  have hlen : (p ++ q ++ r ++ [RelLetter.comp lam h⁻¹]).length
      = (p ++ q ++ r).length + 1 := by
    rw [List.length_append, List.length_singleton]
  have hk1 : k = (p ++ q ++ r).length + 1 := by
    have hlt := hk.1
    have hle := hk.2.1
    rw [hlen] at hle
    omega
  have hspan := hbnd 4 (by norm_num) 1 (p ++ q ++ r ++ [RelLetter.comp lam h⁻¹]) hpoly lam
    (p ++ q ++ r).length k hk hiso
  have hv0 : vertex (1 : G) (p ++ q ++ r ++ [RelLetter.comp lam h⁻¹]) (p ++ q ++ r).length
      = h := by
    rw [vertex_append_of_le (p ++ q ++ r) [RelLetter.comp lam h⁻¹] 1 _ le_rfl,
      vertex_length, one_mul, hvalt]
  have hvk : vertex (1 : G) (p ++ q ++ r ++ [RelLetter.comp lam h⁻¹]) k = 1 := by
    rw [hk1, ← hlen, vertex_length, one_mul, listVal_append, hvalt, listVal_singleton]
    show h * h⁻¹ = 1
    rw [mul_inv_cancel]
  rw [hv0, hvk, mul_one] at hspan
  exact hspan

end Uncone

end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.Uncone.avoidsFrom_append_iff
#audit_axioms GroupApproximation.GGT.Uncone.closingJump_inv_mem_relBall
