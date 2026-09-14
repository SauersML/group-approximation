import GroupApproximation.GGT.VanKampen.CombMap
import GroupApproximation.Meta.AxiomGuard

/-!
# Small faces of a simple bipartite map

Colour the darts of a map by a Boolean `c` that edge reversal flips and vertex rotation keeps.  Take
the map simple (no two darts join one ordered pair of vertices), with every vertex of colour `true`
of degree at least two.  Read a face from a dart `x` of colour `true` as `x, φx, φ²x, φ³x, …`
with `φ = σ ∘ α`.

* `vertexOf_facePerm_ne_pow_three`: `φx` and `φ³x` start at different vertices.  Otherwise `φx`
  and `α(φ²x)` join the same ordered pair, so `φ²x = α(φx)` and the rotation fixes `α(φx)`, a dart
  of colour `true`.
* `sigma_alpha_eq_of_vertexOf_eq`: if `x` and `φ²x` start at one vertex, the rotation fixes `αx`.
  Here `αx` and `φx` join the same ordered pair.
* `card_filter_degenerate_le`: the faces through a dart `x` of colour `true` with `x` and `φ²x` at
  one vertex number at most the darts of colour `false` fixed by the rotation.  So at most one per
  vertex of colour `false` of degree one.

On the contact map of Osin's Lemma 9.4, colour `true` is based at a rich polygon.  A face of degree
four is then either *degenerate*, with a pendant object charged here, or reads two distinct polygons
and two distinct objects.

Model tests (hand).
* The path `a – f – b` with both objects pendant is one face of degree four through `f` twice, and
  it is charged to the pendant object `a`.
* The square `f – a – f′ – b` has two nondegenerate faces of degree four.

Infrastructure for the contact count of Osin's Lemma 9.4 (arXiv:math/0411039v3, §9); certifies no
printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.CombMap

open scoped Classical

universe u

variable (M : CombMap.{u}) (c : M.Dart → Bool)
  (hflip : ∀ x, c (M.alpha x) = !c x) (hsig : ∀ x, c (M.sigma x) = c x)
  (hsimple : ∀ x y, M.vertexOf x = M.vertexOf y →
    M.vertexOf (M.alpha x) = M.vertexOf (M.alpha y) → x = y)

include hflip hsig hsimple in
/-- **`φx` and `φ³x` start at different vertices.** -/
theorem vertexOf_facePerm_ne_pow_three (hdeg : ∀ x, c x = true → M.sigma x ≠ x)
    (x : M.Dart) (hx : c x = true) :
    M.vertexOf (M.facePerm x) ≠ M.vertexOf (M.facePerm (M.facePerm (M.facePerm x))) := by
  intro h
  have h1 : M.vertexOf (M.facePerm x) =
      M.vertexOf (M.alpha (M.facePerm (M.facePerm x))) :=
    h.trans (M.vertexOf_sigma (M.alpha (M.facePerm (M.facePerm x))))
  have h2 : M.vertexOf (M.alpha (M.facePerm x)) =
      M.vertexOf (M.alpha (M.alpha (M.facePerm (M.facePerm x)))) := by
    rw [M.alpha_involutive]
    exact (M.vertexOf_sigma (M.alpha (M.facePerm x))).symm
  have hyz : M.facePerm x = M.alpha (M.facePerm (M.facePerm x)) :=
    hsimple _ _ h1 h2
  have hfix : M.sigma (M.alpha (M.facePerm x)) = M.alpha (M.facePerm x) := by
    have e := congrArg M.alpha hyz
    rw [M.alpha_involutive] at e
    exact e.symm
  have hcol : c (M.alpha (M.facePerm x)) = true := by
    rw [hflip]
    show (!c (M.sigma (M.alpha x))) = true
    simp [hsig, hflip, hx]
  exact hdeg _ hcol hfix

include hsimple in
/-- **If `x` and `φ²x` start at one vertex, the rotation fixes `αx`.** -/
theorem sigma_alpha_eq_of_vertexOf_eq (x : M.Dart)
    (h : M.vertexOf x = M.vertexOf (M.facePerm (M.facePerm x))) :
    M.sigma (M.alpha x) = M.alpha x := by
  have h1 : M.vertexOf (M.alpha x) = M.vertexOf (M.facePerm x) :=
    (M.vertexOf_sigma (M.alpha x)).symm
  have h2 : M.vertexOf (M.alpha (M.alpha x)) = M.vertexOf (M.alpha (M.facePerm x)) := by
    rw [M.alpha_involutive]
    exact h.trans (M.vertexOf_sigma (M.alpha (M.facePerm x)))
  exact (hsimple _ _ h1 h2).symm

include hflip hsig hsimple in
/-- **Degenerate faces are charged to fixed darts of colour `false`.** -/
theorem card_filter_degenerate_le :
    (Finset.univ.filter fun F : M.Face => ∃ x, M.faceOf x = F ∧ c x = true ∧
        M.vertexOf x = M.vertexOf (M.facePerm (M.facePerm x))).card ≤
      (Finset.univ.filter fun y : M.Dart => c y = false ∧ M.sigma y = y).card := by
  classical
  have hsub : (Finset.univ.filter fun F : M.Face => ∃ x, M.faceOf x = F ∧ c x = true ∧
      M.vertexOf x = M.vertexOf (M.facePerm (M.facePerm x))) ⊆
      (Finset.univ.filter fun y : M.Dart => c y = false ∧ M.sigma y = y).image M.faceOf := by
    intro F hF
    obtain ⟨x, rfl, hx, hv⟩ := (Finset.mem_filter.mp hF).2
    have hB := M.sigma_alpha_eq_of_vertexOf_eq hsimple x hv
    refine Finset.mem_image.mpr ⟨M.facePerm x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩,
      M.faceOf_facePerm x⟩
    · show c (M.sigma (M.alpha x)) = false
      simp [hsig, hflip, hx]
    · show M.sigma (M.sigma (M.alpha x)) = M.sigma (M.alpha x)
      rw [hB, hB]
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

end GroupApproximation.GGT.VanKampen.CombMap

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.vertexOf_facePerm_ne_pow_three
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.card_filter_degenerate_le
