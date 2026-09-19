import GroupApproximation.GGT.DGOLemma421Proof

/-!
# The endpoint-close mixed quadrilateral for Lemma 4.21(b)

Given geodesic connector words at the two endpoints of a pair of W-words,
their labels satisfy the four-gon closure identity.  The mixed-quadrilateral
lemma from the DGO proof then supplies the `(4,1)` polygon on which the
isolated-component bound is applied.  This module records that endpoint and
basepoint bookkeeping separately from the finite absorption argument.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- Geodesic connectors at the start and end of two W-words close them to the
mixed quadrilateral used by the DGO Proposition 4.14 bound. -/
theorem isQuasiGeodesicPolygon_of_endpoint_connectors
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (vp vq : G) (p q : List (RelLetter G Λ))
    (u r : List (RelLetter G Λ))
    (hu : IsGeodesicWord D vp vq u)
    (hr : IsGeodesicWord D
      (vertex vq q q.length) (vertex vp p p.length) r)
    (hpq : ∀ i j : ℕ, i ≤ j → j ≤ p.length →
      ((j - i : ℕ) : ℝ) / 4 - 1 ≤
        ((wordDist D.alphabet.carrier (vertex (1 : G) p i)
          (vertex (1 : G) p j) : ℕ) : ℝ))
    (hqq : ∀ i j : ℕ, i ≤ j → j ≤ q.length →
      ((j - i : ℕ) : ℝ) / 4 - 1 ≤
        ((wordDist D.alphabet.carrier (vertex (1 : G) q i)
          (vertex (1 : G) q j) : ℕ) : ℝ))
    (hletp : ∀ a ∈ p, D.IsLetter a)
    (hletq : ∀ a ∈ q, D.IsLetter a) :
    IsQuasiGeodesicPolygon D 4 1 4 vp
      (u ++ q ++ r ++ revWord p) := by
  have huone : IsGeodesicWord D 1 (RelLetter.listVal u) u :=
    isGeodesicWord_one_of D hu
  have hrone : IsGeodesicWord D 1 (RelLetter.listVal r) r :=
    isGeodesicWord_one_of D hr
  have hletu : ∀ a ∈ u, D.IsLetter a := hu.1
  have hletr : ∀ a ∈ r, D.IsLetter a := hr.1
  have hclose : RelLetter.listVal p =
      RelLetter.listVal u * RelLetter.listVal q * RelLetter.listVal r := by
    have huval : vp * RelLetter.listVal u = vq := hu.2.1
    have hpval : vp * RelLetter.listVal p =
        vertex vp p p.length := by
      exact vertex_length vp p
    have hqval : vq * RelLetter.listVal q =
        vertex vq q q.length := by
      exact vertex_length vq q
    have hrval : (vertex vq q q.length) * RelLetter.listVal r =
        vertex vp p p.length := hr.2.1
    calc
      RelLetter.listVal p = vp⁻¹ * vertex vp p p.length := by
        rw [← hpval]
        group
      _ = vp⁻¹ * ((vertex vq q q.length) * RelLetter.listVal r) := by
        rw [hrval]
      _ = vp⁻¹ * ((vq * RelLetter.listVal q) * RelLetter.listVal r) := by
        rw [hqval]
      _ = vp⁻¹ * ((vp * RelLetter.listVal u) * RelLetter.listVal q *
          RelLetter.listVal r) := by
        rw [huval]
      _ = RelLetter.listVal u * RelLetter.listVal q * RelLetter.listVal r := by
        group
  have hlet : ∀ a ∈ u ++ q ++ r ++ revWord p, D.IsLetter a := by
    intro a ha
    rcases List.mem_append.mp ha with hau | haqr
    · exact hletu a hau
    · rcases List.mem_append.mp haqr with haq | harp
      · exact hletq a haq
      · rcases List.mem_append.mp harp with har | harev
        · exact hletr a har
        · exact isLetter_of_mem_revWord D hsymm hletp a harev
  have hpoly_one := isQuasiGeodesicPolygon_fourGon_of_mixed D u q r p
    huone hrone hqq hpq hlet hclose
  exact isQuasiGeodesicPolygon_translate D vp hpoly_one

end OsinComponents
end GGT
end GroupApproximation
