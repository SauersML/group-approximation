import GroupApproximation.GGT.OsinTheorem54SepFourGonPolygon

/-!
# The two interfaces of the relator chain, stated once

The polygon's output and the matching step are consumed by five modules apiece,
and until now each restated them by hand.  That is how the `b` of the
quasi-geodesic clause came to be written `0` in five places while the producer
delivered `|p| + c`: every file was internally consistent, every file compiled,
and nothing could be composed.  A per-file probe cannot see that, because a
hypothesis is a hypothesis; it shows up only at the joint.

So they are stated once here and referred to by name.  Consumer and producer can
no longer disagree, because there is nothing left to disagree about.

* `MatchedPairOutput D eps bn` --- what
  `GGT.OsinComponents.exists_eps_matchedPair_hyp` returns: for a matched pair of
  single-letter components of a quadrilateral whose two long sides are
  `(1, bn)`-quasi-geodesic, both of the polygon's gaps lie in `D.relBall lam eps`,
  BY NAME.  The naming is what the aligned branch spends.
* `DeepMatchOutput D Cm bn` --- what
  `GGT.OsinComponents.exists_deep_match_hyp` returns: a deep component of the
  long side is matched across, at a positive index, with its connector named.

Both are `abbrev`, so they unfold where they are applied and a caller never has
to see the name.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u

variable {G : Type u} [Group G]

/-- **The polygon's output at a matched pair**, at radius `eps`, for a
quadrilateral whose long sides are `(1, bn)`-quasi-geodesic. -/
abbrev MatchedPairOutput (D : RelGenSet G Bool) (eps bn : ℕ) : Prop :=
  ∀ (lam : Bool) (P Q R S : List (RelLetter G Bool)) (i j : ℕ),
    RelLetter.listVal S
        = RelLetter.listVal P * RelLetter.listVal Q * RelLetter.listVal R →
    (∀ x ∈ P ++ Q ++ R ++ revWord S, D.IsLetter x) →
    (∀ x ∈ P, ∃ g : G, x = RelLetter.base g) →
    (∀ x ∈ R, ∃ g : G, x = RelLetter.base g) →
    0 < P.length →
    (∀ t : ℕ, t < 4 → ∀ x y : ℕ, fourGonCut P Q R S t ≤ x → x ≤ y →
      y ≤ fourGonCut P Q R S (t + 1) →
      ((y - x : ℕ) : ℝ) / 1 - (bn : ℝ)
        ≤ ((wordDist D.alphabet.carrier
            (vertex (1 : G) (P ++ Q ++ R ++ revWord S) x)
            (vertex (1 : G) (P ++ Q ++ R ++ revWord S) y) : ℕ) : ℝ)) →
    IsComp lam Q i (i + 1) → (i + 1 < Q.length ∨ 0 < R.length) →
    IsComp lam S j (j + 1) → (j + 1 < S.length ∨ 0 < R.length) →
    Connected D.fam lam 1 (P ++ Q ++ R ++ revWord S) (P.length + i)
        (P.length + Q.length + R.length + (S.length - (j + 1))) →
    (∀ i' : ℕ, i' ≤ Q.length → i' ≠ i →
      (vertex (1 : G) Q i)⁻¹ * vertex (1 : G) Q i' ∉ D.fam lam) →
    (∀ m : ℕ, m ≤ S.length → m ≠ j + 1 →
      (vertex (1 : G) S (j + 1))⁻¹ * vertex (1 : G) S m ∉ D.fam lam) →
    ((vertex (1 : G) S j)⁻¹ * (RelLetter.listVal P * vertex (1 : G) Q i)
        ∈ D.relBall lam eps) ∧
      ((RelLetter.listVal P * vertex (1 : G) Q (i + 1))⁻¹ *
        vertex (1 : G) S (j + 1) ∈ D.relBall lam eps)

/-- **The matching step's output**, at constant `Cm`, for a quadrilateral whose
long sides are `(1, bn)`-quasi-geodesic. -/
abbrev DeepMatchOutput (D : RelGenSet G Bool) (Cm bn : ℕ) : Prop :=
  ∀ (lam : Bool) (rho : ℕ) (P Q R S : List (RelLetter G Bool)) (i : ℕ),
    Cm * 4 ≤ rho →
    RelLetter.listVal S
        = RelLetter.listVal P * RelLetter.listVal Q * RelLetter.listVal R →
    (∀ x ∈ P, ∃ g : G, x = RelLetter.base g) →
    (∀ x ∈ R, ∃ g : G, x = RelLetter.base g) →
    0 < R.length →
    IsQuasiGeodesicPolygon D 1 (bn : ℝ) 4 1 (P ++ Q ++ R ++ revWord S) →
    IsComp lam Q i (i + 1) →
    (vertex (1 : G) Q i)⁻¹ * vertex (1 : G) Q (i + 1) ∉ D.relBall lam rho →
    (∀ i' : ℕ, i' ≤ Q.length → i' ≠ i →
      (vertex (1 : G) Q i)⁻¹ * vertex (1 : G) Q i' ∉ D.fam lam) →
    ∃ j : ℕ, 0 < j ∧ j ≤ S.length ∧
      (∃ x : G, S[j - 1]? = some (RelLetter.comp lam x)) ∧
      ∃ h : G, h ∈ D.fam lam ∧
        RelLetter.listVal P * vertex (1 : G) Q i * h = vertex (1 : G) S j

end OsinComponents
end GGT
end GroupApproximation
