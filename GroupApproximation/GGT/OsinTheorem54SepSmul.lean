import GroupApproximation.GGT.OsinTheorem54SeparatingCosets
import GroupApproximation.GGT.OsinTheorem54SepSplit
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Left translation carries separating cosets to separating cosets

The `sep_smul` field of `GGT.OsinEnlargement.SepData` and `SepDataFam`:
`|S(af, ag; D)| = |S(f, g; D)|`.  For the concrete count
`OsinComponents.sepCard` this is not an axiom but a computation, and every step
of it is left-invariance of something already defined:

* the word metric, since `(af)⁻¹(ag) = f⁻¹g`, so a word is geodesic from `af`
  to `ag` exactly when it is geodesic from `f` to `g`;
* the vertices, `vertex (a * v) w i = a * vertex v w i`;
* the span of a component, `(vertex (av) w i)⁻¹ * vertex (av) w k` being
  literally `(vertex v w i)⁻¹ * vertex v w k`, so a penetration is essential on
  one side exactly when it is on the other --- the `d̂_λ`-ball never enters the
  comparison.

What is left is that the coset recorded, `mk (vertex (af) w i)`, is the
translate `a • mk (vertex f w i)`.  So `sepSet` translates as a set and
`sepCard` is unchanged, left translation on `G ⧸ H_λ` being injective.

This module is unconditional: it consumes neither
`OsinComponents.LemmaFourEight` nor `OsinComponents.IsolatedComponentBound`.
`sepCard` is `Set.ncard`, which is `0` on an infinite set, and the argument
below never needs the set to be finite --- the two sets are in bijection either
way.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Left translation of vertices and spans -/

/-- **Vertices translate.** -/
theorem vertex_mul_left (a v : G) (w : List (RelLetter G Λ)) (i : ℕ) :
    vertex (a * v) w i = a * vertex v w i := by
  rw [vertex_eq_mul_listVal_take w (a * v) i, vertex_eq_mul_listVal_take w v i,
    mul_assoc]

/-- **The span of a component does not see the basepoint.** -/
theorem span_mul_left (a v : G) (w : List (RelLetter G Λ)) (i k : ℕ) :
    (vertex (a * v) w i)⁻¹ * vertex (a * v) w k
      = (vertex v w i)⁻¹ * vertex v w k := by
  rw [vertex_mul_left, vertex_mul_left]
  group

/-- **Essential penetration is left-invariant**, the span being unchanged. -/
theorem essentiallyPenetrates_mul_left (D : RelGenSet G Λ) (lam : Λ) (Dc : ℕ)
    (a v : G) (w : List (RelLetter G Λ)) (i k : ℕ) :
    EssentiallyPenetrates D lam Dc (a * v) w i k
      ↔ EssentiallyPenetrates D lam Dc v w i k := by
  show IsComp lam w i k ∧
      (vertex (a * v) w i)⁻¹ * vertex (a * v) w k ∉ D.relBall lam Dc
    ↔ IsComp lam w i k ∧
      (vertex v w i)⁻¹ * vertex v w k ∉ D.relBall lam Dc
  rw [span_mul_left]

/-- **Geodesic words are left-invariant.** -/
theorem isGeodesicWord_mul_left (D : RelGenSet G Λ) (a f g : G)
    (w : List (RelLetter G Λ)) :
    IsGeodesicWord D (a * f) (a * g) w ↔ IsGeodesicWord D f g w := by
  have hdist : wordDist D.alphabet.carrier (a * f) (a * g)
      = wordDist D.alphabet.carrier f g := by
    show wordNorm D.alphabet.carrier ((a * f)⁻¹ * (a * g))
      = wordNorm D.alphabet.carrier (f⁻¹ * g)
    congr 1
    group
  constructor
  · rintro ⟨hlet, hprod, hlen⟩
    refine ⟨hlet, mul_left_cancel (a := a) ?_, by rw [hlen, hdist]⟩
    rw [← mul_assoc]
    exact hprod
  · rintro ⟨hlet, hprod, hlen⟩
    exact ⟨hlet, by rw [mul_assoc, hprod], by rw [hlen, hdist]⟩

/-! ## The separating set translates -/

/-- **`S(af, ag; D)` is the translate of `S(f, g; D)`.** -/
theorem sepSet_smul (D : RelGenSet G Λ) (lam : Λ) (Dc : ℕ) (a f g : G) :
    sepSet D lam Dc (a * f) (a * g)
      = (fun c : G ⧸ D.fam lam => a • c) '' sepSet D lam Dc f g := by
  ext c
  constructor
  · rintro ⟨w, i, k, hgw, hpen, rfl⟩
    refine ⟨QuotientGroup.mk (vertex f w i),
      ⟨w, i, k, (isGeodesicWord_mul_left D a f g w).mp hgw,
        (essentiallyPenetrates_mul_left D lam Dc a f w i k).mp hpen, rfl⟩, ?_⟩
    show (a • (QuotientGroup.mk (vertex f w i) : G ⧸ D.fam lam))
      = QuotientGroup.mk (vertex (a * f) w i)
    rw [vertex_mul_left]
    rfl
  · rintro ⟨c', ⟨w, i, k, hgw, hpen, rfl⟩, rfl⟩
    refine ⟨w, i, k, (isGeodesicWord_mul_left D a f g w).mpr hgw,
      (essentiallyPenetrates_mul_left D lam Dc a f w i k).mpr hpen, ?_⟩
    show (a • (QuotientGroup.mk (vertex f w i) : G ⧸ D.fam lam))
      = QuotientGroup.mk (vertex (a * f) w i)
    rw [vertex_mul_left]
    rfl

/-- **`sep_smul`, for the concrete count.**  This is the field of `SepData` and
`SepDataFam`, discharged. -/
theorem sepCard_smul (D : RelGenSet G Λ) (lam : Λ) (Dc : ℕ) (a f g : G) :
    sepCard D lam Dc (a * f) (a * g) = sepCard D lam Dc f g := by
  have hinj : Function.Injective (fun c : G ⧸ D.fam lam => a • c) := by
    intro c₁ c₂ hc
    have hc' : a • c₁ = a • c₂ := hc
    have h1 : a⁻¹ • (a • c₁) = a⁻¹ • (a • c₂) := by rw [hc']
    rwa [inv_smul_smul, inv_smul_smul] at h1
  show (sepSet D lam Dc (a * f) (a * g)).ncard = (sepSet D lam Dc f g).ncard
  rw [sepSet_smul, Set.ncard_image_of_injective _ hinj]

end OsinComponents
end GGT
end GroupApproximation
