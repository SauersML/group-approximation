import GroupApproximation.GGT.CayleyGeodesicQuotient

/-!
# Vertices of the geodesic model, and the two uniformities B2 needs

`GGT/HullSCConeOffHeavyLemma67.lean` left B2 resting on one leaf,
`MatchedPowersForceCommonPower`: Dahmani--Guirardel--Osin's Lemma 6.7 with the
threshold chosen before the conjugating element.  That leaf is stated in the word
metric and mentions the whole family `g`, which is the wrong shape for whoever
discharges it --- the content is geometric and has nothing to do with families.

This module and its sequel move it.  Here are the vertex map into the geodesic
model and the two uniform statements the passage needs; the sequel proves the
word-metric leaf from the geometric one.

## `modelPoint`

`Cayley A` is not a geodesic space --- every distance in it is a natural number
--- so the fellow-travel machinery cannot run there.  `PointQuot A` is geodesic
(`CayleyGeodesicModel.isGeodesicRealisationQuot`, unconditional) and carries an
isometric `G`-action, and `iotaQuot` embeds the vertices with additive distortion
`1`.  `modelPoint A x` is that vertex, named by a group element rather than by a
`Cayley` term, and the three lemmas after it are the entire interface the sequel
uses: distances move by at most one in each direction, and left translation on
`G` becomes the action on the model.

Distortion `1` rather than `0` is what the doubling costs and it is not
negotiable, so the sequel's constants all carry it explicitly.

## The two uniformities

`UniformlyLoxodromic` asks the *family* for one set of loxodromy constants,
because `MatchedPowersForceCommonPower` fixes its threshold before `λ` and `μ`.
This is not an artifact of the formalisation: Dahmani--Guirardel--Osin state
Theorem 6.8 for a finite family, and `uniformlyLoxodromic_of_finite` shows that
is exactly what finiteness buys --- minimise the rates, maximise the additive
constants and the displacements.

`UniformCommonZpowThreshold` is the geometric leaf.  It is the integer-exponent
statement of `GGT/HullSCConeOffHeavyFellowTravel.lean` with the threshold hoisted
in front of the two elements and the basepoint, and with the loxodromy data
supplied as numeric bounds rather than as existentials.  No group family, no word
metric, no alphabet: a hyperbolic geodesic space with an action, two elements and
a point.

`uniformCommonZpowThreshold_of_bounded` is the satisfiability check.  In a
bounded space the threshold may be taken past the diameter, so the hypothesis
never fires --- a statement even a bounded space could not satisfy would be
malformed rather than hard.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

variable {G : Type u} [Group G]

/-! ## Vertices of the model -/

/-- The vertex of the geodesic model named by a group element. -/
def modelPoint (A : Alphabet G) (x : G) : CayleyGeodesicModel.PointQuot A :=
  CayleyGeodesicModel.iotaQuot A (Cayley.of A x)

/-- **Left translation becomes the action.** -/
theorem smul_modelPoint (A : Alphabet G) (h x : G) :
    h • modelPoint A x = modelPoint A (h * x) := by
  show h • CayleyGeodesicModel.iotaQuot A (Cayley.of A x)
    = CayleyGeodesicModel.iotaQuot A (Cayley.of A (h * x))
  rw [← CayleyGeodesicModel.isEquivariant_iotaQuot A h (Cayley.of A x)]
  rfl

/-- **The vertex map changes no distance by more than one.** -/
theorem abs_dist_modelPoint_sub_le (A : Alphabet G) (x y : G) :
    |dist (modelPoint A x) (modelPoint A y)
      - (wordDist A.carrier x y : ℝ)| ≤ 1 := by
  have h := CayleyGeodesicModel.hasAdditiveDistortion_iotaQuot A
    (Cayley.of A x) (Cayley.of A y)
  simpa [modelPoint, Cayley.dist_eq] using h

/-- The upper half of additive distortion. -/
theorem dist_modelPoint_le (A : Alphabet G) (x y : G) :
    dist (modelPoint A x) (modelPoint A y) ≤ (wordDist A.carrier x y : ℝ) + 1 := by
  have h := abs_le.mp (abs_dist_modelPoint_sub_le A x y)
  linarith [h.2]

/-- The lower half of additive distortion. -/
theorem le_dist_modelPoint (A : Alphabet G) (x y : G) :
    (wordDist A.carrier x y : ℝ) - 1 ≤ dist (modelPoint A x) (modelPoint A y) := by
  have h := abs_le.mp (abs_dist_modelPoint_sub_le A x y)
  linarith [h.1]

/-! ## Uniform loxodromy for a family -/

/-- **One set of loxodromy constants for the whole family.**  The rate `l`, the
additive constant `B` and the generator displacement `D` are shared by every
member.  `MatchedPowersForceCommonPower` fixes its threshold before `λ` and `μ`,
so nothing weaker is usable. -/
def UniformlyLoxodromic {Λ : Type w} (A : Alphabet G) (g : Λ → G) : Prop :=
  ∃ l B D : ℝ, 0 < l ∧ 0 ≤ B ∧ 0 ≤ D ∧ ∀ nu : Λ,
    (∀ n : ℕ, l * n - B ≤ (wordDist A.carrier 1 ((g nu) ^ n) : ℝ)) ∧
    ((wordDist A.carrier 1 (g nu) : ℝ) ≤ D)

/-- **A finite family of loxodromic elements is uniformly loxodromic.**  This is
what Dahmani--Guirardel--Osin's finiteness hypothesis in Theorem 6.8 is for:
minimise the rates and maximise the two upper constants. -/
theorem uniformlyLoxodromic_of_finite {Λ : Type w} [Finite Λ] [Nonempty Λ]
    (A : Alphabet G) (g : Λ → G)
    (hlox : ∀ nu : Λ, IsLoxodromic (g nu) (Cayley.base A)) :
    UniformlyLoxodromic A g := by
  choose l hl B hB hlin using hlox
  obtain ⟨nu₀, hnu₀⟩ := Finite.exists_min l
  obtain ⟨nu₁, hnu₁⟩ := Finite.exists_max B
  obtain ⟨nu₂, hnu₂⟩ :=
    Finite.exists_max (fun nu : Λ => (wordDist A.carrier 1 (g nu) : ℝ))
  refine ⟨l nu₀, B nu₁, (wordDist A.carrier 1 (g nu₂) : ℝ), hl nu₀,
    le_trans (hB nu₁) le_rfl, Nat.cast_nonneg _, ?_⟩
  intro nu
  refine ⟨?_, hnu₂ nu⟩
  intro n
  have hstep : l nu₀ * n ≤ l nu * n :=
    mul_le_mul_of_nonneg_right (hnu₀ nu) (Nat.cast_nonneg n)
  have hword : l nu * n - B nu
      ≤ (wordDist A.carrier 1 ((g nu) ^ n) : ℝ) := by
    have h := hlin nu n
    have hpt : dist (Cayley.base A) (((g nu) ^ n) • Cayley.base A)
        = (wordDist A.carrier 1 ((g nu) ^ n) : ℝ) := by
      simp [Cayley.dist_eq, Cayley.base]
    rwa [hpt] at h
  linarith [hnu₁ nu]

/-! ## The geometric leaf -/

/-- **The uniform threshold of Dahmani--Guirardel--Osin's Lemma 6.7.**

Given a closeness budget and loxodromy data for two elements, one length works
for *every* pair realising that data at every basepoint.  This is
`exists_common_zpow_of_close_orbit_endpoints_zpow` with the threshold moved in
front of `a`, `b` and `z`, which is the only difference and the whole
difficulty: that theorem builds its threshold out of exactly these numbers but
produces it after the elements are fixed. -/
def UniformCommonZpowThreshold (G : Type u) [Group G] (X : Type v)
    [PseudoMetricSpace X] [MulAction G X] : Prop :=
  ∀ E la Ba Da lb Bb Db : ℝ, ∃ T : ℝ, ∀ (a b : G) (z : X),
    (∀ n : ℕ, la * n - Ba ≤ dist z ((a ^ n) • z)) →
    dist z (a • z) ≤ Da →
    (∀ n : ℕ, lb * n - Bb ≤ dist z ((b ^ n) • z)) →
    dist z (b • z) ≤ Db →
    ∀ n m : ℤ,
      T ≤ dist z ((a ^ n) • z) → T ≤ dist z ((b ^ m) • z) →
      dist ((a ^ n) • z) ((b ^ m) • z) ≤ E →
      ∃ p r : ℤ, p ≠ 0 ∧ r ≠ 0 ∧ a ^ p = b ^ r

/-- **Model test: the quantifier order is satisfiable.**  A bounded space admits
a threshold past its own diameter, so the hypothesis never fires.  All the
content is in the unbounded case. -/
theorem uniformCommonZpowThreshold_of_bounded (G : Type u) [Group G] (X : Type v)
    [PseudoMetricSpace X] [MulAction G X] {R : ℝ} (hR : ∀ x y : X, dist x y ≤ R) :
    UniformCommonZpowThreshold G X := by
  intro _E _la _Ba _Da _lb _Bb _Db
  refine ⟨R + 1, ?_⟩
  intro a _b z _ _ _ _ n _ hn _ _
  exact absurd (hR z ((a ^ n) • z)) (by linarith)

end HullSC
end GroupApproximation
