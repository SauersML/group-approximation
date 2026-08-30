import GroupApproximation.GGT.ElementaryCoarseTranslationQuasiconvex

/-!
# The algebraic finish of DGO Lemma 6.7

For one elementary closure, the geometric heart of DGO Lemma 6.7 is that a
sufficiently long coarse overlap between `E(h) • x` and `g E(h) • x` forces
`g` to conjugate a nonzero power of `h` to another nonzero power.  The latter
equation is exactly membership in `E(h)`.  This file separates and proves that
algebraic finish, leaving only the long-overlap-to-common-power implication as
geometry.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-- The geometric core of DGO Lemma 6.7 at one basepoint: a sufficiently large
coarse overlap of an elementary-closure orbit with a translate forces a
conjugate common nonzero power. -/
def DiameterForcesConjugatePowerAt (h : G) (x : X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ g : G,
    (∀ D : ℝ, D < R → ∃ a b : G,
      a ∈ elementaryClosure h ∧ b ∈ elementaryClosure h ∧
      D ≤ dist (a • x) (b • x) ∧
      (∃ c : G, c ∈ elementaryClosure h ∧
        dist (a • x) ((g * c) • x) ≤ ε) ∧
      (∃ c : G, c ∈ elementaryClosure h ∧
        dist (b • x) ((g * c) • x) ≤ ε)) →
    ∃ p q : ℤ, p ≠ 0 ∧ q ≠ 0 ∧ g * h ^ p * g⁻¹ = h ^ q

/-- The common-power conclusion is exactly the conclusion required by
geometric separation for a single elementary closure. -/
theorem geometricallySeparatedAt_elementaryClosure_of_diameterForcesConjugatePower
    {h : G} {x : X} (hpower : DiameterForcesConjugatePowerAt h x) :
    GeometricallySeparatedAt (elementaryClosure h) x := by
  intro ε hε
  obtain ⟨R, hR, hforce⟩ := hpower ε hε
  refine ⟨R, hR, ?_⟩
  intro g hdiam
  obtain ⟨p, q, hp, hq, heq⟩ := hforce g hdiam
  exact mem_elementaryClosure.mpr ⟨p, q, hp, hq, heq⟩

end Elementary
end GGT
end GroupApproximation
