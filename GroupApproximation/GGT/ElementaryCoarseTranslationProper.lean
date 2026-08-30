import GroupApproximation.GGT.ElementaryProperFromTransversal
import GroupApproximation.GGT.WPDElementaryEmbedding

/-!
# Properness of the elementary closure from coarse translation

This supplies the index-at-most-two argument left after the WPD transversal
construction.  Orientation-preserving elements occupy finitely many cosets of
the cyclic subgroup.  After fixing one orientation-reversing element, every
other reversing element differs from it by an orientation-preserving element,
with twice the coarse error.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry

universe u v

section CoarseTranslation

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-- The inverse of a coarse orientation-reversing translation is reversing
with the same error and shift. -/
theorem coarseReversing_inv (hiso : IsIsometricAction G X) {h r : G} {x : X}
    {K : ℝ} {c : ℤ}
    (hr : ∀ m : ℤ,
      dist ((r * h ^ m) • x) ((h ^ (-m + c)) • x) ≤ K) :
    ∀ m : ℤ,
      dist ((r⁻¹ * h ^ m) • x) ((h ^ (c - m)) • x) ≤ K := by
  intro m
  have hr' := hr (c - m)
  have hexp : -(c - m) + c = m := by ring
  rw [hexp] at hr'
  have hmove := hiso r⁻¹ ((r * h ^ (c - m)) • x) ((h ^ m) • x)
  calc
    dist ((r⁻¹ * h ^ m) • x) ((h ^ (c - m)) • x) =
        dist ((h ^ (c - m)) • x) ((r⁻¹ * h ^ m) • x) := dist_comm _ _
    _ = dist ((r * h ^ (c - m)) • x) ((h ^ m) • x) := by
      rw [← hmove]
      simp only [← mul_smul]
      congr 2
      group
    _ ≤ K := hr'

/-- The product of two coarse reversing translations is preserving, with the
sum of their errors. -/
theorem coarsePreserving_mul_inv_of_reversing
    (hiso : IsIsometricAction G X) {h a r : G} {x : X} {K : ℝ} {ca cr : ℤ}
    (ha : ∀ m : ℤ,
      dist ((a * h ^ m) • x) ((h ^ (-m + ca)) • x) ≤ K)
    (hr : ∀ m : ℤ,
      dist ((r * h ^ m) • x) ((h ^ (-m + cr)) • x) ≤ K) :
    ∀ m : ℤ,
      dist (((a * r⁻¹) * h ^ m) • x)
        ((h ^ (m + (ca - cr))) • x) ≤ K + K := by
  intro m
  have hri := coarseReversing_inv hiso hr m
  have hfirst := hiso a ((r⁻¹ * h ^ m) • x) ((h ^ (cr - m)) • x)
  have hfirst' :
      dist (((a * r⁻¹) * h ^ m) • x) ((a * h ^ (cr - m)) • x) ≤ K := by
    calc
      dist (((a * r⁻¹) * h ^ m) • x) ((a * h ^ (cr - m)) • x) =
          dist ((r⁻¹ * h ^ m) • x) ((h ^ (cr - m)) • x) := by
        simpa only [← mul_smul, mul_assoc] using hfirst
      _ ≤ K := hri
  have hsecond := ha (cr - m)
  have hexp : -(cr - m) + ca = m + (ca - cr) := by ring
  rw [hexp] at hsecond
  exact le_trans
    (dist_triangle _ ((a * h ^ (cr - m)) • x) _)
    (add_le_add hfirst' hsecond)

/-- If the elementary closure is the whole group, uniform coarse translation
makes the group virtually cyclic.  The reversing part contributes at most one
additional finite family of cyclic cosets. -/
theorem isVirtuallyCyclic_of_elementaryClosure_eq_top
    (hiso : IsIsometricAction G X) {h : G} {x : X}
    (hwpd : IsWPDAt h x) (hlox : IsLoxodromic h x)
    (hct : ElementaryClosureCoarseTranslation G x)
    (htop : elementaryClosure h = ⊤) : IsVirtuallyCyclic G := by
  obtain ⟨K, hK, hall⟩ := hct h hlox
  have h2K : 0 ≤ K + K := add_nonneg hK hK
  have hKle2K : K ≤ K + K := le_add_of_nonneg_right hK
  obtain ⟨F, hFfin, hF⟩ :=
    exists_finite_transversal_of_coarseTranslation hiso hwpd h2K
  by_cases hreversing : ∃ r : G, r ∈ elementaryClosure h ∧
      ∃ cr : ℤ, ∀ m : ℤ,
        dist ((r * h ^ m) • x) ((h ^ (-m + cr)) • x) ≤ K
  · obtain ⟨r, hrE, cr, hr⟩ := hreversing
    let F' : Set G := F ∪ (fun f : G => f * r) '' F
    have hF'fin : F'.Finite := hFfin.union (hFfin.image (fun f : G => f * r))
    refine isVirtuallyCyclic_of_finite_transversal (h := h) hF'fin ?_
    intro a
    have haE : a ∈ elementaryClosure h := by rw [htop]; trivial
    obtain ⟨e, ca, he, ha⟩ := hall a haE
    rcases he with rfl | rfl
    · obtain ⟨c, f, hf, haf⟩ := hF a ⟨ca, fun m =>
          le_trans (by simpa using ha m) hKle2K⟩
      exact ⟨c, f, Or.inl hf, haf⟩
    · have ha' : ∀ m : ℤ,
          dist ((a * h ^ m) • x) ((h ^ (-m + ca)) • x) ≤ K := by
        simpa using ha
      have hpres := coarsePreserving_mul_inv_of_reversing hiso ha' hr
      obtain ⟨c, f, hf, hq⟩ := hF (a * r⁻¹) ⟨ca - cr, by
        intro m
        simpa [add_assoc] using hpres m⟩
      refine ⟨c, f * r, Or.inr ⟨f, hf, rfl⟩, ?_⟩
      calc
        a = (a * r⁻¹) * r := by group
        _ = (h ^ c * f) * r := by rw [hq]
        _ = h ^ c * (f * r) := by group
  · refine isVirtuallyCyclic_of_finite_transversal (h := h) hFfin ?_
    intro a
    have haE : a ∈ elementaryClosure h := by rw [htop]; trivial
    obtain ⟨e, c, he, ha⟩ := hall a haE
    rcases he with rfl | rfl
    · exact hF a ⟨c, fun m =>
        le_trans (by simpa using ha m) hKle2K⟩
    · exfalso
      apply hreversing
      exact ⟨a, haE, c, by simpa using ha⟩

/-- The elementary closure of a loxodromic WPD element is proper in a
non-virtually-cyclic group, assuming the uniform coarse-translation lemma. -/
theorem elementaryClosure_ne_top_of_coarseTranslation
    (hiso : IsIsometricAction G X) {h : G} {x : X}
    (hwpd : IsWPDAt h x) (hlox : IsLoxodromic h x)
    (hct : ElementaryClosureCoarseTranslation G x)
    (hnvc : ¬ IsVirtuallyCyclic G) : elementaryClosure h ≠ ⊤ := by
  intro htop
  exact hnvc
    (isVirtuallyCyclic_of_elementaryClosure_eq_top hiso hwpd hlox hct htop)

end CoarseTranslation

/-! ## The named DGO obligation -/

/-- The uniform coarse-translation part of DGO Lemma 6.5, for every `(AH₃)`
datum on its given hyperbolic space. -/
def ElementaryClosureCoarseTranslationStatement : Prop :=
  ∀ (G : Type u) [Group G] (D : AH3Data.{u, u} G),
    @ElementaryClosureCoarseTranslation G _ D.Space D.metricSpace D.mulAction D.base

/-- Properness of `E(g)` is a consequence of the uniform coarse-translation
lemma and is not an additional DGO input. -/
theorem elementaryClosureProper_of_coarseTranslation
    (hct : ElementaryClosureCoarseTranslationStatement.{u}) :
    ElementaryClosureProper.{u} := by
  intro G _inst D hnvc
  letI : PseudoMetricSpace D.Space := D.metricSpace
  letI : MulAction G D.Space := D.mulAction
  exact elementaryClosure_ne_top_of_coarseTranslation D.isometric D.wpd
    D.loxodromic (hct G D) hnvc

end Elementary
end GGT
end GroupApproximation
