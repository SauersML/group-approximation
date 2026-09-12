import GroupApproximation.Analysis.MaximalCStarKazhdanProjection
import GroupApproximation.Analysis.MaximalCStarKazhdanAverage
import GroupApproximation.Analysis.MaximalGroupCStarTrace
import GroupApproximation.Analysis.UnitaryAverageFixedVector
import GroupApproximation.Meta.AxiomGuard

/-!
# The Kazhdan projection `e_L ∈ C*_max(L)`

`non_mf_groups_exist.tex`, Section 2 (tex lines 451-454 at 73c867c5b):

> For a group `L` with property (T), the Kazhdan projection is the central
> projection `e_L ∈ C*_max(L)` whose image in every unitary representation of
> `L` is the orthogonal projection onto the `L`-invariant vectors [AkemannWalter].

The census graded this sentence `attribution`.  It asserts the existence of an
object with three properties, and the paper uses all three, so it is carried
here as a theorem with no literature input:

* `e_L` is a star projection of `C*_max(L)` (`KazhdanData.projection`, the
  spectral projection of the orbit average above the Kazhdan rate);
* `e_L` is central: it absorbs every canonical unitary on both sides, and the
  two continuous linear maps `x ↦ x e_L`, `x ↦ e_L x` then agree by density of
  `ℂ[L]`;
* for **every** unitary representation `ρ` of `L` on a Hilbert space `E`, in
  every universe, the image of `e_L` under the induced `⋆`-homomorphism is a
  star projection whose fixed vectors are exactly the `ρ(L)`-invariant vectors.
  The spectral gap of the image of the orbit average is inherited from `C*_max(L)`
  (a unital homomorphism shrinks the spectrum), so no Kazhdan pair at the
  universe of `E` is needed.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences

open MaximalCStarKazhdanProjection AbstractSpectralGap CStarSpectralProjection

noncomputable section

universe u v

/-- **The Kazhdan projection is central.** -/
theorem kazhdanProjection_central {L : Type u} [Group L] (KD : KazhdanData L)
    (x : MaximalGroupCStar L) : x * KD.projection = KD.projection * x := by
  have hgen : ∀ g : L, maximalGroupCStarGenerator L g * KD.projection
      = KD.projection * maximalGroupCStarGenerator L g := by
    intro g
    have h1 : maximalGroupCStarGenerator L g * KD.projection = KD.projection :=
      KD.generator_mul_projection g
    have h2 : maximalGroupCStarGenerator L g⁻¹ * KD.projection = KD.projection :=
      KD.generator_mul_projection g⁻¹
    have h3 : KD.projection * maximalGroupCStarGenerator L g = KD.projection := by
      have h := congrArg star h2
      rwa [star_mul, KD.isSelfAdjoint_projection.star_eq,
        star_maximalGroupCStarGenerator, inv_inv] at h
    rw [h1, h3]
  have hext : (ContinuousLinearMap.mul ℂ (MaximalGroupCStar L)).flip KD.projection
      = ContinuousLinearMap.mul ℂ (MaximalGroupCStar L) KD.projection :=
    maximalGroupCStar_ext_of_generator L fun g ↦ by
      simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply']
        using hgen g
  exact congrArg (fun F : MaximalGroupCStar L →L[ℂ] MaximalGroupCStar L ↦ F x) hext

/-- **The printed sentence (tex lines 451-454), every clause.**  For every group
`L` with property (T) there is a central star projection `e_L ∈ C*_max(L)` such
that, for every unitary representation `ρ` of `L` on a Hilbert space `E` and the
induced `⋆`-homomorphism `f : C*_max(L) → B(E)`, `f(e_L)` is a star projection
fixing exactly the `ρ(L)`-invariant vectors, i.e. the orthogonal projection onto
them. -/
def PrintedKazhdanProjection : Prop :=
  ∀ (L : Type u) [Group L], HasKazhdanPropertyT.{u, u} L →
    ∃ e : MaximalGroupCStar L, IsStarProjection e ∧
      (∀ x : MaximalGroupCStar L, x * e = e * x) ∧
      ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
        (ρ : L →* unitary (E →L[ℂ] E)) (f : MaximalGroupCStar L →⋆ₐ[ℂ] (E →L[ℂ] E)),
        (∀ l : L, f (maximalGroupCStarGenerator L l)
          = ((ρ l : unitary (E →L[ℂ] E)) : E →L[ℂ] E)) →
          IsStarProjection (f e) ∧
            ∀ x : E, f e x = x ↔
              ∀ l : L, ((ρ l : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x = x

theorem manuscriptSentence_kazhdanProjection : PrintedKazhdanProjection.{u, v} := by
  intro L _ hT
  obtain ⟨KD⟩ := exists_kazhdanData L hT
  refine ⟨KD.projection, ⟨KD.projection_mul_projection, KD.isSelfAdjoint_projection⟩,
    kazhdanProjection_central KD, ?_⟩
  intro E _ _ _ ρ f hf
  have hgap : ∀ mu ∈ spectrum ℝ (unitaryAverage ρ KD.S), mu ≤ KD.rate ∨ mu = 1 := by
    intro mu hmu
    rw [← image_average KD ρ f hf] at hmu
    exact KD.gap mu
      (AlgHom.spectrum_apply_subset (f.toAlgHom.restrictScalars ℝ) KD.average hmu)
  have himage : f KD.projection = spectralProjection (unitaryAverage ρ KD.S) KD.rate :=
    image_eq_spectralProjection KD ρ f hf hgap
  refine ⟨isStarProjection_image KD f, fun x ↦ ?_⟩
  rw [himage]
  have hset := UnitaryAverageFixedVector.spectralProjection_apply_eq_self_iff
    ρ ⟨1, KD.one_mem⟩ KD.symm KD.rate_lt_one hgap x
  constructor
  · intro hx l
    have hxS : ∀ g ∈ (KD.S : Set L),
        ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x = x :=
      fun g hg ↦ hset.mp hx g (Finset.mem_coe.1 hg)
    have hl : l ∈ Subgroup.closure (KD.S : Set L) := by
      rw [KD.generates]
      trivial
    exact UnitaryAverageFixedVector.apply_eq_self_of_mem_closure ρ hxS hl
  · intro hx
    exact hset.mpr fun g _ ↦ hx g

end

end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  Manuscript.NonMFSentences.kazhdanProjection_central
#audit_closed_axioms
  Manuscript.NonMFSentences.manuscriptSentence_kazhdanProjection
