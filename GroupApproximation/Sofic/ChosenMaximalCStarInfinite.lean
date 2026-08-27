import GroupApproximation.Analysis.MaximalCStarProperCompression
import GroupApproximation.Sofic.ChosenNonMFEndpoint
import GroupApproximation.Sofic.MarkedCompressionProperness

/-!
# The chosen presentation has a properly infinite maximal algebra

Instantiation of the strict-Kazhdan-compression endpoint for the chosen
finitely presented marked group: its maximal group C-star algebra is not
Dedekind finite, not stably finite, and carries no faithful tracial
state — in sharp contrast to its reduced algebra.

Ingredients, all from the existing literal layer: the marked-compression
inclusion data of `ChosenNonMFEndpoint` (which supplies `ι`, `t`, the
one-sided compression, and the nontrivial marked word), the strictness
conversion of `MarkedCompressionProperness` (a nontrivial marked word
certifies `ι(a) ∉ t ι(Γ) t⁻¹`), the symmetric generating Kazhdan set
from `KazhdanFiniteGeneration`, and the on-generators Kazhdan pair of
`KazhdanGenerators` — the latter at representation universe `1`, where
the maximal algebra lives.

The vertex cover's property `(T)` at representation universe `1` comes
from the universe-generalized Shalom cover
(`Shalom.exists_presented_kazhdan_cover` at target universe `w`,
stored in `CoverData.kazhdan` at `{0, 1}` and descended to `{0, 0}`
via `HasKazhdanPropertyT.of_max`).
-/

namespace GroupApproximation
namespace ChosenMaximalCStarInfinite

open ChosenMarkedPresentation ChosenNonMFEndpoint
open MaximalCStarProperCompression

noncomputable section
/-- The symmetric generating Kazhdan package for the vertex cover, with
the pair at representation universe `1`. -/
theorem exists_pair_package :
    ∃ S : Finset Vertex, ∃ ε : ℝ, 1 ∈ S ∧ (∀ g ∈ S, g⁻¹ ∈ S) ∧
      Subgroup.closure (S : Set Vertex) = ⊤ ∧ 0 < ε ∧ ε ≤ 1 ∧
      IsKazhdanPair.{0, 1} Vertex S ε := by
  obtain ⟨S, hone, hsymm, hgen⟩ :=
    KazhdanFiniteGeneration.exists_symmetric_generating_finset
      Vertex vertex_hasKazhdanPropertyT
  obtain ⟨δ, hδ⟩ := KazhdanGenerators.exists_pair_on_generators
    GroupApproximation.ChosenMarkedPresentation.vertex_hasKazhdanPropertyT_universeOne S hsymm hgen
  have hpos : 0 < min δ 1 := lt_min hδ.1 zero_lt_one
  exact ⟨S, min δ 1, hone, hsymm, hgen, hpos, min_le_right _ _,
    IsKazhdanPair.shrink hδ hpos (min_le_left _ _)⟩

/-- Strictness in mapped-subgroup form: the omitted vertex escapes the
conjugated image. -/
theorem strictness :
    ∃ a : Vertex,
      inclusionData.iota a ∉
        (inclusionData.iota.range.map
          (MulAut.conj inclusionData.t).toMonoidHom) := by
  refine ⟨inclusionData.a, fun hmem => ?_⟩
  obtain ⟨x, hx, hconj⟩ := hmem
  obtain ⟨γ, hγ⟩ := hx
  apply inclusionData.iota_a_not_in_compressed_image_of_word_ne_one
    inclusionData_word_ne_one
  exact ⟨γ, by rw [← hconj, ← hγ]; rfl⟩

/-- The strict Kazhdan compression data of the chosen presentation. -/
theorem nonempty_strictCompression :
    Nonempty (StrictKazhdanCompression Vertex MarkedGroup) := by
  obtain ⟨S, ε, hone, hsymm, hgen, hpos, hle, hpair⟩ := exists_pair_package
  obtain ⟨a, ha⟩ := strictness
  exact ⟨{ iota := inclusionData.iota
           t := inclusionData.t
           Q := S
           ε := ε
           kazhdan := hpair
           S := S
           QS := Finset.Subset.refl S
           one_mem := hone
           symm := hsymm
           eps_le := hle
           generates := hgen
           compresses := inclusionData.compresses
           strict := ⟨a, ha⟩ }⟩

/-- **The chosen finitely presented group's maximal algebra is not
Dedekind finite.** -/
theorem chosen_maximalCStar_not_isDedekindFiniteMonoid :
    ¬ IsDedekindFiniteMonoid (MaximalGroupCStar MarkedGroup) := by
  obtain ⟨D⟩ := nonempty_strictCompression
  exact D.maximalCStar_not_isDedekindFiniteMonoid

/-- **The chosen finitely presented group's maximal algebra is not stably
finite.** -/
theorem chosen_maximalCStar_not_isStablyFiniteRing :
    ¬ IsStablyFiniteRing (MaximalGroupCStar MarkedGroup) := by
  obtain ⟨D⟩ := nonempty_strictCompression
  exact D.maximalCStar_not_isStablyFiniteRing

/-- **The chosen finitely presented group's maximal algebra has no
faithful tracial state.** -/
theorem chosen_maximalCStar_no_faithfulTracialState :
    ¬ Nonempty (FaithfulTracialState (MaximalGroupCStar MarkedGroup)) := by
  obtain ⟨D⟩ := nonempty_strictCompression
  exact D.maximalCStar_no_faithfulTracialState

end

end ChosenMaximalCStarInfinite
end GroupApproximation
