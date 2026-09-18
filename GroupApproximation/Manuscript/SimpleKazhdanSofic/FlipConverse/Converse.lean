import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.BoyleTomiyama
import GroupApproximation.Meta.AxiomGuard

/-!
# Flip converse, part 5: the printed sentence for topological full groups

Printed sentence (census row `2e7c7d9ab149`): *If `(X,T)` is flip conjugate to `(Y,T')`, that is,
topologically conjugate to `(Y,T')` or to `(Y,T'^{-1})`, then `G_X ≅ G_Y`, and for topological
full groups the converse holds [GPS99, Bezuglyi–Medynets].*

The forward clause for the subshift groups `G_X` is
`AbstractIntro.manuscriptSentence_flipConjugateSubshiftsIsomorphicGroups`.  This file treats the
topological full group clause.

## Forward direction (unconditional)

`manuscriptSentence_flipConjugateFullGroupsIsomorphic`: a flip conjugacy induces
`[[T]] ≅ [[S]]` (`nonempty_mulEquiv_of_flipConjugate`).

## Converse

Let `(X,T)`, `(Y,S)` be Cantor minimal systems and `Φ : [[T]] ≃* [[S]]`.

1. *Spatial realization* (GPS99 Thm 4.2 / Bezuglyi–Medynets / Matui): there is a homeomorphism
   `h : X → Y` with `Φ g = h g h⁻¹` for all `g ∈ [[T]]`.  This reconstruction of the space from
   the group (via stabilizers or maximal abelian subgroups / clopen supports) is not formalized;
   it is the single isolated hypothesis `SpatialRealizationStatement`.
2. *From a spatial isomorphism to flip conjugacy* (`flipConjugate_of_spatiallyImplemented`,
   unconditional).  Put `S' = h⁻¹ S h`, a homeomorphism of `X`.
   * `S' ∈ [[T]]`: `S' = Φ⁻¹(S)` as a homeomorphism of `X`.
   * `T ∈ [[S']]`: if `Φ(T) y = S^{n(y)} y` then `T x = h⁻¹ S^{n(h x)} h x = S'^{n(h x)} x`.
   * `T` is aperiodic (minimal on an infinite Hausdorff space: a nonempty perfect T₁ space is
     infinite) and so is `S'` (its periodic points are `h⁻¹` of periodic points of `S`).
   * By the Boyle–Tomiyama step `exists_flip_of_mem_fullGroup`, some `φ : X ≃ₜ X` satisfies
     `φ T = S' φ` or `φ T = S'⁻¹ φ`; then `ψ = h ∘ φ` gives `ψ T = S ψ` or `ψ T = S⁻¹ ψ`.
3. `manuscriptSentence_flipConjugateConverse_of_spatialRealization`: under
   `SpatialRealizationStatement`, `[[T]] ≅ [[S]] ↔ FlipConjugate T S` for Cantor minimal systems.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

/-- Spatial realization of isomorphisms of topological full groups of Cantor minimal systems
(Giordano–Putnam–Skau 1999, Bezuglyi–Medynets, Matui): every isomorphism `Φ : [[T]] ≃* [[S]]` is
`g ↦ h g h⁻¹` for a homeomorphism `h : X ≃ₜ Y`.  Literature input, not assumed anywhere except
in the `_of_spatialRealization` endpoint. -/
def SpatialRealizationStatement : Prop :=
  ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X]
    [TopologicalSpace.MetrizableSpace X] [CompactSpace Y] [T2Space Y]
    [TotallyDisconnectedSpace Y] [PerfectSpace Y] [Nonempty Y]
    [TopologicalSpace.MetrizableSpace Y] (T : X ≃ₜ X) (S : Y ≃ₜ Y),
    IsMinimalHomeo T → IsMinimalHomeo S →
      ∀ Φ : topologicalFullGroup T ≃* topologicalFullGroup S,
        ∃ h : X ≃ₜ Y, ∀ (g : topologicalFullGroup T) (x : X),
          ((Φ g : topologicalFullGroup S) : Y ≃ₜ Y) (h x) = h ((g : X ≃ₜ X) x)

theorem flipConjugate_of_spatiallyImplemented {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [T2Space X] [PerfectSpace X] [Nonempty X] [T2Space Y]
    {T : X ≃ₜ X} {S : Y ≃ₜ Y} (hT : IsMinimalHomeo T) (hS : IsMinimalHomeo S)
    (Φ : topologicalFullGroup T ≃* topologicalFullGroup S) (h : X ≃ₜ Y)
    (hΦ : ∀ (g : topologicalFullGroup T) (x : X),
      ((Φ g : topologicalFullGroup S) : Y ≃ₜ Y) (h x) = h ((g : X ≃ₜ X) x)) :
    FlipConjugate T S := by
  haveI : Infinite X := infinite_of_perfectSpace
  haveI : Infinite Y := Infinite.of_injective h.symm h.symm.injective
  have hTa : IsAperiodic T := isAperiodic_of_isMinimalHomeo hT
  have hSa : IsAperiodic S := isAperiodic_of_isMinimalHomeo hS
  obtain ⟨S', hS'⟩ : ∃ S' : X ≃ₜ X, ∀ x, h (S' x) = S (h x) :=
    ⟨(h.trans S).trans h.symm, fun x => h.apply_symm_apply (S (h x))⟩
  have hsemi : ∀ y, h.symm (S y) = S' (h.symm y) := symm_semiconj h hS'
  have hS'T : S' ∈ topologicalFullGroup T := by
    obtain ⟨gS, hgS⟩ : ∃ g : topologicalFullGroup T,
        ((Φ g : topologicalFullGroup S) : Y ≃ₜ Y) = S :=
      ⟨Φ.symm ⟨S, self_mem_topologicalFullGroup S⟩, by rw [MulEquiv.apply_symm_apply]⟩
    have hext : (gS : X ≃ₜ X) = S' := Homeomorph.ext fun x => h.injective (by
      rw [hS', ← hΦ gS x, hgS])
    rw [← hext]
    exact gS.2
  have hTS' : T ∈ topologicalFullGroup S' := by
    obtain ⟨gT, hgT⟩ : ∃ g : topologicalFullGroup T, (g : X ≃ₜ X) = T :=
      ⟨⟨T, self_mem_topologicalFullGroup T⟩, rfl⟩
    obtain ⟨n, hn, hgn⟩ := mem_topologicalFullGroup.1 (Φ gT).2
    refine mem_topologicalFullGroup.2 ⟨fun x => n (h x), hn.comp h.continuous, fun x => ?_⟩
    have h2 := hΦ gT x
    rw [hgn, hgT] at h2
    have h3 := apply_hpow_of_semiconj h.symm hsemi (n (h x)) (h x)
    rw [h2, Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply] at h3
    exact h3
  have hS'a : IsAperiodic S' := by
    intro x p hp
    have h3 := apply_hpow_of_semiconj h.symm hsemi p (h x)
    rw [Homeomorph.symm_apply_apply, hp] at h3
    have h4 := congrArg h h3
    rw [Homeomorph.apply_symm_apply] at h4
    exact hSa (h x) p h4
  have hsymm : ∀ y, h (S'.symm y) = S.symm (h y) := fun y => S.injective (by
    rw [Homeomorph.apply_symm_apply, ← hS', Homeomorph.apply_symm_apply])
  obtain ⟨φ, hφ | hφ⟩ := exists_flip_of_mem_fullGroup hT hTa hS'a hTS' hS'T
  · refine ⟨φ.trans h, Or.inl fun x => ?_⟩
    show h (φ (T x)) = S (h (φ x))
    rw [hφ, hS']
  · refine ⟨φ.trans h, Or.inr fun x => ?_⟩
    show h (φ (T x)) = S.symm (h (φ x))
    rw [hφ, hsymm]

/-- Forward clause for topological full groups: flip conjugate systems have isomorphic
topological full groups. -/
theorem manuscriptSentence_flipConjugateFullGroupsIsomorphic {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {T : X ≃ₜ X} {S : Y ≃ₜ Y} (hflip : FlipConjugate T S) :
    Nonempty (topologicalFullGroup T ≃* topologicalFullGroup S) :=
  nonempty_mulEquiv_of_flipConjugate hflip

/-- The printed converse for topological full groups of Cantor minimal systems, reduced to the
single literature input `SpatialRealizationStatement`. -/
theorem manuscriptSentence_flipConjugateConverse_of_spatialRealization
    (hsr : SpatialRealizationStatement) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X]
    [TopologicalSpace.MetrizableSpace X] [CompactSpace Y] [T2Space Y]
    [TotallyDisconnectedSpace Y] [PerfectSpace Y] [Nonempty Y]
    [TopologicalSpace.MetrizableSpace Y] {T : X ≃ₜ X} {S : Y ≃ₜ Y}
    (hT : IsMinimalHomeo T) (hS : IsMinimalHomeo S) :
    Nonempty (topologicalFullGroup T ≃* topologicalFullGroup S) ↔ FlipConjugate T S := by
  constructor
  · rintro ⟨Φ⟩
    obtain ⟨h, hh⟩ := hsr X Y T S hT hS Φ
    exact flipConjugate_of_spatiallyImplemented hT hS Φ h hh
  · exact nonempty_mulEquiv_of_flipConjugate

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_flip_of_mem_fullGroup
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.flipConjugate_of_spatiallyImplemented
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.manuscriptSentence_flipConjugateFullGroupsIsomorphic
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.manuscriptSentence_flipConjugateConverse_of_spatialRealization
