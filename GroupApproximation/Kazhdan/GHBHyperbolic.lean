import GroupApproximation.Kazhdan.GHBHyperbolicStokesLadder
import GroupApproximation.Kazhdan.CCKWCosetComplex
import GroupApproximation.Kazhdan.UnipotentSylowCounts
import GroupApproximation.Meta.AxiomGuard

/-!
# Hyperbolicity of `GHB(7)` through the linear Stokes inequality

The letters of `GHB(7)` are `a^±1, b^±1, c^±1`.  The coset complex
`CCKW.cosetComplex = CCKWTits.titsComplex (GHB 7) vertexGroup` has the cosets `gPᵢ` as
vertices.  This module supplies the complex-side inputs of
`GHBHyperbolicStokes.linearStokes_of_chainFillingBound` (H5):

* `finite_vertexGroup`: the three vertex groups are finite, being images of `U₃(7)` and
  `U₄(7)`, so their elements have word length at most some `M₀`
  (`exists_wordNorm_le_vertexGroup`);
* `cosetSection v`: a representative of the coset `v`; every representative of `v` is within
  `M₀` of it (`wordDist_cosetSection_le`);
* `letterVertex g s`: the vertex `gP₀` when `s ∈ P₀` and `gP₁` otherwise, which contains
  both `g` and `g s` for every letter `s` (`rep_letterVertex`);
* distinct cosets with a common representative are adjacent, and a triangle has a common
  representative, by the definition of the Tits complex.

`isHyperbolicGroup_ghb7_of_chainFillingBound` (H10, H11) then derives
`IsHyperbolicGroup (GHB 7)` from the area input `ChainFillingBound` for the coset complex,
at constant `6`.  That input is the composite of `Systolic.exists_leastDisc_typedLinks`, the
typed count `F ≤ 6 B` (`TypedTriangularDiscCounts`) and
`TriangulatedDisc.abs_boundarySum_le`.
-/

namespace GroupApproximation
namespace KMSGroup
namespace GHBQuotient

open WordMetric DiscreteStokes GHBHyperbolicStokes

/-- The letters `a^±1, b^±1, c^±1` of `GHB(7)`. -/
noncomputable abbrev ghbLetters : Finset (GHB 7) := presentedLetters (relators 7)

theorem isSymmetricGeneratingSet_ghbLetters :
    IsSymmetricGeneratingSet (ghbLetters : Set (GHB 7)) :=
  isSymmetricGeneratingSet_presentedLetters (relators 7)

/-! ## The vertex groups are finite -/

/-- **The vertex groups of `GHB(7)` are finite.** -/
theorem finite_vertexGroup (i : Fin 3) : (vertexGroup i : Set (GHB 7)).Finite := by
  fin_cases i
  · refine (Set.finite_range (u3ToAB 7)).subset ?_
    intro g hg
    rw [← MonoidHom.coe_range, range_u3ToAB]
    exact hg
  · refine (Set.finite_range (u4ToCB 7)).subset ?_
    intro g hg
    rw [← MonoidHom.coe_range, range_u4ToCB]
    exact hg
  · refine (Set.finite_range (u4ToCA 7)).subset ?_
    intro g hg
    rw [← MonoidHom.coe_range, range_u4ToCA]
    exact hg

/-- The elements of the vertex groups have bounded word length. -/
theorem exists_wordNorm_le_vertexGroup :
    ∃ M : ℕ, ∀ (i : Fin 3), ∀ p ∈ vertexGroup i, wordNorm (ghbLetters : Set (GHB 7)) p ≤ M := by
  have h : ∀ i : Fin 3, ∃ M : ℕ, ∀ p ∈ vertexGroup i,
      wordNorm (ghbLetters : Set (GHB 7)) p ≤ M := by
    intro i
    obtain ⟨M, hM⟩ := ((finite_vertexGroup i).image (wordNorm (ghbLetters : Set (GHB 7)))).bddAbove
    exact ⟨M, fun p hp => hM ⟨p, hp, rfl⟩⟩
  choose M hM using h
  refine ⟨∑ j, M j, fun i p hp => (hM i p hp).trans ?_⟩
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (M j)) (Finset.mem_univ i)

/-! ## Sections and letter vertices -/

/-- A representative of a coset of a vertex group. -/
noncomputable def cosetSection (v : CCKW.Vertex) : GHB 7 :=
  Classical.choose (CCKWTits.exists_rep v)

theorem rep_cosetSection (v : CCKW.Vertex) :
    CCKWTits.Rep vertexGroup v (cosetSection v) :=
  Classical.choose_spec (CCKWTits.exists_rep v)

/-- **H5.**  Every representative of a coset is within `M₀` of the chosen section. -/
theorem wordDist_cosetSection_le {M : ℕ}
    (hM : ∀ (i : Fin 3), ∀ p ∈ vertexGroup i, wordNorm (ghbLetters : Set (GHB 7)) p ≤ M)
    {g : GHB 7} {v : CCKW.Vertex} (hg : CCKWTits.Rep vertexGroup v g) :
    wordDist (ghbLetters : Set (GHB 7)) g (cosetSection v) ≤ M :=
  hM v.1 _ (CCKWTits.mem_of_rep_rep hg (rep_cosetSection v))

/-- Every letter lies in `P₀ = ⟨a,b⟩` or in `P₁ = ⟨c,b⟩`. -/
theorem mem_vertexGroup_of_mem_ghbLetters {s : GHB 7} (hs : s ∈ (ghbLetters : Set (GHB 7))) :
    s ∈ vertexGroup 0 ∨ s ∈ vertexGroup 1 := by
  obtain ⟨⟨i, bb⟩, rfl⟩ := mem_presentedLetters.mp (Finset.mem_coe.mp hs)
  have ha : (PresentedGroup.of 0 : GHB 7) ∈ vertexGroup 0 :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : (PresentedGroup.of 1 : GHB 7) ∈ vertexGroup 0 :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hc : (PresentedGroup.of 2 : GHB 7) ∈ vertexGroup 1 :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  fin_cases i <;> cases bb
  · exact Or.inl (Subgroup.inv_mem _ ha)
  · exact Or.inl ha
  · exact Or.inl (Subgroup.inv_mem _ hb)
  · exact Or.inl hb
  · exact Or.inr (Subgroup.inv_mem _ hc)
  · exact Or.inr hc

open Classical in
/-- The vertex containing the step `g → g s`: `gP₀` for `s ∈ P₀`, otherwise `gP₁`. -/
noncomputable def letterVertex (g s : GHB 7) : CCKW.Vertex :=
  if s ∈ vertexGroup 0 then CCKWTits.vtx vertexGroup 0 g else CCKWTits.vtx vertexGroup 1 g

/-- The letter vertex contains both ends of its step. -/
theorem rep_letterVertex (g s : GHB 7) (hs : s ∈ (ghbLetters : Set (GHB 7))) :
    CCKWTits.Rep vertexGroup (letterVertex g s) g ∧
      CCKWTits.Rep vertexGroup (letterVertex g s) (g * s) := by
  unfold letterVertex
  split_ifs with h
  · exact ⟨CCKWTits.rep_vtx 0 g, CCKWTits.rep_mul (CCKWTits.rep_vtx 0 g) h⟩
  · exact ⟨CCKWTits.rep_vtx 1 g, CCKWTits.rep_mul (CCKWTits.rep_vtx 1 g)
      ((mem_vertexGroup_of_mem_ghbLetters hs).resolve_left h)⟩

/-! ## The endpoint -/

/-- **H10.**  The area input for the coset complex gives the linear Stokes inequality for the
letters of `GHB(7)`. -/
theorem linearStokes_ghb7_of_chainFillingBound
    (hfill : ChainFillingBound CCKW.cosetComplex.G.Adj CCKW.cosetComplex.Tri 6) :
    ∃ K : ℕ, LinearStokes (ghbLetters : Set (GHB 7)) K := by
  classical
  obtain ⟨M, hM⟩ := exists_wordNorm_le_vertexGroup
  exact ⟨_, linearStokes_of_chainFillingBound isSymmetricGeneratingSet_ghbLetters hfill
    (fun g v => CCKWTits.Rep vertexGroup v g) cosetSection
    (fun _ _ hg => wordDist_cosetSection_le hM hg)
    (fun _ _ _ hv hw hne => CCKWTits.adj_of_rep_ne hv hw hne)
    (fun _ _ _ h => by
      obtain ⟨-, -, -, g, hx, hy, hz⟩ := h
      exact ⟨g, hx, hy, hz⟩)
    letterVertex rep_letterVertex⟩

/-- **H11.**  The area input for the coset complex makes `GHB(7)` hyperbolic. -/
theorem isHyperbolicGroup_ghb7_of_chainFillingBound
    (hfill : ChainFillingBound CCKW.cosetComplex.G.Adj CCKW.cosetComplex.Tri 6) :
    Hyperbolic.IsHyperbolicGroup (GHB 7) := by
  obtain ⟨K, hK⟩ := linearStokes_ghb7_of_chainFillingBound hfill
  exact isHyperbolicGroup_of_linearStokes isSymmetricGeneratingSet_ghbLetters hK

end GHBQuotient
end KMSGroup
end GroupApproximation

#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.finite_vertexGroup
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.rep_letterVertex
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.linearStokes_ghb7_of_chainFillingBound
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.isHyperbolicGroup_ghb7_of_chainFillingBound
