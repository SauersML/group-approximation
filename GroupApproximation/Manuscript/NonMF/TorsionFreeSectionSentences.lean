import GroupApproximation.Manuscript.NonMF.TorsionFreeLeafAssembly
import GroupApproximation.Meta.AxiomGuard

/-!
# Sentence carriers for `sec:torsion-free` at the current print

`non_mf_groups_exist.tex`, Section `sec:torsion-free` (tex lines 1621–1737), as
printed since 73c867c5b.  `TorsionFreePrintedSentences` carries the section's
proof sentences at an earlier print, which quantified over a finite set `Ω`,
applied `thm:hull` "with the set `Ω`" and `lem:saturation` "to `G₀`, `N`, and
`Ω = ∅`", and cited Hull's Theorem 7.1 through the package
`HullSmallCancellationPrinted`.  The current print has no finite set, adds the
paragraph after `thm:hull` on the shape of Hull's proof, and says that `N₀` is
suitable "with respect to a generating set `A' ⊇ A` to which Hull's small
cancellation theorem again applies".  This module carries those sentences.

Every sentence that rests on Hull's Theorem 7.1 is stated over the two named
Hull leaves of `TorsionFreeLeafAssembly` —
`GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement` and
`HullSC.RelativeIsoperimetricBridgeQuasiGeodesicStatement` — as hypotheses of
the carrier, never a literature package.  Sentences that do not rest on it are
closed.

`thm:hull` itself is printed for every acylindrically hyperbolic `G`; the proved
chain reaches it at a torsion-free `G`, the only case `lem:saturation` uses.
`PrintedHullSmallCancellationCurrent` records the printed statement in full, and
`manuscriptSentence_hullTheoremTorsionFree_of_leaves` is the torsion-free case.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeSectionSentences

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted
open GroupApproximation.Manuscript.NonMF.HullCorrectedInputs
open GroupApproximation.Manuscript.NonMF.TorsionFreeLeafAssembly

universe u

/-! ## `thm:hull` -/

/-- **`thm:hull`, exactly as printed** (tex line 1636).

> Let `G` be acylindrically hyperbolic, let `N ≤ G` be suitable with respect to
> `A`, and let `g₁,…,g_m ∈ G`.  Then there is a surjective homomorphism
> `φ : G → Q` such that `Q` is acylindrically hyperbolic, `φ(gᵢ) ∈ φ(N)` for all
> `i`, and every element of finite order in `Q` is the image of an element of
> the same order in `G`.

The conclusion is `HullQuotient` at the empty set, whose injectivity field is
then the empty statement: the four remaining fields are the four printed
clauses. -/
def PrintedHullSmallCancellationCurrent : Prop :=
  ∀ {G : Type u} [Group G] [IsAcylindricallyHyperbolic G] (A : HullGeneratingSet G)
    {N : Subgroup G}, Suitable A.alphabet N → ∀ {m : ℕ} (g : Fin m → G),
      Nonempty (HullQuotient N g (∅ : Set G))

/-- The earlier, finite-set-carrying form of the citation implies the current
print: take the finite set empty and forget the kernel datum. -/
theorem printedHullSmallCancellationCurrent_of_printed
    (h : HullSmallCancellationPrinted.{u}) : PrintedHullSmallCancellationCurrent.{u} := by
  intro G _ _ A N hN m g
  obtain ⟨H⟩ := h A hN g Set.finite_empty
  exact ⟨H.quotient⟩

/-- **`thm:hull` at a torsion-free acylindrically hyperbolic group**, the case
`lem:saturation` applies it in, from the two Hull leaves. -/
theorem manuscriptSentence_hullTheoremTorsionFree_of_leaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicStatement.{0, 0, 0}) :
    ∀ {G : Type} [Group G] [IsAcylindricallyHyperbolic G], IsPowerTorsionFree G →
      ∀ (A : HullGeneratingSet G) {N : Subgroup G}, Suitable A.alphabet N →
        ∀ {m : ℕ} (g : Fin m → G), Nonempty (HullQuotient N g (∅ : Set G)) := by
  intro G _ _ hG A N hN m g
  obtain ⟨H⟩ :=
    hullSmallCancellationTorsionFreePrinted_of_leaves hgreendlinger hbridge
      hG A hN g
  exact ⟨H.quotient⟩

/-! ## The paragraph after `thm:hull` (tex lines 1644–1648) -/

/-- **"Hull's proof treats `m = 1` by passing to `G/⟨⟨r⟩⟩_G` for one element
`r` …"**

At one target the quotient of Hull's construction has kernel the normal
closure of a single element `r`, and the quotient *is* `G/⟨⟨r⟩⟩_G`.  The kernel
datum of the one-step construction is a finset of at most one element; the empty
case is `r = 1`. -/
theorem manuscriptSentence_hullOneTargetOneRelator_of_leaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicStatement.{0, 0, 0})
    {G : Type} [Group G] (hG : IsPowerTorsionFree G) (A : HullGeneratingSet G)
    {N : Subgroup G} (hN : Suitable A.alphabet N) (t : G) :
    ∃ (s : HullSC.HullTower A N (fun j : Fin 0 => Fin.elim0 j) (fun _ : Fin 1 => t) 0)
      (r : G), s.step.q.ker = Subgroup.normalClosure ({r} : Set G) ∧
        Nonempty (G ⧸ Subgroup.normalClosure ({r} : Set G) ≃* s.step.Q) := by
  have hOne := hullOneStep_of_leaves hgreendlinger hbridge
  obtain ⟨s⟩ := hOne (k := 0) (S := fun j : Fin 0 => Fin.elim0 j) hG A hN
    (fun j : Fin 0 => Fin.elim0 j) t 0
  obtain ⟨T, hTcard, hTker⟩ := s.kerNormallyGenerated
  obtain ⟨x, hx⟩ := Finset.card_le_one_iff_subset_singleton.mp hTcard
  have hr : ∃ r : G,
      Subgroup.normalClosure (T : Set G) = Subgroup.normalClosure ({r} : Set G) := by
    rcases Finset.subset_singleton_iff.mp hx with rfl | rfl
    · refine ⟨1, ?_⟩
      rw [Finset.coe_empty,
        Subgroup.normalClosure_eq_bot_iff.mpr (Set.empty_subset _),
        Subgroup.normalClosure_eq_bot_iff.mpr Set.Subset.rfl]
    · exact ⟨x, by rw [Finset.coe_singleton]⟩
  obtain ⟨r, hrT⟩ := hr
  have hker : s.step.q.ker = Subgroup.normalClosure ({r} : Set G) := hTker.trans hrT
  exact ⟨s, r, hker, ⟨(QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective (φ := s.step.q) s.step.surjective)⟩⟩

/-- **"… and the general case by induction on `m`, using his clause (d), that
`φ(N)` is again suitable"** (Hull, proof of Theorem 7.1).

The induction is `HullSC.hullTower_of_oneStep`; clause (d) is the
`suitable_map` field of each step, which is what lets the next step be applied
to the image of `N`, and it survives the composite. -/
theorem manuscriptSentence_hullInductionOnTargets_of_leaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicStatement.{0, 0, 0})
    (m : ℕ) {G : Type} [Group G] (A : HullGeneratingSet G) (hG : IsPowerTorsionFree G)
    {N : Subgroup G} (hN : Suitable A.alphabet N) (t : Fin m → G) (R : ℕ) :
    ∃ s : HullSC.HullTower A N (fun j : Fin 0 => Fin.elim0 j) t R,
      Suitable s.step.hullSet.alphabet (N.map s.step.q) := by
  obtain ⟨s⟩ := HullSC.hullTower_of_oneStep
    (hullOneStep_of_leaves hgreendlinger hbridge) m A hG hN
    (k := 0) (S := fun j : Fin 0 => Fin.elim0 j) (fun j : Fin 0 => Fin.elim0 j) t R
  exact ⟨s, s.step.suitable_map⟩

/-- **"… so `ker φ` is the normal closure of `m` elements and `Q` is finitely
presented when `G` is."**

Both clauses, for the quotient Hull's induction produces: its kernel datum, and
finite presentation of a quotient of a finitely presented group by the normal
closure of a finite set. -/
theorem manuscriptSentence_hullKernelRemark {G : Type} [Group G]
    {A : HullGeneratingSet G} {N : Subgroup G} {k : ℕ} {S : Fin k → Subgroup G}
    {m : ℕ} {t : Fin m → G} {R : ℕ} (s : HullSC.HullTower A N S t R) :
    (∃ T : Finset G, T.card ≤ m ∧ s.step.q.ker = Subgroup.normalClosure (T : Set G)) ∧
      (Group.IsFinitelyPresented G → Group.IsFinitelyPresented s.step.Q) := by
  refine ⟨s.kerNormallyGenerated, fun hfp => ?_⟩
  haveI := hfp
  obtain ⟨T, -, hker⟩ := s.kerNormallyGenerated
  exact Group.IsFinitelyPresented.of_surjective s.step.q s.step.surjective
    ⟨(T : Set G), T.finite_toSet, hker.symm⟩

/-! ## The proof of `lem:saturation` (tex lines 1658–1673) -/

/-- **"By Hull [Corollary 5.7 and Lemma 5.8], `N` contains two elements
`h₁,h₂` such that `N₀ = ⟨h₁,h₂⟩` is suitable with respect to a generating set
`A' ⊇ A` to which Hull's small cancellation theorem again applies."**

Over a torsion-free ambient group the pair is a theorem with `A' = A`
(`hullSuitablePair_of_torsionFree`); the last clause is `thm:hull` at `A'`, from
the two Hull leaves. -/
theorem manuscriptSentence_saturationPairAndHullAgain_of_leaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicStatement.{0, 0, 0})
    {G : Type} [Group G] [IsAcylindricallyHyperbolic G] (hG : IsPowerTorsionFree G)
    (A : HullGeneratingSet G) {N : Subgroup G} (hN : Suitable A.alphabet N) :
    ∃ A' : HullGeneratingSet G, A.alphabet.carrier ⊆ A'.alphabet.carrier ∧
      ∃ h₁ ∈ N, ∃ h₂ ∈ N,
        Suitable A'.alphabet (Subgroup.closure ({h₁, h₂} : Set G)) ∧
          ∀ {m : ℕ} (g : Fin m → G),
            Nonempty (HullQuotientNG (Subgroup.closure ({h₁, h₂} : Set G)) g
              (∅ : Set G)) := by
  obtain ⟨A', hA', h₁, hh₁, h₂, hh₂, hsuit⟩ := hullSuitablePair_of_torsionFree hG A hN
  exact ⟨A', hA', h₁, hh₁, h₂, hh₂, hsuit, fun g =>
    hullSmallCancellationTorsionFreePrinted_of_leaves hgreendlinger hbridge
      hG A' hsuit g⟩

/-- **"Apply Theorem `thm:hull` to `N₀`, with respect to `A'`, with
`g₁,…,g_m` a finite generating set of `G`."**

The finite generating family comes from finite presentation; the application is
`thm:hull` at a torsion-free group, from the two Hull leaves, with its kernel
datum. -/
theorem manuscriptSentence_saturationApplyHullNoOmega_of_leaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicStatement.{0, 0, 0})
    {G : Type} [Group G] [Group.IsFinitelyPresented G] [IsAcylindricallyHyperbolic G]
    (hG : IsPowerTorsionFree G) (A' : HullGeneratingSet G) {N₀ : Subgroup G}
    (hN₀ : Suitable A'.alphabet N₀) :
    ∃ (m : ℕ) (g : Fin m → G), Subgroup.closure (Set.range g) = ⊤ ∧
      Nonempty (HullQuotientNG N₀ g (∅ : Set G)) := by
  obtain ⟨m, g, htop⟩ := exists_finite_generating_family G
  exact ⟨m, g, htop,
    hullSmallCancellationTorsionFreePrinted_of_leaves hgreendlinger hbridge
      hG A' hN₀ g⟩

/-! ## The proof of `thm:torsion-free` (tex lines 1696–1716) -/

/-- **"By Lemma `lem:saturation` applied to `G₀` and `N`, there is a surjective
homomorphism `φ : G₀ → Q` with `Q` two-generated, finitely presented,
torsion-free, and acylindrically hyperbolic, and `φ(N) = Q`."**

Every printed clause is a field of `SaturationQuotient`; the lemma is applied as
printed, with no finite set. -/
theorem manuscriptSentence_theoremApplySaturationNoOmega_of_leaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicStatement.{0, 0, 0})
    {G₀ : Type} [Group G₀] [Group.IsFinitelyPresented G₀] [IsAcylindricallyHyperbolic G₀]
    (hG₀ : IsPowerTorsionFree G₀) (N : Subgroup G₀) [N.Normal] (hN : N ≠ ⊥) :
    Nonempty (SaturationQuotient N (∅ : Set G₀)) :=
  printedSaturationNoOmega_of_leaves hgreendlinger hbridge G₀ hG₀ N hN

end TorsionFreeSectionSentences
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentences.printedHullSmallCancellationCurrent_of_printed
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentences.manuscriptSentence_hullTheoremTorsionFree_of_leaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentences.manuscriptSentence_hullOneTargetOneRelator_of_leaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentences.manuscriptSentence_hullInductionOnTargets_of_leaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentences.manuscriptSentence_hullKernelRemark
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentences.manuscriptSentence_saturationPairAndHullAgain_of_leaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentences.manuscriptSentence_saturationApplyHullNoOmega_of_leaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentences.manuscriptSentence_theoremApplySaturationNoOmega_of_leaves
