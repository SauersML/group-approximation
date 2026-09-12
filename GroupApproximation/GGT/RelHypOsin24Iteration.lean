import GroupApproximation.GGT.RelHypOsin24Construction
import GroupApproximation.GGT.HullSC

/-!
# Iterating the one-target form of Osin's Theorem 2.4

Osin constructs one small-cancellation relation for each prescribed target.
The geometric argument is therefore a one-target statement, while the printed
theorem quantifies over a finite set.  This module proves the finite induction.

`Osin24SingletonStepStatement` is strictly smaller than Theorem 2.4: it treats
one target and asks only for the same quotient conclusions at that singleton.
Its identity model is proved when the target already belongs to the suitable
subgroup.  The induction composes quotient maps.  Relative hyperbolicity,
peripheral injectivity, suitability, and torsion lifting all compose directly.
For the finite-presentation clause, `HullSC.ker_comp_eq` shows that finite
normal generating sets for two successive kernels lift to a finite normal
generating set for the composite kernel.

Thus the only geometric task left after this module is the literal one-relator
Hull specialization.  No simultaneous relator family is postulated here.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

/-! ## The singleton interface and its identity model -/

/-- The one-target form of Osin's quotient theorem, including the kernel
clause read from the construction. -/
def Osin24SingletonStepStatement : Prop :=
  ∀ (G : Type) (_ : Group G) (ι : Type) (Hfam : ι → Subgroup G),
    IsRelativelyHyperbolic G Hfam →
      ∀ H : Subgroup G, IsSuitableSubgroup Hfam H → ∀ t : G,
        ∃ (Q : Type) (_ : Group Q) (eta : G →* Q),
          IsOsin24Quotient Hfam H ({t} : Set G) Q eta ∧
            eta.ker.IsFinitelyNormallyGenerated

/-- If the target already lies in `H`, the identity quotient is a genuine
model of the singleton conclusion.  This checks that the interface is not
made inconsistent by its peripheral and kernel clauses. -/
theorem osin24SingletonStep_identityModel
    {G : Type} [Group G] {ι : Type} (Hfam : ι → Subgroup G)
    (hrel : IsRelativelyHyperbolic G Hfam) (H : Subgroup G)
    (hsuit : IsSuitableSubgroup Hfam H) {t : G} (ht : t ∈ H) :
    IsOsin24Quotient Hfam H ({t} : Set G) G (MonoidHom.id G) ∧
      (MonoidHom.id G).ker.IsFinitelyNormallyGenerated := by
  have hrelative : IsOsin24RelativeQuotientConclusion Hfam (MonoidHom.id G) :=
    isOsin24RelativeQuotientConclusion_id Hfam hrel
  have hsuitable : IsOsin24SuitabilityConclusion Hfam H (MonoidHom.id G) :=
    isOsin24SuitabilityConclusion_id Hfam H hsuit
  have htorsion : IsOsin24TorsionConclusion (MonoidHom.id G) :=
    isOsin24TorsionConclusion_id
  obtain ⟨hrelQ, hinj⟩ := hrelative
  refine ⟨⟨fun q => ⟨q, rfl⟩, hrelQ, ?_, hinj, hsuitable, htorsion⟩, ?_⟩
  · intro x hx
    have hxt : x = t := Set.mem_singleton_iff.mp hx
    subst x
    exact Subgroup.mem_map_of_mem (MonoidHom.id G) ht
  · have hker : (MonoidHom.id G).ker = ⊥ := MonoidHom.ker_id
    rw [hker]
    exact Subgroup.IsFinitelyNormallyGenerated.bot

/-! ## Finite normal generation under composition -/

/-- Finite normal generation of kernels is closed under composition when the
first map is surjective.  A finite generating set for the second kernel is
lifted along a chosen section of the first map. -/
theorem ker_comp_isFinitelyNormallyGenerated
    {G Q P : Type} [Group G] [Group Q] [Group P]
    (phi : G →* Q) (hphi : Function.Surjective phi) (psi : Q →* P)
    (hkerPhi : phi.ker.IsFinitelyNormallyGenerated)
    (hkerPsi : psi.ker.IsFinitelyNormallyGenerated) :
    (psi.comp phi).ker.IsFinitelyNormallyGenerated := by
  obtain ⟨s, hsfinite, hs⟩ := hkerPhi
  obtain ⟨u, hufinite, hu⟩ := hkerPsi
  have hsurj : Function.Surjective phi := hphi
  choose sigma hsigma using hsurj
  let r : Set G := s ∪ sigma '' u
  have hrfinite : r.Finite := hsfinite.union (hufinite.image sigma)
  refine ⟨r, hrfinite, ?_⟩
  symm
  apply HullSC.ker_comp_eq phi hphi psi s u r hs.symm hu.symm
  · exact Set.subset_union_left
  · intro v hv
    exact ⟨sigma v, Set.mem_union_right _ ⟨v, hv, rfl⟩, hsigma v⟩
  · intro y hy
    rcases hy with hy | hy
    · have hphiOne : phi y = 1 := by
        rw [← MonoidHom.mem_ker, ← hs]
        exact Subgroup.subset_normalClosure hy
      rw [hphiOne, map_one]
    · obtain ⟨v, hv, rfl⟩ := hy
      rw [hsigma v, ← MonoidHom.mem_ker, ← hu]
      exact Subgroup.subset_normalClosure hv

/-! ## Composition of the five quotient clauses -/

/-- Two successive Osin quotients compose.  The second step is applied to the
mapped peripheral family and suitable subgroup, at the image of one new
target. -/
theorem isOsin24Quotient_comp_insert
    {G Q P : Type} [Group G] [Group Q] [Group P] {ι : Type}
    (Hfam : ι → Subgroup G) (H : Subgroup G) (s : Set G) (t : G)
    (phi : G →* Q) (psi : Q →* P)
    (hphi : IsOsin24Quotient Hfam H s Q phi)
    (hpsi : IsOsin24Quotient (fun l => (Hfam l).map phi) (H.map phi)
      ({phi t} : Set Q) P psi) :
    IsOsin24Quotient Hfam H (insert t s) P (psi.comp phi) := by
  obtain ⟨hphiSurj, hphiRel, hphiTarget, hphiInj, hphiSuit, hphiTorsion⟩ := hphi
  obtain ⟨hpsiSurj, hpsiRel, hpsiTarget, hpsiInj, hpsiSuit, hpsiTorsion⟩ := hpsi
  refine ⟨hpsiSurj.comp hphiSurj, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Subgroup.map_map] using hpsiRel
  · intro x hx
    rcases hx with hxt | hx
    · have ht := hpsiTarget (phi t) (Set.mem_singleton (phi t))
      subst x
      simpa only [MonoidHom.comp_apply, Subgroup.map_map] using ht
    · have hxmap : phi x ∈ H.map phi := hphiTarget x hx
      have hxmapped : psi (phi x) ∈ (H.map phi).map psi :=
        Subgroup.mem_map_of_mem psi hxmap
      simpa only [MonoidHom.comp_apply, Subgroup.map_map] using hxmapped
  · intro x hx y hy hxy
    have hphiX : phi x ∈ ⋃ l, (((Hfam l).map phi : Subgroup Q) : Set Q) := by
      obtain ⟨l, hxl⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨l, Subgroup.mem_map_of_mem phi hxl⟩
    have hphiY : phi y ∈ ⋃ l, (((Hfam l).map phi : Subgroup Q) : Set Q) := by
      obtain ⟨l, hyl⟩ := Set.mem_iUnion.mp hy
      exact Set.mem_iUnion.mpr ⟨l, Subgroup.mem_map_of_mem phi hyl⟩
    have hxyPhi : phi x = phi y := hpsiInj hphiX hphiY hxy
    exact hphiInj hx hy hxyPhi
  · simpa only [Subgroup.map_map] using hpsiSuit
  · intro p hp
    obtain ⟨q, hqfinite, hqmap⟩ := hpsiTorsion p hp
    obtain ⟨g, hgfinite, hgmap⟩ := hphiTorsion q hqfinite
    exact ⟨g, hgfinite, by rw [MonoidHom.comp_apply, hgmap, hqmap]⟩

/-! ## The finite induction -/

/-- The singleton step implies Osin's finite-presentation addendum by finite
induction, one actual quotient map per target. -/
theorem osinTheorem24FinitePresentationAddendum_of_singletonStep
    (hstep : Osin24SingletonStepStatement) :
    OsinTheorem24FinitePresentationAddendum := by
  intro G instG ι Hfam hrel H hsuit t ht
  letI : Group G := instG
  classical
  have hind : ∀ s : Finset G,
      ∃ (Q : Type) (_ : Group Q) (eta : G →* Q),
        IsOsin24Quotient Hfam H (s : Set G) Q eta ∧
          eta.ker.IsFinitelyNormallyGenerated := by
    intro s
    induction s using Finset.induction with
    | empty =>
        refine ⟨G, inferInstance, MonoidHom.id G, ?_⟩
        have hmodel := osin24SingletonStep_identityModel Hfam hrel H hsuit
          (t := (1 : G)) H.one_mem
        obtain ⟨hone, hker⟩ := hmodel
        obtain ⟨hsurj, hrelQ, _htarget, hinj, hsuitQ, htorsion⟩ := hone
        refine ⟨⟨hsurj, hrelQ, ?_, hinj, hsuitQ, htorsion⟩, hker⟩
        intro x hx
        cases hx
    | @insert a s ha ih =>
        obtain ⟨Q, instQ, phi, hphi, hkerPhi⟩ := ih
        letI : Group Q := instQ
        have hrelQ : IsRelativelyHyperbolic Q
            (fun l => (Hfam l).map phi) := hphi.2.1
        have hsuitQ : IsSuitableSubgroup (fun l => (Hfam l).map phi)
            (H.map phi) := hphi.2.2.2.2.1
        obtain ⟨P, instP, psi, hpsi, hkerPsi⟩ :=
          hstep Q instQ ι (fun l => (Hfam l).map phi) hrelQ
            (H.map phi) hsuitQ (phi a)
        letI : Group P := instP
        refine ⟨P, instP, psi.comp phi, ?_, ?_⟩
        · simpa only [Finset.coe_insert] using
            isOsin24Quotient_comp_insert Hfam H (s : Set G) a phi psi hphi hpsi
        · exact ker_comp_isFinitelyNormallyGenerated phi hphi.1 psi
            hkerPhi hkerPsi
  obtain ⟨Q, instQ, eta, hq, hker⟩ := hind ht.toFinset
  exact ⟨Q, instQ, eta, by simpa only [Set.Finite.coe_toFinset] using hq, hker⟩

end RelHyp
end GGT
end GroupApproximation
