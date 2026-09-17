import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterHost
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFCharacterizationClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFLevelEmbedding
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFRecursivePresentationClasses
import GroupApproximation.Sofic.ContinuumMultiplicityCore
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Host.Setup
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:host` and the proof of `cor:host`

`simple_kazhdan_sofic_group.tex`.

> (l.533–537, `lem:host`) If `Δ` is infinite and LEF, then `G_Δ` is an infinite, finitely
> generated, simple Kazhdan group and an expander limit of finite simple groups `SL_{3N}(F_2)`, and
> `ξ ↦ diag(u_ξ, 1, 1)` embeds `[Λ,Λ]`, which contains `[Δ,Δ]`, in `G_Δ`.
>
> (l.577–578) Therefore Theorem `thm:general` applies to `R_Δ`.
>
> (l.591–592) Limits of finite groups in the space of marked groups are LEF, and so are their
> subgroups.
>
> (l.592–594) Conversely, by Lemmas `lem:nn` and `lem:host` every countable LEF group is a
> subgroup of a group `G_Δ` as in the corollaries.
>
> (l.597–598) Conversely, a countable group has countably many finitely generated subgroups.
>
> (l.598–600) The last statement of Corollary `cor:host` follows, as there are countably many
> recursive presentations.

Route.

* `manuscriptSentence_generalTheoremApplies`: for a finite generating set `T` of `Δ` take finite
  models `M` on balls (`Lamplighter.exists_ballModelSequence`); every hypothesis of `thm:general`
  holds for `Λ ↷ Ω` (finitely generated `Λ`, `Ω` a compact metrizable totally disconnected perfect
  space, minimal and topologically free action), with the finite generating set
  `Lamplighter.lampGenerators T` of `R_Δ` and the matrices `φ_n`
  (`Lamplighter.isMatricialVia_lampRing`); the conclusion is `printedSimpleKazhdanGeneral` at `n = 3`.
* `manuscriptSentence_hostLemma`: the conclusion above, with `EL_3(M_N(F_2)) ≅ SL_{3N}(F_2)`
  (`elementaryBlockEquivSL`) transporting simplicity, the marked limit and the expander property;
  `ξ ↦ diag(u_ξ,1,1)` (`lefDiagonalHom`) is injective (`Lamplighter.unitHom_injective`) and maps
  `[Λ,Λ]` into `EL_3(R_Δ)` (`lefDiagonalHom_commutator_le`); `[Δ,Δ] ≤ [Λ,Λ]` is
  `Host.manuscriptSentence_commutatorContainment`.
* `manuscriptSentence_markedLimitsLEF`: `printedMarkedLimitSubgroupsLEF`.
* `manuscriptSentence_countableLEFSubgroupOfHost`: `lem:nn` (`lefUltraproductEmbeddingStatement`)
  embeds `Γ` in `[Δ,Δ]` for an infinite finitely generated LEF `Δ`; `lem:host`
  (`printedLamplighterHost`) embeds `[Δ,Δ]` in `G_Δ`.
* `manuscriptSentence_countableFGSubgroups`: `ContinuumMultiplicity.countable_fg_subgroups`.
* `manuscriptSentence_recursivelyPresentedHost`: countably many isomorphism classes of recursively
  presented groups (`recursivePresentationClassesStatement`), and one host for all of them
  (`printedRecursivelyPresentedLEFHost`).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace Host

open Lamplighter

/-- **Theorem `thm:general` applies to `R_Δ`** (tex l.577–578): its hypotheses hold for `Λ ↷ Ω`, a
finite generating set `S ∋ 1` of `R_Δ` and the matrices `φ_n`, and its conclusion holds for
`n = 3`. -/
theorem manuscriptSentence_generalTheoremApplies (Δ : Type) [Group Δ] [Infinite Δ]
    (hΔ : Group.FG Δ) (hLEF : IsLEF Δ) :
    Group.FG (LampAffine Δ) ∧ CompactSpace (LampSpace Δ) ∧
    TopologicalSpace.MetrizableSpace (LampSpace Δ) ∧ TotallyDisconnectedSpace (LampSpace Δ) ∧
    PerfectSpace (LampSpace Δ) ∧ Nonempty (LampSpace Δ) ∧
    MulAction.IsMinimal (LampAffine Δ) (LampSpace Δ) ∧
    (∀ ξ : LampAffine Δ, ξ ≠ 1 → ∀ U : Set (LampSpace Δ), IsOpen U → U.Nonempty →
      ∃ z ∈ U, ξ • z ≠ z) ∧
    ∃ (S : Finset (LampRing Δ)) (N : ℕ → ℕ)
      (φ : ∀ k, LampRing Δ → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)),
      1 ∈ S ∧ Subring.closure (S : Set (LampRing Δ)) = ⊤ ∧ IsMatricialVia S N φ ∧
      Infinite ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
      Group.FG ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
      IsSimpleGroup ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
      HasKazhdanPropertyT.{0, 0} ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
      IsMarkedLimit (elementaryMarking 3 S) (matricialMarking 3 S N φ) ∧
      (∀ k, IsSimpleGroup ↥(elementaryGroup (Fin 3) (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)))) ∧
      IsExpanderFamily (matricialMarking 3 S N φ) := by
  classical
  obtain ⟨T, hT, hTfin⟩ := Group.fg_iff.1 hΔ
  obtain ⟨M⟩ := Lamplighter.exists_ballModelSequence hLEF hTfin
  haveI : Countable Δ := Lamplighter.countable_of_fg Δ hΔ
  haveI : Group.FG (LampAffine Δ) := Lamplighter.fg_lampAffine Δ hΔ
  have hS1 : (1 : LampRing Δ) ∈ (Lamplighter.lampGenerators_finite hTfin).toFinset :=
    (Set.Finite.mem_toFinset _).2 Lamplighter.one_mem_lampGenerators
  have hSgen : Subring.closure
      (((Lamplighter.lampGenerators_finite hTfin).toFinset : Finset (LampRing Δ)) :
        Set (LampRing Δ)) = ⊤ := by
    rw [Set.Finite.coe_toFinset]
    exact Lamplighter.closure_lampGenerators hT
  obtain ⟨hinf, hfg, hsimple, hkaz, hlim, hsl, -, hexp⟩ :=
    printedSimpleKazhdanGeneral (LampAffine Δ) (LampSpace Δ) (Lamplighter.isMinimal Δ)
      (Lamplighter.isTopologicallyFree Δ) (Lamplighter.lampGenerators_finite hTfin).toFinset hS1
      hSgen (Lamplighter.modelDim M) (Lamplighter.modelMapFin M)
      (Lamplighter.isMatricialVia_lampRing hTfin hT M) 3 le_rfl
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Lamplighter.isMinimal Δ, Lamplighter.isTopologicallyFree Δ,
    (Lamplighter.lampGenerators_finite hTfin).toFinset, Lamplighter.modelDim M,
    Lamplighter.modelMapFin M, hS1, hSgen, Lamplighter.isMatricialVia_lampRing hTfin hT M,
    hinf, hfg, hsimple, hkaz, hlim, hsl, hexp⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.Host.manuscriptSentence_generalTheoremApplies

/-- **`lem:host`** (tex l.528–537): for an infinite finitely generated LEF group `Δ`,
`G_Δ = EL_3(R_Δ)` is an infinite, finitely generated, simple Kazhdan group and the marked limit of
the finite simple groups `SL_{3N_ℓ}(F_2)`, whose marked Cayley graphs form an expander family;
`ξ ↦ diag(u_ξ, 1, 1)` embeds `[Λ,Λ]` in `G_Δ`; and `[Λ,Λ]` contains `[Δ,Δ]`. -/
theorem manuscriptSentence_hostLemma (Δ : Type) [Group Δ] [Infinite Δ] (hΔ : Group.FG Δ)
    (hLEF : IsLEF Δ) :
    Infinite ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
    Group.FG ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
    IsSimpleGroup ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
    HasKazhdanPropertyT.{0, 0} ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
    (∃ (ι : Type) (s : ι → ↥(elementaryGroup (Fin 3) (LampRing Δ))) (N : ℕ → ℕ)
      (σ : ∀ ℓ, ι → Matrix.SpecialLinearGroup (Fin 3 × Fin (N ℓ)) (ZMod 2)),
      (∀ ℓ, IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3 × Fin (N ℓ)) (ZMod 2))) ∧
      IsMarkedLimit s σ ∧ IsExpanderFamily σ) ∧
    (∃ f : ↥(commutator (LampAffine Δ)) →* ↥(elementaryGroup (Fin 3) (LampRing Δ)),
      Function.Injective f ∧
      ∀ ξ : ↥(commutator (LampAffine Δ)),
        (((f ξ : ↥(elementaryGroup (Fin 3) (LampRing Δ))) : (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) :
            Matrix (Fin 3) (Fin 3) (LampRing Δ)) =
          Matrix.diagonal ![((ClopenGroupCrossedProduct.unit (LampAffine Δ) (LampSpace Δ) (ZMod 2)
            (ξ : LampAffine Δ) : (LampRing Δ)ˣ) : LampRing Δ), 1, 1]) ∧
    (commutator Δ).map (SemidirectProduct.inr : Δ →* LampAffine Δ) ≤
      commutator (LampAffine Δ) := by
  obtain ⟨-, -, -, -, -, -, -, -, S, N, φ, -, -, hφ, hinf, hfg, hsimple, hkaz, hlim, hsl, hexp⟩ :=
    manuscriptSentence_generalTheoremApplies Δ hΔ hLEF
  have hmem : ∀ x : ↥(commutator (LampAffine Δ)),
      lefDiagonalHom (ClopenGroupCrossedProduct.unitHom (LampAffine Δ) (LampSpace Δ) (ZMod 2))
          (x : LampAffine Δ) ∈ elementaryGroup (Fin 3) (LampRing Δ) := fun x =>
    lefDiagonalHom_commutator_le
      (ClopenGroupCrossedProduct.unitHom (LampAffine Δ) (LampSpace Δ) (ZMod 2))
      (Subgroup.mem_map_of_mem
        (lefDiagonalHom (ClopenGroupCrossedProduct.unitHom (LampAffine Δ) (LampSpace Δ) (ZMod 2)))
        x.2)
  refine ⟨hinf, hfg, hsimple, hkaz,
    ⟨MarkingIndex 3 S, elementaryMarking 3 S, N,
      fun ℓ i => elementaryBlockEquivSL 3 le_rfl (N ℓ) (hφ.1 ℓ) (matricialMarking 3 S N φ ℓ i),
      fun ℓ => (MulEquiv.isSimpleGroup_congr
        (elementaryBlockEquivSL 3 le_rfl (N ℓ) (hφ.1 ℓ))).1 (hsl ℓ),
      hlim.map_target fun ℓ => elementaryBlockEquivSL 3 le_rfl (N ℓ) (hφ.1 ℓ),
      hexp.map_target fun ℓ => elementaryBlockEquivSL 3 le_rfl (N ℓ) (hφ.1 ℓ)⟩,
    ⟨MonoidHom.codRestrict
      ((lefDiagonalHom
        (ClopenGroupCrossedProduct.unitHom (LampAffine Δ) (LampSpace Δ) (ZMod 2))).comp
          (commutator (LampAffine Δ)).subtype)
      (elementaryGroup (Fin 3) (LampRing Δ)) hmem, ?_, fun ξ =>
        lefDiagonalHom_val (ClopenGroupCrossedProduct.unitHom (LampAffine Δ) (LampSpace Δ) (ZMod 2))
          (ξ : LampAffine Δ)⟩,
    (manuscriptSentence_commutatorContainment Δ).2⟩
  intro x y hxy
  have h : lefDiagonalHom (ClopenGroupCrossedProduct.unitHom (LampAffine Δ) (LampSpace Δ) (ZMod 2))
        (x : LampAffine Δ) =
      lefDiagonalHom (ClopenGroupCrossedProduct.unitHom (LampAffine Δ) (LampSpace Δ) (ZMod 2))
        (y : LampAffine Δ) :=
    congrArg Subtype.val hxy
  exact Subtype.ext (lefDiagonalHom_injective (Lamplighter.unitHom_injective Δ) h)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.Host.manuscriptSentence_hostLemma

/-- **Limits of finite groups in the space of marked groups are LEF, and so are their subgroups**
(tex l.591–592). -/
theorem manuscriptSentence_markedLimitsLEF (ι G : Type) [Group G] (s : ι → G) (H : ℕ → Type)
    [∀ ℓ, Group (H ℓ)] (σ : ∀ ℓ, ι → H ℓ) (hfin : ∀ ℓ, Finite (H ℓ))
    (hlim : IsMarkedLimit s σ) :
    IsLEF G ∧ ∀ K : Subgroup G, IsLEF ↥K :=
  printedMarkedLimitSubgroupsLEF ι G s H σ hfin hlim

#audit_axioms GroupApproximation.SimpleKazhdanSofic.Host.manuscriptSentence_markedLimitsLEF

/-- **Every countable LEF group is a subgroup of a group `G_Δ` as in the corollaries**
(tex l.592–594): `G_Δ` for an infinite finitely generated LEF group `Δ`, an infinite finitely
generated simple Kazhdan group that is an expander limit of finite simple groups `SL_N(F_2)`. -/
theorem manuscriptSentence_countableLEFSubgroupOfHost (Γ : Type) [Group Γ] (hc : Countable Γ)
    (hΓ : IsLEF Γ) :
    ∃ (Δ : Type) (_ : Group Δ), Infinite Δ ∧ Group.FG Δ ∧ IsLEF Δ ∧
      IsLEFHost ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
      ∃ f : Γ →* ↥(elementaryGroup (Fin 3) (LampRing Δ)), Function.Injective f := by
  obtain ⟨Δ, _, hinf, hfgΔ, hlefΔ, φ, hφ, hmem⟩ := lefUltraproductEmbeddingStatement Γ hc hΓ
  obtain ⟨hE, ψ, hψ⟩ := printedLamplighterHost Δ hinf hfgΔ hlefΔ
  refine ⟨Δ, inferInstance, hinf, hfgΔ, hlefΔ, hE, ψ.comp (φ.codRestrict (commutator Δ) hmem), ?_⟩
  intro x y hxy
  have h1 : ψ (φ.codRestrict (commutator Δ) hmem x) = ψ (φ.codRestrict (commutator Δ) hmem y) :=
    hxy
  have h2 : φ x = φ y := congrArg Subtype.val (hψ h1)
  exact hφ h2

#audit_axioms GroupApproximation.SimpleKazhdanSofic.Host.manuscriptSentence_countableLEFSubgroupOfHost

/-- **A countable group has countably many finitely generated subgroups** (tex l.597–598). -/
theorem manuscriptSentence_countableFGSubgroups (X : Type) [Group X] [Countable X] :
    {H : Subgroup X | H.FG}.Countable :=
  ContinuumMultiplicity.countable_fg_subgroups X

#audit_axioms GroupApproximation.SimpleKazhdanSofic.Host.manuscriptSentence_countableFGSubgroups

/-- **The last statement of `cor:host` follows, as there are countably many recursive
presentations** (tex l.598–600): the recursively presented finitely generated groups fall into
countably many isomorphism classes, and one group `E` as in the corollaries (infinite, finitely
generated, simple, Kazhdan, an expander limit of finite simple groups `SL_N(F_2)`) contains every
recursively presented finitely generated LEF group. -/
theorem manuscriptSentence_recursivelyPresentedHost :
    (∃ (J : Type) (_ : Countable J) (H : J → Type) (_ : ∀ j, Group (H j)),
      ∀ (Γ : Type) [Group Γ], Group.FG Γ → Nonempty (Higman.RecursivePresentation Γ) →
        ∃ j, Nonempty (Γ ≃* H j)) ∧
    ∃ (E : Type) (_ : Group E), IsLEFHost E ∧
      ∀ (Γ : Type) [Group Γ], Group.FG Γ → Nonempty (Higman.RecursivePresentation Γ) →
        IsLEF Γ → ∃ f : Γ →* E, Function.Injective f :=
  ⟨recursivePresentationClassesStatement, printedRecursivelyPresentedLEFHost⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.Host.manuscriptSentence_recursivelyPresentedHost

end Host
end SimpleKazhdanSofic
end GroupApproximation
