import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterModelGeneration
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleKazhdanGeneralClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFCharacterization
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFDiagonalCommutators
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MarkedLimitTransport
import GroupApproximation.Meta.AxiomGuard
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Perfect

/-!
# The lamplighter host `G_Δ = EL_3(R_Δ)`

`simple_kazhdan_sofic_group.tex` at origin/main 696c4b602 (md5 0648e5f8…), tex 419–430, in the
proof of `cor:lef` and `cor:host`:

> By Theorem `thm:general`, `G_Δ = EL_3(R_Δ)` is an infinite finitely generated simple Kazhdan group,
> and the limit of finite simple groups `SL_{3N}(F_2)` whose Cayley graphs form expanders.
>
> Finally, `ξ ↦ diag(u_ξ,1,1)` is an injective homomorphism `Λ → GL_3(R_Δ)`.  It maps `[Λ,Λ]` into
> `G_Δ` [...].  So `G_Δ` contains `Γ ≤ [Δ,Δ] ≤ [Λ,Λ]`.

For an infinite finitely generated LEF group `Δ`:

* `countable_of_fg`, `perfectSpace_lampSpace`: `Ω = F_2^Δ` is a Cantor set (compact, metrizable,
  totally disconnected, perfect and nonempty);
* `isMatricialVia_lampRing`: `R_Δ` is matricial via the reindexed `φ_n` of the finite models, on the
  printed generators;
* `isLEFHost_lampRing`: Theorem `thm:general` (ct-two-ended's closed `printedSimpleKazhdanGeneral`)
  applies, and block flattening carries the finite groups `EL_3(M_N(F_2))` onto `SL_{3N}(F_2)`;
* `exists_commutator_embedding`: `[Δ,Δ] ≤ [Λ,Λ]` embeds in `G_Δ` through `ξ ↦ diag(u_ξ,1,1)`
  (ms-intro-2's `lefDiagonalHom`);
* `printedLamplighterHost`: the concrete host, in the form of sk-lef-assembly's `LamplighterHostStatement`,
  from which `LEFLamplighterStatement` follows (`lefLamplighterStatement_of_host`).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace Lamplighter

open Filter

variable (Δ : Type) [Group Δ]

/-- A finitely generated group is countable: it is a quotient of a free group on finitely many
generators. -/
theorem countable_of_fg (hΔ : Group.FG Δ) : Countable Δ := by
  obtain ⟨T, hT, -⟩ := Group.fg_iff.1 hΔ
  have hsurj : Function.Surjective (FreeGroup.lift (Subtype.val : T → Δ)) := by
    intro δ
    have hδ : δ ∈ (FreeGroup.lift (Subtype.val : T → Δ)).range := by
      rw [FreeGroup.range_lift_eq_closure, Subtype.range_coe, hT]
      exact Subgroup.mem_top δ
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.1 hδ
    exact ⟨w, hw⟩
  exact hsurj.countable

/-- `Ω = F_2^Δ` has no isolated points when `Δ` is infinite. -/
instance perfectSpace_lampSpace [Infinite Δ] : PerfectSpace (LampSpace Δ) := by
  refine ⟨preperfect_iff_nhds.2 fun x _ U hU => ?_⟩
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.1 hU
  obtain ⟨I, u, hu, hIU⟩ := isOpen_pi_iff.1 hV x hxV
  obtain ⟨h, hh⟩ := Infinite.exists_notMem_finset I
  refine ⟨Function.update x h (x h + 1),
    ⟨hVU (hIU (Set.mem_pi.2 fun a ha => ?_)), Set.mem_univ _⟩, fun he => ?_⟩
  · have hah : a ≠ h := fun hah => hh (by rw [← hah]; exact Finset.mem_coe.1 ha)
    rw [Function.update_of_ne hah]
    exact (hu a (Finset.mem_coe.1 ha)).2
  · have hxh := congrFun he h
    rw [Function.update_self] at hxh
    simp at hxh

variable {Δ}

/-- **`R_Δ` is matricial** (tex 416–419, the hypothesis of `thm:general`): the reindexed `φ_n` of the
finite models on balls, on the printed generators. -/
theorem isMatricialVia_lampRing {T : Set Δ} (hTfin : T.Finite) (hT : Subgroup.closure T = ⊤)
    (M : BallModelSequence Δ T) :
    IsMatricialVia (lampGenerators_finite hTfin).toFinset (modelDim M) (modelMapFin M) := by
  refine ⟨modelDim_pos M, modelMapFin_one M, fun k => ?_, fun r s =>
    (eventually_modelMapFin_mul M hT r s).mono fun k hk => ⟨modelMapFin_add M k r s, hk⟩⟩
  rw [Set.Finite.coe_toFinset]
  exact closure_modelMapFin_lampGenerators_eq_top M k

variable (Δ)

/-- **The host** (tex 419–422): for an infinite finitely generated LEF group `Δ`, `G_Δ = EL_3(R_Δ)` is an
infinite finitely generated simple Kazhdan group, the limit of finite simple groups `SL_{3N}(F_2)`
whose Cayley graphs form expanders. -/
theorem isLEFHost_lampRing [Infinite Δ] (hΔ : Group.FG Δ) (hLEF : IsLEF Δ) :
    IsLEFHost ↥(elementaryGroup (Fin 3) (LampRing Δ)) := by
  classical
  obtain ⟨T, hT, hTfin⟩ := Group.fg_iff.1 hΔ
  obtain ⟨M⟩ := exists_ballModelSequence hLEF hTfin
  haveI : Countable Δ := countable_of_fg Δ hΔ
  haveI : Group.FG (LampAffine Δ) := fg_lampAffine Δ hΔ
  have hS1 : (1 : LampRing Δ) ∈ (lampGenerators_finite hTfin).toFinset :=
    (Set.Finite.mem_toFinset _).2 one_mem_lampGenerators
  have hSgen : Subring.closure
      (((lampGenerators_finite hTfin).toFinset : Finset (LampRing Δ)) : Set (LampRing Δ)) = ⊤ := by
    rw [Set.Finite.coe_toFinset]
    exact closure_lampGenerators hT
  obtain ⟨hinf, hfg, hsimple, hkaz, hlim, hsl, -, hexp⟩ :=
    printedSimpleKazhdanGeneral (LampAffine Δ) (LampSpace Δ) (isMinimal Δ) (isTopologicallyFree Δ)
      (lampGenerators_finite hTfin).toFinset hS1 hSgen (modelDim M) (modelMapFin M)
      (isMatricialVia_lampRing hTfin hT M) 3 le_rfl
  refine ⟨hinf, hfg, hsimple, hkaz, MarkingIndex 3 (lampGenerators_finite hTfin).toFinset,
    elementaryMarking 3 (lampGenerators_finite hTfin).toFinset,
    fun ℓ => Fin 3 × Fin (modelDim M ℓ), fun _ => inferInstance, fun _ => inferInstance,
    fun ℓ i => elementaryBlockEquivSL 3 le_rfl (modelDim M ℓ) (modelDim_pos M ℓ)
      (matricialMarking 3 (lampGenerators_finite hTfin).toFinset (modelDim M) (modelMapFin M) ℓ i),
    fun ℓ => ?_, ?_, ?_⟩
  · exact (MulEquiv.isSimpleGroup_congr
      (elementaryBlockEquivSL 3 le_rfl (modelDim M ℓ) (modelDim_pos M ℓ))).1 (hsl ℓ)
  · exact hlim.map_target fun ℓ =>
      elementaryBlockEquivSL 3 le_rfl (modelDim M ℓ) (modelDim_pos M ℓ)
  · exact hexp.map_target fun ℓ =>
      elementaryBlockEquivSL 3 le_rfl (modelDim M ℓ) (modelDim_pos M ℓ)

/-- `ξ ↦ u_ξ` is injective. -/
theorem unitHom_injective :
    Function.Injective (ClopenGroupCrossedProduct.unitHom (LampAffine Δ) (LampSpace Δ) (ZMod 2)) := by
  intro ξ η h
  have hval := congrArg (fun z : (LampRing Δ)ˣ => (z : LampRing Δ)) h
  simp only [ClopenGroupCrossedProduct.unitHom_apply, ClopenGroupCrossedProduct.val_unit] at hval
  refine (SkewMonoidAlgebra.single_left_inj ?_).1 hval
  intro h1
  have h2 := congrArg
    (fun g => (ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2)).symm g (fun _ => 0)) h1
  exact (one_ne_zero : (1 : ZMod 2) ≠ 0) h2

/-- **`[Δ,Δ] ≤ [Λ,Λ]` embeds in `G_Δ`** (tex 424–430), through `ξ ↦ diag(u_ξ,1,1)`. -/
theorem exists_commutator_embedding :
    ∃ f : ↥(commutator Δ) →* ↥(elementaryGroup (Fin 3) (LampRing Δ)), Function.Injective f := by
  have hmem : ∀ x : ↥(commutator Δ),
      lefDiagonalHom (ClopenGroupCrossedProduct.unitHom (LampAffine Δ) (LampSpace Δ) (ZMod 2))
          (SemidirectProduct.inr (x : Δ)) ∈ elementaryGroup (Fin 3) (LampRing Δ) := by
    intro x
    refine lefDiagonalHom_commutator_le _ ⟨SemidirectProduct.inr (x : Δ), ?_, rfl⟩
    have hx : (SemidirectProduct.inr (x : Δ) : LampAffine Δ) ∈
        (commutator Δ).map SemidirectProduct.inr :=
      Subgroup.mem_map_of_mem _ x.2
    rw [commutator_def, Subgroup.map_commutator] at hx
    rw [commutator_def]
    exact Subgroup.commutator_mono le_top le_top hx
  refine ⟨{ toFun := fun x => ⟨lefDiagonalHom
              (ClopenGroupCrossedProduct.unitHom (LampAffine Δ) (LampSpace Δ) (ZMod 2))
              (SemidirectProduct.inr (x : Δ)), hmem x⟩
            map_one' := Subtype.ext (by simp)
            map_mul' := fun x y => Subtype.ext (by simp) }, ?_⟩
  intro x y hxy
  have h := congrArg Subtype.val hxy
  exact Subtype.ext (SemidirectProduct.inr_injective
    (lefDiagonalHom_injective (unitHom_injective Δ) h))

end Lamplighter

open Lamplighter

/-- **The lamplighter host** (tex 419–430): for an infinite finitely generated LEF group `Δ`,
`G_Δ = EL_3(LC(Ω, F_2) ⋊ Λ)` is an infinite finitely generated simple Kazhdan group that is a limit of
finite simple groups `SL_{3N}(F_2)` with expander Cayley graphs, and `[Δ,Δ]` embeds in it. -/
def PrintedLamplighterHost : Prop :=
  ∀ (Δ : Type) [Group Δ], Infinite Δ → Group.FG Δ → IsLEF Δ →
    IsLEFHost ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
      ∃ f : ↥(commutator Δ) →* ↥(elementaryGroup (Fin 3) (LampRing Δ)), Function.Injective f

theorem printedLamplighterHost : PrintedLamplighterHost := fun Δ _ hinf hfg hLEF => by
  haveI := hinf
  exact ⟨isLEFHost_lampRing Δ hfg hLEF, exists_commutator_embedding Δ⟩

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedLamplighterHost


end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.isLEFHost_lampRing
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.exists_commutator_embedding
