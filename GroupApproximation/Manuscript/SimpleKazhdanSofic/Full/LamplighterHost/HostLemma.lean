import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterHost
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ThmMainA.MarkedGroups
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Host.Setup
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:host`

`simple_kazhdan_sofic_group.tex`, `lem:host` (tex l.527–537) and its proof (tex l.539–587).

> (l.533–537) If `Δ` is infinite and LEF, then `G_Δ` is an infinite, finitely generated, simple
> Kazhdan group and an expander limit of finite simple groups `SL_{3N}(F_2)`, and
> `ξ ↦ diag(u_ξ,1,1)` embeds `[Λ,Λ]`, which contains `[Δ,Δ]`, in `G_Δ`.
>
> (l.577–578) Therefore Theorem `thm:general` applies to `R_Δ`.
>
> (l.580–587) Finally, `ξ ↦ diag(u_ξ,1,1)` is an injective homomorphism `Λ → GL_3(R_Δ)`. It maps
> `[Λ,Λ]` into `G_Δ` [...]. As `Δ ≤ Λ`, the group `[Λ,Λ]` contains `[Δ,Δ]`.

The objects `Ω`, `Λ`, `R_Δ`, `u_ξ` are those of `Full/LamplighterHost/Setting.lean`.

## Spelling

* "Expander limit" is the printed notion `ThmMainA.IsExpanderLimit` (tex l.92–98). The markings are
  tuples `Fin m → _`, the finite groups converge to `G_Δ` in the space of marked groups, their orders
  tend to infinity, and there is a uniform vertex-expansion constant. The neighbours of a set are its
  products with the entries of the tuple and their inverses.
* `SL_{3N}(F_2)` is `Matrix.SpecialLinearGroup (Fin 3 × Fin N) (ZMod 2)`, on an index type of size
  `3N`, with `N ≥ 1`.
* "Embeds" means an injective homomorphism `[Λ,Λ] →* G_Δ`, and its formula is recorded.

## Route

* `generalTheoremApplies` (tex l.577–578): finite models on balls (`Lamplighter.exists_ballModelSequence`)
  give the matrices `φ_n` (`Lamplighter.isMatricialVia_lampRing`) on the printed generators, and
  `printedSimpleKazhdanGeneral` is applied at `n = 3`.
* `hostLemma`: `EL_3(M_N(F_2)) ≅ SL_{3N}(F_2)` (`elementaryBlockEquivSL`) transports simplicity, the
  marked limit and the expander property. `ThmMainA.isExpanderLimit_of_isMarkedLimit` converts them
  to the printed expander limit. `ξ ↦ diag(u_ξ,1,1)` is `lefDiagonalHom`, injective by
  `Lamplighter.unitHom_injective`, with `[Λ,Λ]` mapped into `EL_3(R_Δ)` by
  `lefDiagonalHom_commutator_le`. The corpus host notion `IsLEFHost` is
  `Lamplighter.isLEFHost_lampRing`.
* `printedHostLemma`: the closed form.
-/

namespace GroupApproximation.Full.SK10

open GroupApproximation.SimpleKazhdanSofic
open GroupApproximation.SimpleKazhdanSofic.Lamplighter

/-- **Theorem `thm:general` applies to `R_Δ`** (`simple_kazhdan_sofic_group.tex`, tex l.577–578).
For an infinite finitely generated LEF group `Δ`, every hypothesis of `thm:general` holds for `Λ ↷ Ω`,
a finite generating set `S ∋ 1` of `R_Δ` and the matrices `φ_n`, and its conclusion holds for
`n = 3`. -/
theorem generalTheoremApplies (Δ : Type) [Group Δ] [Infinite Δ] (hΔ : Group.FG Δ)
    (hLEF : IsLEF Δ) :
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

#audit_axioms GroupApproximation.Full.SK10.generalTheoremApplies

/-- **`lem:host`** (`simple_kazhdan_sofic_group.tex`, tex l.527–537). Let `Δ` be finitely generated,
LEF and infinite. Then:
* `G_Δ = EL_3(R_Δ)` is infinite, finitely generated, simple and Kazhdan;
* some marking `g` of `G_Δ` is an expander limit of markings `q_ℓ` of the finite simple groups
  `SL_{3N_ℓ}(F_2)`, in the printed sense;
* `G_Δ` is a host in the corpus sense `IsLEFHost`;
* `ξ ↦ diag(u_ξ, 1, 1)` is an injective homomorphism `[Λ,Λ] → G_Δ`;
* `Δ ≤ Λ` maps `[Δ,Δ]` into `[Λ,Λ]`. -/
theorem hostLemma (Δ : Type) [Group Δ] (hfg : Group.FG Δ) (hlef : IsLEF Δ) (hinf : Infinite Δ) :
    Infinite ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
    Group.FG ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
    IsSimpleGroup ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
    HasKazhdanPropertyT.{0, 0} ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
    (∃ (N : ℕ → ℕ) (m : ℕ) (g : Fin m → ↥(elementaryGroup (Fin 3) (LampRing Δ)))
      (q : ∀ ℓ, Fin m → Matrix.SpecialLinearGroup (Fin 3 × Fin (N ℓ)) (ZMod 2)),
      (∀ ℓ, 0 < N ℓ) ∧
      (∀ ℓ, IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3 × Fin (N ℓ)) (ZMod 2))) ∧
      ThmMainA.IsExpanderLimit q g) ∧
    IsLEFHost ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
    (∃ f : ↥(commutator (LampAffine Δ)) →* ↥(elementaryGroup (Fin 3) (LampRing Δ)),
      Function.Injective f ∧
      ∀ ξ : ↥(commutator (LampAffine Δ)),
        (((f ξ : ↥(elementaryGroup (Fin 3) (LampRing Δ))) : (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) :
            Matrix (Fin 3) (Fin 3) (LampRing Δ)) =
          Matrix.diagonal ![((ClopenGroupCrossedProduct.unit (LampAffine Δ) (LampSpace Δ) (ZMod 2)
            (ξ : LampAffine Δ) : (LampRing Δ)ˣ) : LampRing Δ), 1, 1]) ∧
    (commutator Δ).map (SemidirectProduct.inr : Δ →* LampAffine Δ) ≤
      commutator (LampAffine Δ) := by
  haveI := hinf
  obtain ⟨-, -, -, -, -, -, -, -, S, N, φ, -, -, hφ, hinfE, hfgE, hsimple, hkaz, hlim, hsl, hexp⟩ :=
    generalTheoremApplies Δ hfg hlef
  obtain ⟨hpos, -⟩ := hφ
  have e : ∀ ℓ, ↥(elementaryGroup (Fin 3) (Matrix (Fin (N ℓ)) (Fin (N ℓ)) (ZMod 2))) ≃*
      Matrix.SpecialLinearGroup (Fin 3 × Fin (N ℓ)) (ZMod 2) := fun ℓ =>
    elementaryBlockEquivSL 3 le_rfl (N ℓ) (hpos ℓ)
  obtain ⟨m, g, q, hq⟩ :=
    ThmMainA.isExpanderLimit_of_isMarkedLimit (hlim.map_target e) (hexp.map_target e)
  have hmem : ∀ x : ↥(commutator (LampAffine Δ)),
      lefDiagonalHom (ClopenGroupCrossedProduct.unitHom (LampAffine Δ) (LampSpace Δ) (ZMod 2))
          (x : LampAffine Δ) ∈ elementaryGroup (Fin 3) (LampRing Δ) := fun x =>
    lefDiagonalHom_commutator_le
      (ClopenGroupCrossedProduct.unitHom (LampAffine Δ) (LampSpace Δ) (ZMod 2))
      (Subgroup.mem_map_of_mem
        (lefDiagonalHom (ClopenGroupCrossedProduct.unitHom (LampAffine Δ) (LampSpace Δ) (ZMod 2)))
        x.2)
  refine ⟨hinfE, hfgE, hsimple, hkaz,
    ⟨N, m, g, q, hpos, fun ℓ => (MulEquiv.isSimpleGroup_congr (e ℓ)).1 (hsl ℓ), hq⟩,
    Lamplighter.isLEFHost_lampRing Δ hfg hlef,
    ⟨MonoidHom.codRestrict
      ((lefDiagonalHom
        (ClopenGroupCrossedProduct.unitHom (LampAffine Δ) (LampSpace Δ) (ZMod 2))).comp
          (commutator (LampAffine Δ)).subtype)
      (elementaryGroup (Fin 3) (LampRing Δ)) hmem, ?_, fun ξ =>
        lefDiagonalHom_val (ClopenGroupCrossedProduct.unitHom (LampAffine Δ) (LampSpace Δ) (ZMod 2))
          (ξ : LampAffine Δ)⟩,
    (Host.manuscriptSentence_commutatorContainment Δ).2⟩
  intro x y hxy
  have h : lefDiagonalHom (ClopenGroupCrossedProduct.unitHom (LampAffine Δ) (LampSpace Δ) (ZMod 2))
        (x : LampAffine Δ) =
      lefDiagonalHom (ClopenGroupCrossedProduct.unitHom (LampAffine Δ) (LampSpace Δ) (ZMod 2))
        (y : LampAffine Δ) :=
    congrArg Subtype.val hxy
  exact Subtype.ext (lefDiagonalHom_injective (Lamplighter.unitHom_injective Δ) h)

#audit_axioms GroupApproximation.Full.SK10.hostLemma

/-- **`lem:host`, closed form** (`simple_kazhdan_sofic_group.tex`, tex l.527–537): the conclusion of
`hostLemma` for every finitely generated, LEF, infinite group `Δ`. -/
def PrintedHostLemma : Prop :=
  ∀ (Δ : Type) [Group Δ], Group.FG Δ → IsLEF Δ → Infinite Δ →
    Infinite ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
    Group.FG ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
    IsSimpleGroup ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
    HasKazhdanPropertyT.{0, 0} ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
    (∃ (N : ℕ → ℕ) (m : ℕ) (g : Fin m → ↥(elementaryGroup (Fin 3) (LampRing Δ)))
      (q : ∀ ℓ, Fin m → Matrix.SpecialLinearGroup (Fin 3 × Fin (N ℓ)) (ZMod 2)),
      (∀ ℓ, 0 < N ℓ) ∧
      (∀ ℓ, IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3 × Fin (N ℓ)) (ZMod 2))) ∧
      ThmMainA.IsExpanderLimit q g) ∧
    IsLEFHost ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
    (∃ f : ↥(commutator (LampAffine Δ)) →* ↥(elementaryGroup (Fin 3) (LampRing Δ)),
      Function.Injective f ∧
      ∀ ξ : ↥(commutator (LampAffine Δ)),
        (((f ξ : ↥(elementaryGroup (Fin 3) (LampRing Δ))) : (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) :
            Matrix (Fin 3) (Fin 3) (LampRing Δ)) =
          Matrix.diagonal ![((ClopenGroupCrossedProduct.unit (LampAffine Δ) (LampSpace Δ) (ZMod 2)
            (ξ : LampAffine Δ) : (LampRing Δ)ˣ) : LampRing Δ), 1, 1]) ∧
    (commutator Δ).map (SemidirectProduct.inr : Δ →* LampAffine Δ) ≤
      commutator (LampAffine Δ)

theorem printedHostLemma : PrintedHostLemma := fun Δ _ hfg hlef hinf =>
  hostLemma Δ hfg hlef hinf

#audit_closed_axioms GroupApproximation.Full.SK10.printedHostLemma

end GroupApproximation.Full.SK10
