import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralRing.Statement
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleKazhdanSoficMainClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MatricialEndpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterHost
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFLevelEmbedding
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MarkedLimitLEF
import GroupApproximation.Sofic.LEF
import GroupApproximation.Meta.AxiomGuard

/-!
# The consequences of `thm:general` in `simple_kazhdan_sofic_group.tex`

The paragraph after Theorem `thm:general` (tex l.191–195):

> (l.191–192) Periodic approximations of $X$ give such maps, and Theorem~\ref{thm:main} follows.
>
> (l.192–194) Lamplighter actions show that the countable subgroups of the groups in
> Theorem~\ref{thm:general}\textup{(b)} are exactly the countable LEF groups
> (Corollary~\ref{cor:host}).

## Formalization

* `manuscriptSentence_periodicApproximationsMain`: for every infinite minimal subshift `X` over a
  finite alphabet, periodic approximations make `R = LC(X, F₂) ⋊_T ℤ` matricial on its printed
  generators `{1, u, u⁻¹} ∪ {e_a}` (`PrintedPeriodicMatricialStatement`), and Theorem `thm:main`
  holds (`PrintedSimpleKazhdanSoficMain`, all clauses, every `n ≥ 3`).
* `manuscriptSentence_countableSubgroupsLEF`: a countable group `Γ` is LEF if and only if it embeds
  in `EL_n(R)`, `n ≥ 3`, for some setting of `thm:general`(b): a finitely generated `Λ` acting
  minimally and topologically freely on a Cantor set `C`, a finite generating set `S ∋ 1` of
  `R = LC(C, F₂) ⋊ Λ`, and maps `φ_k : R → M_{N_k}(F₂)` as printed.

## Proof route

* Periodic approximations: `printedPeriodicMatricialStatement` (`MatricialEndpoints`, from
  `exists_periodicMatricial`); `thm:main`: `printedSimpleKazhdanSoficMain`.
* "Only if": `lefUltraproductEmbeddingStatement` embeds `Γ` in `[Δ, Δ]` for an infinite finitely
  generated LEF group `Δ`; the lamplighter action of `Λ = F₂^{(Δ)} ⋊ Δ` on `F₂^Δ` is a setting of
  `thm:general`(b) (`Lamplighter.isMinimal`, `Lamplighter.isTopologicallyFree`,
  `Lamplighter.closure_lampGenerators`, `Lamplighter.isMatricialVia_lampRing`), and `[Δ, Δ]` embeds
  in `EL_3(R_Δ)` (`Lamplighter.exists_commutator_embedding`).
* "If": `thm:general`(b) (`printedSimpleKazhdanGeneral`) makes `EL_n(R)` a marked limit of the finite
  groups `EL_n(M_{N_k}(F₂))`, hence LEF (`isLEF_of_isMarkedLimit`), and LEF passes to subgroups
  (`isLEF_of_injective`).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace GeneralRing

/-! ## Periodic approximations and `thm:main` (tex l.191–192) -/

/-- **Periodic approximations give such maps, and `thm:main` follows** (tex l.191–192): for every
infinite minimal subshift `X ⊆ A^ℤ` over a finite alphabet there are maps `φ_k` as in
`thm:general`(b) on the printed generators of `R = LC(X, F₂) ⋊_T ℤ`, and Theorem `thm:main` holds. -/
theorem manuscriptSentence_periodicApproximationsMain :
    PrintedPeriodicMatricialStatement ∧ PrintedSimpleKazhdanSoficMain :=
  ⟨printedPeriodicMatricialStatement, printedSimpleKazhdanSoficMain⟩

/-! ## Countable subgroups (tex l.192–194) -/

/-- **The countable subgroups of the groups in `thm:general`(b) are exactly the countable LEF
groups** (tex l.192–194): a countable group `Γ` is LEF if and only if, for some finitely generated
group `Λ` acting minimally and topologically freely on a Cantor set `C`, some finite set `S ∋ 1`
generating `R = LC(C, F₂) ⋊ Λ`, some maps `φ_k : R → M_{N_k}(F₂)` as in `thm:general`(b), and some
`n ≥ 3`, `Γ` embeds in `EL_n(R)`. -/
theorem manuscriptSentence_countableSubgroupsLEF :
    ∀ (Γ : Type) [Group Γ], Countable Γ →
      (IsLEF Γ ↔
        ∃ (Λ : Type) (_ : Group Λ) (_ : Group.FG Λ) (C : Type) (_ : TopologicalSpace C)
          (_ : CompactSpace C) (_ : TopologicalSpace.MetrizableSpace C)
          (_ : TotallyDisconnectedSpace C) (_ : PerfectSpace C) (_ : Nonempty C)
          (_ : MulAction Λ C) (_ : ContinuousConstSMul Λ C)
          (S : Finset (ClopenGroupCrossedProduct Λ C (ZMod 2))),
          IsGeneralSetting Λ C S ∧
            ∃ (N : ℕ → ℕ) (φ : ∀ k, ClopenGroupCrossedProduct Λ C (ZMod 2) →
                Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)),
              IsMatricialVia S N φ ∧
                ∃ n : ℕ, 3 ≤ n ∧
                  ∃ f : Γ →* ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ C (ZMod 2))),
                    Function.Injective f) := by
  intro Γ _ hc
  constructor
  · intro hΓ
    classical
    obtain ⟨Δ, _, hinfΔ, hFG, hLEF, f, hf, hcomm⟩ := lefUltraproductEmbeddingStatement Γ hc hΓ
    haveI : Infinite Δ := hinfΔ
    obtain ⟨T, hT, hTfin⟩ := Group.fg_iff.1 hFG
    obtain ⟨M⟩ := Lamplighter.exists_ballModelSequence hLEF hTfin
    haveI : Countable Δ := Lamplighter.countable_of_fg Δ hFG
    haveI : Group.FG (Lamplighter.LampAffine Δ) := Lamplighter.fg_lampAffine Δ hFG
    have hS1 : (1 : Lamplighter.LampRing Δ) ∈ (Lamplighter.lampGenerators_finite hTfin).toFinset :=
      (Set.Finite.mem_toFinset _).2 Lamplighter.one_mem_lampGenerators
    have hSgen : Subring.closure
        (((Lamplighter.lampGenerators_finite hTfin).toFinset : Finset (Lamplighter.LampRing Δ)) :
          Set (Lamplighter.LampRing Δ)) = ⊤ := by
      rw [Set.Finite.coe_toFinset]
      exact Lamplighter.closure_lampGenerators hT
    obtain ⟨g, hg⟩ := Lamplighter.exists_commutator_embedding Δ
    refine ⟨Lamplighter.LampAffine Δ, inferInstance, inferInstance, Lamplighter.LampSpace Δ,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, (Lamplighter.lampGenerators_finite hTfin).toFinset,
      ⟨Lamplighter.isMinimal Δ, Lamplighter.isTopologicallyFree Δ, hS1, hSgen⟩,
      Lamplighter.modelDim M, Lamplighter.modelMapFin M,
      Lamplighter.isMatricialVia_lampRing hTfin hT M, 3, le_rfl,
      g.comp (f.codRestrict (commutator Δ) hcomm), ?_⟩
    intro x y hxy
    have h1 : g (f.codRestrict (commutator Δ) hcomm x) = g (f.codRestrict (commutator Δ) hcomm y) :=
      hxy
    exact hf (congrArg Subtype.val (hg h1))
  · rintro ⟨Λ, _, _, C, _, _, _, _, _, _, _, _, S, hset, N, φ, hφ, n, hn, f, hf⟩
    obtain ⟨hmin, hfree, hS1, hS⟩ := hset
    obtain ⟨-, -, -, -, hlim, -⟩ := printedSimpleKazhdanGeneral Λ C hmin hfree S hS1 hS N φ hφ n hn
    have hfin : ∀ k, Finite ↥(elementaryGroup (Fin n) (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))) :=
      fun k => finite_elementaryGroup_matrix n (N k)
    exact isLEF_of_injective f hf (isLEF_of_isMarkedLimit hfin hlim)

end GeneralRing
end SimpleKazhdanSofic
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.SimpleKazhdanSofic.GeneralRing.manuscriptSentence_periodicApproximationsMain
#audit_axioms GroupApproximation.SimpleKazhdanSofic.GeneralRing.manuscriptSentence_countableSubgroupsLEF
