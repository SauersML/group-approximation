import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFCharacterizationAssembly
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFSolvableWordProblem
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterWordProblem
import GroupApproximation.Meta.AxiomGuard

/-!
# The lamplighter host, with and without solvable word problem

`simple_kazhdan_sofic_group.tex` at origin/main f34e9c0b1, proof of `cor:lef` and `cor:host`.

> By Theorem `thm:general`, `G_Δ = EL_3(R_Δ)` is an infinite finitely generated simple Kazhdan
> group, and the limit of finite simple groups `SL_{3N}(F_2)` whose Cayley graphs form expanders.
> … So `G_Δ` contains `Γ ≤ [Δ,Δ] ≤ [Λ,Λ]`. … So `G_Δ` has solvable word problem.

Both `LEFLamplighterStatement` and `LEFLamplighterSolvableWordProblemStatement` ask for some host.
The printed host is the concrete group `G_Δ = EL_3(LC(Ω, F_2) ⋊ Λ)`. This module names that concrete
claim and combines it with skf-consequences' word problem of `G_Δ`.

* `LamplighterHostStatement`: for an infinite finitely generated LEF group `Δ`, `G_Δ` is such a
  host and `[Δ,Δ]` embeds in it. This is the piece sk-lef-action produces.
* `lefLamplighterStatement_of_host`: it gives `LEFLamplighterStatement`.
* `lefLamplighterSolvableWordProblemStatement_of_pieces`: together with
  `Lamplighter.PrintedLamplighterHostSolvableWordProblem` it gives
  `LEFLamplighterSolvableWordProblemStatement`.
* `printedLEFSubgroupCharacterization_of_host` and
  `printedLEFSolvableWordProblemCharacterization_of_lamplighter`: both statements of `cor:lef` over
  these pieces.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

/-- **The lamplighter host** (tex, proof of `cor:lef`: the application of `thm:general` and
`[Δ,Δ] ≤ [Λ,Λ] ↪ G_Δ`): for an infinite finitely generated LEF group `Δ`, the group
`G_Δ = EL_3(LC(Ω, F_2) ⋊ Λ)` is such a host, and `[Δ,Δ]` embeds in it. -/
def LamplighterHostStatement : Prop :=
  ∀ (Δ : Type) [Group Δ], Infinite Δ → Group.FG Δ → IsLEF Δ →
    IsLEFHost ↥(elementaryGroup (Fin 3) (Lamplighter.LampRing Δ)) ∧
      ∃ f : ↥(commutator Δ) →* ↥(elementaryGroup (Fin 3) (Lamplighter.LampRing Δ)),
        Function.Injective f

/-- **The lamplighter piece of `cor:lef` and `cor:host`** from the concrete host. -/
theorem lefLamplighterStatement_of_host (hhost : LamplighterHostStatement) :
    LEFLamplighterStatement := by
  intro Δ _ hinf hfg hlef
  obtain ⟨hE, f, hf⟩ := hhost Δ hinf hfg hlef
  exact ⟨↥(elementaryGroup (Fin 3) (Lamplighter.LampRing Δ)), inferInstance, hE, f, hf⟩

/-- **The lamplighter host with solvable word problem** (tex l.445–455) from the concrete host and
skf-consequences' word problem of `G_Δ`. -/
theorem lefLamplighterSolvableWordProblemStatement_of_pieces (hhost : LamplighterHostStatement)
    (hswp : Lamplighter.PrintedLamplighterHostSolvableWordProblem) :
    LEFLamplighterSolvableWordProblemStatement := by
  intro Δ _ hinf hfg hlef hswpΔ
  obtain ⟨hE, f, hf⟩ := hhost Δ hinf hfg hlef
  exact ⟨↥(elementaryGroup (Fin 3) (Lamplighter.LampRing Δ)), inferInstance, hE, hswp Δ hswpΔ, f,
    hf⟩

/-- **`cor:lef`, first statement**, over the concrete lamplighter host. -/
theorem printedLEFSubgroupCharacterization_of_host (hhost : LamplighterHostStatement) :
    PrintedLEFSubgroupCharacterization :=
  printedLEFSubgroupCharacterization_of_lamplighter (lefLamplighterStatement_of_host hhost)

/-- **`cor:lef`, second statement**, over the second choice of `Δ`, the concrete lamplighter host
and the word problem of `G_Δ`. -/
theorem printedLEFSolvableWordProblemCharacterization_of_lamplighter
    (hultra : LEFSolvableWordProblemEmbeddingStatement) (hhost : LamplighterHostStatement)
    (hswp : Lamplighter.PrintedLamplighterHostSolvableWordProblem) :
    PrintedLEFSolvableWordProblemCharacterization :=
  printedLEFSolvableWordProblemCharacterization_of_pieces hultra
    (lefLamplighterSolvableWordProblemStatement_of_pieces hhost hswp)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.lefLamplighterStatement_of_host
#audit_axioms GroupApproximation.SimpleKazhdanSofic.lefLamplighterSolvableWordProblemStatement_of_pieces
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedLEFSubgroupCharacterization_of_host
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedLEFSolvableWordProblemCharacterization_of_lamplighter

end SimpleKazhdanSofic
end GroupApproximation
