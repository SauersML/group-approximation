import GroupApproximation.Manuscript.MFRecognition.MarkedHigmanOutput

/-!
# The effective Higman compiler (`lem:mikhailova`, effectivity half)

## Survey: what the repository already has, and the one arrow it does not

Everything below was located by reading the modules named in the lane brief.

**Already proved, and reused verbatim.**

* Mihailova's lemma, in full: `Higman/MikhailovaFiberProduct.lean` proves
  `Higman.Mikhailova.freeSubgroup_eq_fiberProduct` and
  `Higman.Mikhailova.mem_freeSubgroup_iff_presented_mk_eq`, i.e. the diagonal
  pairs `(z,z)` together with the relator pairs `(r,1)` generate exactly
  `{(u,v) : u = v in Λ}`; and `Higman.Mikhailova.freeSubgroup_fg` gives the
  finite generating set for a finite alphabet and a finite relator list.  No
  literature interface is involved.
* The whole `K^0_e`, `i_e`, `L^0_e` package, at exactly the printed shape:
  `Higman/MikhailovaRankThreeWitness.lean` has
  `MikhailovaRankThree.Ambient X = F₃ × (FreeGroup X × FreeGroup X)`,
  `inputHom words f = (f, words f, 1)`, `inputHom_injective`,
  `cuttingSubgroup R = ⊤ × Mikhailova.freeSubgroup R`,
  `input_mem_cutting_iff`, `comap_cutting_eq_kernel`,
  `kernel_eq_normalClosure_of_markedEmbedding`, and
  `range_inf_cutting_eq_normalClosure_map`.  These are the printed
  "Consequently ..." sentences and they are unconditional.
* The syntactic (raw finite-presentation) compilers downstream of a marked
  embedding: `Higman/MikhailovaRankThreeCode.lean`
  (`MikhailovaRankThreeCode.computable_compile`) and
  `Higman/MikhailovaRopeCode.lean` (`MikhailovaRopeCode.computable_compile`)
  are primitive recursive transformations of codes; and
  `Higman/MikhailovaRopeCompiler.lean` turns marked embedding data into an
  `FPOvergroup`.
* Concrete coding layers: `Computability/PresentationCodes.lean` for *finite*
  presentations (`ℕ × List (List (ℕ × Bool))`, with `Carrier`, `wordOf`,
  `relatorFinset`) and `Computability/EnumeratedPresentationCodes.lean` for
  *recursive* presentations (`Nat.Partrec.Code`, with `rawRelator`).

**Not present.**  Higman's embedding theorem itself is carried in
`Higman/EmbeddingTheorem.lean` as the single uninhabited input
`Higman.REBenign` (recursively enumerable normal subgroups of finitely
generated free groups are benign), from which
`Higman.fpOvergroup_of_fgRecursive` produces an `FPOvergroup`.  That statement
is **existential and unmarked**: it yields *some* finitely presented overgroup,
not a finite presentation *code* together with *words* spelling the images of
the three generators, and it is not uniform in a code for the input.  Nothing
in `Higman/` or `Computability/` produces such marked data.
`Higman/HigmanPlacement.lean` and its neighbours are the ongoing internal proof
of the missing benign-closure input, not a compiler.
`Manuscript/OneSidedMFRadical/ComputabilityConstructionClosure.lean` says so in
its own header: "This module does not claim the one effectivity statement that
remains open in the current development: an effective Higman embedding compiler
from a recursive presentation to a finite presentation with marked embedding
words."

So the missing arrow is exactly `EffectiveHigmanCompiler` below, and nothing
else in the printed lemma is missing.

## The form of the literature input

LITERATURE INPUT: Higman 1961, Theorem 1 -- cited as Higman in the manuscript
-- together with Mikaelian's explicit algorithm, which the printed proof cites
for the finite presentation and the embedding words.

It is carried as an **uninhabited structure**, the idiom this repository
already uses for exactly this gap (`Higman.REBenign`,
`Higman.BridgeEff.BridgeEffective`, `Higman.BridgeEff.ExtWordProblemRE`), and
not as a declaration with an open leaf: the `GroupApproximation` library is
built with `-DwarningAsError=true`, under which an open leaf is a build error
(see the `lakefile.toml` comment on `PalomarChallenge`), and `scripts/check.py`
carries a hard lexical gate for open leaves with a single pinned exception in
`Palomar/Challenge.lean`.  The structure form is equivalent, is visible to
the kernel audit as a hypothesis rather than as a new constant, and lets every
consequence below be *proved*.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HigmanCompiler

noncomputable section

/-! ## 1.  The missing arrow -/

/-- **LITERATURE INPUT: Higman 1961, Theorem 1, made effective by Mikaelian's
algorithm.**  An algorithm that computes from a recursively enumerated
presentation on the three letters `x, y, t` a finite presentation
`⟨X_e | R_e⟩` of a group `Λ_e` together with words `w_x, w_y, w_t ∈ F(X_e)`
whose assignment induces an embedding `Q_e → Λ_e`.

This is the *only* content of `lem:mikhailova` that the development does not
prove.  The three fields are, in order: the algorithm, its computability, and
the single semantic clause that its output is a marked embedding.  The
Mihailova clause of the printed lemma is not a field, because it is proved
(`MarkedHigmanOutput.mem_mihailova_iff`).

**Nothing inhabits this structure.**  What the repository has of Higman's
theorem is `Higman.REBenign` plus the rope trick
(`Higman.fpOvergroup_of_fgRecursive`), which is existential, unmarked, and not
uniform in a code; see this module's header. -/
structure EffectiveHigmanCompiler where
  /-- The algorithm: recursive presentation code on `x, y, t` in, finite
  presentation code and three marked words out. -/
  compile : RecPresCode → RawMarkedOutput
  /-- The algorithm is computable. -/
  computable : Computable compile
  /-- Its output is a marked embedding of the presented group. -/
  marks : ∀ P : RecPresCode, ∃ o : MarkedHigmanOutput P, o.raw = compile P

/-! ## 2.  `lem:mikhailova`, first sentence -/

/-- **`lem:mikhailova`, the printed first sentence.**  "There is an algorithm
that computes from `e` a finite presentation `⟨X_e | R_e⟩` of a group `Λ_e`,
words `w_x, w_y, w_t ∈ F(X_e)`, and a finite generating set of a subgroup
`M_e ≤ F(X_e) × F(X_e)`, such that `x ↦ w_x`, `y ↦ w_y`, `t ↦ w_t` induces an
embedding `Q_e → Λ_e`, and `M_e = {(u,v) : u = v in Λ_e}`."

Stated uniformly in a recursive presentation code for `Q_e`; the specialisation
to `e` is `manuscriptMikhailovaUniform`.  Everything except the marked
embedding, which is the hypothesis, is proved: `Λ_e` is finitely presented
because its presentation is a code, and the two `M_e` clauses are Mihailova's
lemma as proved in `Higman.Mikhailova`. -/
theorem manuscriptMikhailova (h : EffectiveHigmanCompiler) :
    ∃ f : RecPresCode → RawMarkedOutput, Computable f ∧
      ∀ P : RecPresCode, ∃ o : MarkedHigmanOutput P,
        o.raw = f P ∧
        Group.IsFinitelyPresented (Host o.host) ∧
        (∃ S : Set (FreeGroup (HostAlphabet o.host) ×
            FreeGroup (HostAlphabet o.host)),
          S.Finite ∧ Subgroup.closure S = o.mihailova) ∧
        (∀ u v : FreeGroup (HostAlphabet o.host),
          (u, v) ∈ o.mihailova ↔
            PresentedGroup.mk (hostRelators o.host) u =
              PresentedGroup.mk (hostRelators o.host) v) := by
  refine ⟨h.compile, h.computable, ?_⟩
  intro P
  obtain ⟨o, ho⟩ := h.marks P
  exact ⟨o, ho, host_isFinitelyPresented o.host,
    o.exists_finite_generating_set_mihailova, o.mem_mihailova_iff⟩

/-- **`lem:mikhailova`, computing from `e`.**  Composed with any computable
map `e ↦ Q_e` --- which Lemmas `lem:switch` and `lem:bridge` supply --- the
compiler runs on the index itself. -/
theorem manuscriptMikhailovaUniform (h : EffectiveHigmanCompiler)
    {qcode : ℕ → RecPresCode} (hq : Computable qcode) :
    ∃ f : ℕ → RawMarkedOutput, Computable f ∧
      ∀ e : ℕ, ∃ o : MarkedHigmanOutput (qcode e),
        o.raw = f e ∧
        Group.IsFinitelyPresented (Host o.host) ∧
        (∃ S : Set (FreeGroup (HostAlphabet o.host) ×
            FreeGroup (HostAlphabet o.host)),
          S.Finite ∧ Subgroup.closure S = o.mihailova) ∧
        (∀ u v : FreeGroup (HostAlphabet o.host),
          (u, v) ∈ o.mihailova ↔
            PresentedGroup.mk (hostRelators o.host) u =
              PresentedGroup.mk (hostRelators o.host) v) := by
  refine ⟨fun e => h.compile (qcode e), h.computable.comp hq, ?_⟩
  intro e
  obtain ⟨o, ho⟩ := h.marks (qcode e)
  exact ⟨o, ho, host_isFinitelyPresented o.host,
    o.exists_finite_generating_set_mihailova, o.mem_mihailova_iff⟩

end

end HigmanCompiler
end MFRecognition
end Manuscript
end GroupApproximation
