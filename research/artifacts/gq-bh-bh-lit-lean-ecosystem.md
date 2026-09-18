# Lean and Mathlib ecosystem for a Boone–Higman formalization (for bh-palomar-plan)

Lane `bh-lit`, 2026-09-18. Read-only survey: the repo's pinned Mathlib (rev `81a5d257`, toolchain v4.32.0,
read with `git -C /Users/user/mathlib4 show/grep 81a5d257`), the newer local Mathlib checkout
(v4.33.0-rc2, grep only), the repo's Lean on `origin/main`, and a web search. Nothing was built; every
"proved" below is what the source text says, not a fresh build or axiom audit.

## 1. Mathlib at the pin (81a5d257)

| Need | In Mathlib? | Where / name |
|---|---|---|
| Presentations | yes | `PresentedGroup (rels : Set (FreeGroup α))`, `PresentedGroup.of`, `.toGroup`, `.mk_eq_one_iff`, `.closure_range_of`, `equivPresentedGroup`, `coprodPresentations` — `Mathlib/GroupTheory/PresentedGroup.lean` |
| Finite presentation | yes | `class Group.IsFinitelyPresented G` := ∃ n, ∃ φ : FreeGroup (Fin n) →* G, surjective ∧ `φ.ker.IsFinitelyNormallyGenerated`; API `.equiv`, `.of_surjective`, `.quotient` (by a finitely normally generated normal subgroup), `.exists_mulEquiv_presentedGroup`; instances: finite groups, `FreeGroup α` (α finite), `PresentedGroup` with finite rels, `Multiplicative ℤ`, `Monoid.Coprod G H` — `Mathlib/GroupTheory/FinitelyPresentedGroup.lean`. `Subgroup.IsFinitelyNormallyGenerated` in the same file. (No `Group.FinitePresentation`; the 62 `FinitePresentation` hits are the ring/algebra notion.) |
| Finite generation | yes | `Group.FG` — `Mathlib/GroupTheory/Finiteness.lean` |
| Simplicity | yes | `class IsSimpleGroup` — `Mathlib/GroupTheory/Subgroup/Simple.lean`; `Subgroup.Normal.eq_bot_or_eq_top`, `isSimpleGroup_of_surjective`; Iwasawa criterion `IwasawaStructure.isSimpleGroup` in `Mathlib/GroupTheory/GroupAction/Iwasawa.lean` (hypotheses: nontrivial, perfect, quasi-preprimitive faithful action, and an Iwasawa structure of commutative subgroups conjugated by the action and generating); alternating groups `alternatingGroup.isSimpleGroup` (n ≥ 5); PSL₂ over fields `Matrix.ProjectiveSpecialLinearGroup.rank_two_simple'` |
| Free products, amalgams, HNN | yes | `Monoid.Coprod`; `Monoid.PushoutI` (`Mathlib/GroupTheory/PushoutI.lean`); `HNNExtension` with normal words / Britton (`Mathlib/GroupTheory/HNNExtension.lean`) |
| Free groups, decidability | yes | `FreeGroup.reduce`, `instance : DecidableEq (FreeGroup α)` (`Mathlib/GroupTheory/FreeGroup/Reduce.lean`) |
| Coxeter groups | yes | `Mathlib/GroupTheory/Coxeter/*` (Coxeter matrices, braid relation as a relation in Coxeter groups) |
| Artin groups, braid groups | **no** | no `ArtinGroup`/`BraidGroup` definition (only the braid relation inside Coxeter theory; "braid" otherwise means monoidal-category braidings) |
| Baumslag–Solitar groups | **no** | none |
| Thompson / Higman–Thompson groups | **no** | none at the pin or in the v4.33.0-rc2 checkout |
| Homeomorphism groups of Cantor space | partial | `Homeomorph` groups exist generally; `Mathlib/Topology/Instances/CantorSet.lean` is the ternary Cantor set in ℝ; no prefix-replacement or Cantor-space group theory |
| Computability | general only | `Mathlib/Computability/*`: `Partrec`, `Primrec`, `RE` sets, halting problem, Turing machines, `ComputablePred`. **No group word problem, no recursive presentations, no Higman embedding theorem, no Novikov–Boone.** |

Consequence: the statement of Boone–Higman ("f.g. with solvable word problem ⟹ embeds in an f.p. simple
group") needs a repo-side definition of "solvable word problem" (e.g. a `ComputablePred` on words in
`FreeGroup (Fin n)` for a surjection, shown independent of the generating set). The *embedding* half is
expressible in pure Mathlib vocabulary, as the repo's Palomar challenge already does (§3).

## 2. External Lean projects (web search, 2026-09-18)

- **lean-eval leaderboard, problem `higman_infinite_simple`** (targets Mathlib v4.32.2; status on the page:
  unsolved, statement is `sorry`):
  `theorem higman_infinite_simple : ∃ (n : ℕ) (rels : Set (FreeGroup (Fin n))), rels.Finite ∧
  IsSimpleGroup (PresentedGroup rels) ∧ Infinite (PresentedGroup rels)`.
  The page says Mathlib has "No Higman–Thompson construction, no Higman embedding theorem, and no
  construction of an infinite finitely-presented simple group."
  Source: https://leanprover.github.io/lean-eval-leaderboard/problems/higman_infinite_simple/
- No public Lean formalization of Thompson's F, T, V, of their simplicity or finite presentation, of
  twisted Brin–Thompson groups, of Baumslag–Solitar or Artin groups was found. A Zulip thread discusses
  defining Artin–Tits groups by a Coxeter-style matrix (no library result). Search was bounded: web
  search only; GitHub code search needs a login and was not used.

## 3. The repo's own Lean (origin/main)

Counts are files mentioning the name, not theorems. 10,633 `.lean` files on main.

- **Statement.** `GroupApproximation/BooneHigman/Statement/Basic.lean`: `EmbedsInFinitelyPresentedSimpleGroup`,
  `IsMetabelianGroup`, `FinitelyPresentedMetabelianStatement` (T1 = survey 5.3(7)),
  `FinitelyGeneratedMetabelianStatement` (T2), `FinitelyGeneratedLinearStatement` (T3). `Statement/API.lean`,
  `ModelTests.lean` (A_5 simple, S_3 not).
- **Palomar pair for metabelian BH.** `Palomar/MetabelianBooneHigmanChallenge.lean` / `...Solution.lean` /
  `comparator-metabelian-boone-higman.json` (landed 0db476348, 2026-09-13; permitted axioms propext,
  Quot.sound, Classical.choice). The Solution is a **skeleton**: its theorems end in `_of` and take the
  development endpoint `FinitelyGeneratedMetabelianStatement` as a hypothesis. The development has
  `finitelyGeneratedMetabelianStatement_of_pieces` (`BooneHigman/Products/Assembly.lean`) and
  `finitelyGeneratedLinearStatement_of_hosts` (`BooneHigman/Products/Hosts.lean`): conditional assemblies.
- **Finite presentation machinery (793 files under `BooneHigman/Metabelian`).** Named results include
  `isFinitelyPresented_affine`, `isFinitelyPresented_presAff`, `steinbergSIntPoly_isFinitelyPresented`,
  `steinbergPoly_isFinitelyPresented`, `isFinitelyPresented_elementaryGroup_of_fg`,
  `kmGroup_isFinitelyPresented` (Krstić–McCool-type groups), `steinbergFreeAlgebra_isFinitelyPresented`,
  `isFinitelyPresented_envelopeK`; `BooneHigman/SteinbergBasic/Kernel.lean`
  (`isFinitelyPresented_elementaryGroup_iff`, `..._of_K2_eq_bot`); `BooneHigman/Products/FinitePi.lean`
  (`isFinitelyPresented_pi_fin`); `BooneHigman/RNPresentation/SectionCriterion.lean`.
- **Simplicity machinery.** `BooneHigman/Metabelian/EnvelopeSimpleEpstein.lean`
  (`isSimpleGroup_of_room_fragments`, an Epstein-type criterion), `EnvelopeSimpleStatement.lean`
  (`RNCommutatorSimpleStatement'`: Nekrashevych Thm 4.7 for Röver–Nekrashevych groups, as a statement).
- **Higman–Thompson / V.** `BooneHigman/V/*`: `higmanThompsonV X` as prefix-substitution permutations of
  `Cantor X`, depth calculus, cone transitivity (no simplicity or finite presentation theorem for V found
  by name). `GroupTheory/HigmanThompson/*`: Brown's presentation of F_{m+2,∞} (`brownF_isFinitelyPresented`,
  normal-form injectivity), `compactF_isFinitelyPresented`, `isSimpleGroup_commutator_compactCore`.
  `Leavitt/FamilyVEmbedding.lean` has `ThompsonV.HasDepth`/`tableGroup`;
  `Manuscript/NonMF/RelatedKunThom/ThompsonVNotLEF.lean` has `thompsonV_infinite`.
- **A closed finitely presented infinite simple group.** `GroupTheory/HydeLodha/FinitelyPresentedInfiniteSimpleClosed.lean`
  (landed 47b31bef8, 2026-09-13; imported by the root `GroupApproximation.lean`):
  `finitelyPresentedInfiniteSimple_closed : FinitelyPresentedInfiniteSimpleStatement`, i.e.
  `∃ W, Group.IsFinitelyPresented W ∧ IsPowerTorsionFree W ∧ IsSimpleGroup W ∧ Infinite W`, witnessed by
  Hyde–Lodha's `Q₂ = [Γ₂, Γ₂]`, with `#audit_closed_axioms` in the file. Together with Mathlib's
  `Group.IsFinitelyPresented.exists_mulEquiv_presentedGroup` this should give the lean-eval statement
  `higman_infinite_simple` (not checked by a build here; the leaderboard's Mathlib is v4.32.2 vs the
  repo's pin v4.32.0).
- **Absent in the repo Lean (by name search):** Baumslag–Solitar groups beyond metabelian notes (20 files
  mention "Baumslag"), Artin groups (22 files mention "Artin", mostly comments), Houghton groups (0),
  twisted Brin–Thompson groups (2 files mention "Brin"), word problems as a computability notion (the
  292 hits for `ComputablePred|Partrec|word problem` are manuscript notes, not a word-problem API).

## 4. What this means for a Palomar BH submission (lane remark)

- **Statements are cheap:** everything needed to state "G embeds in an f.p. simple group" is in Mathlib at
  the pin. Stating full BH needs one repo definition of solvable word problem.
- **Reusable proofs:** finite presentation of Steinberg / elementary groups over f.g. commutative rings and
  of affine groups (Metabelian tree), a closed f.p. infinite simple group (Hyde–Lodha Q₂), Brown's F_{n,∞}.
- **Missing for any twisted Brin–Thompson or shell-envelope route:** Thompson's V finite presentation and
  simplicity, twisted Brin–Thompson groups SV_G and Zaremsky's type (A) theorem, Belk–Hyde–Matucci germ
  extensions, Nekrashevych/Röver simplicity and finite presentation (only as statements).
- **Quick external win to consider:** a Palomar or lean-eval submission of `higman_infinite_simple` from
  `finitelyPresentedInfiniteSimple_closed` (verify the axiom audit and the Mathlib version first; the user
  decides on any external submission).
