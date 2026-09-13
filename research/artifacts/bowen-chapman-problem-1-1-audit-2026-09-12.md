# Bowen–Chapman Problem 1.1: audit of the Palomar submission, 2026-09-12

This file records what was checked before the negative answer to Problem 1.1 of
Bowen and Chapman (arXiv:2511.06586) was submitted to the Palomar registry, what
each check found, and what was not read.  Times are UTC unless marked CDT.

## 1. The submission

- Repository `SauersML/group-approximation`, commit
  `1d67f09d015d322d8afa1d0390524e9b0691aa85`, configuration
  `Palomar/comparator-bowen-chapman.json`.
- Compared theorems, in `Palomar/BowenChapmanSolution.lean`:
  - `BowenChapman.not_all_surjunctive_groups_sofic :
    ¬ ∀ (G : Type) [Group G], IsSurjunctive G → IsSoficGroup G`;
  - `BowenChapman.exists_finitelyGenerated_surjunctive_not_sofic :
    ∃ (G : Type) (_ : Group G), (∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤) ∧
    IsSurjunctive G ∧ ¬ IsSoficGroup G`.
- Both have axiom closure exactly `propext`, `Classical.choice`, `Quot.sound`.
- The group comes from
  `GroupApproximation.BowenChapman.exists_fg_surjunctive_not_isSofic`, in
  `GroupApproximation/BowenChapman/Endpoint.lean`.

### Machine evidence

- `Palomar Comparator` run 34735545983 on `1d67f09d0` completed on 2026-09-13 at
  03:35.  It reports that the nanoda kernel and the Lean default kernel accept the
  solution.
- `Palomar check` run 34735308857 on `2720752d2` succeeded.  The workflow's path
  filter is `Palomar/**`, and no file under it changed between `2720752d2` and
  `1d67f09d0`.
- Carry-over to later commits.  A Comparator run depends only on:
  - the transitive in-repository import closure of the two Palomar modules;
  - `lean-toolchain`, `lake-manifest.json` and the lakefile;
  - the configuration and the workflow.

  That is 428 files at `1d67f09d0`.  At `cbaef238a`, origin/main when this record
  was written, the closure is the same list and none of its files differs, so the
  pass holds there.  `formalization.yaml`, `README.md`, `Palomar/` and the Palomar
  workflows are also unchanged between the two commits.

## 2. Statement fidelity

The challenge's shared block was compared with Bowen–Chapman §1 and with the
textbook definitions.  No defect was found in the block or in either statement.

- **The automaton.** `cellularAutomaton γ φ = fun c x => φ fun i => c (x * γ i)`
  is the paper's automaton Φ(c)(x) = ϕ(c(xγ₁), …, c(xγₙ)), with the same
  right-translate orientation and a finite memory tuple `Fin n → G`.
- **Surjunctivity.** `IsSurjunctive G` quantifies over palettes `A : Type` with
  `[Finite A]`, memory tuples and local rules, and asks that injective automata be
  surjective.
  - Restricting palettes to `Type` loses nothing, since every finite type is
    equivalent to some `Fin k`.
  - Finiteness matters: over `A = ℕ`, the automaton `c ↦ c + 1` is injective and
    not surjective on every group.
  - The development's `Surjunctivity.IsSurjunctive` is the topological form (every
    injective continuous shift-equivariant self-map of a finite full shift is
    surjective).  The solution derives the challenge's form from it, and the driver
    `BcxSurjunctivityConverse.lean` (§7) proves the converse.
- **Soficity.** `IsSoficGroup G` asks, for every finite `F` and every ε > 0, for a
  nonempty finite carrier and a map from `G` to its permutations such that:
  - σ(gh) and σ(g)σ(h) differ in normalized Hamming distance by at most ε, for all
    g, h ∈ F;
  - σ(g) and σ(h) are at distance at least 1 − ε, for distinct g, h ∈ F.

  Pestov's Theorem 3.5 (arXiv:0804.3968) differs in three ways, each immaterial:
  1. it requires multiplicativity only when gh ∈ F, and the two forms agree
     (`GroupApproximation.isSofic_iff_productRestricted`);
  2. it requires separation 1/4 rather than 1 − ε, and tensor amplification
     recovers 1 − ε (`GroupApproximation.isSofic_iff_weak_quarter`);
  3. it has a separate clause d(σ(1), 1) ≤ ε, which follows from multiplicativity
     at g = h = 1 and left invariance of the Hamming distance.

  The driver `BcxPestovEquivalence.lean` proves `isSoficGroup_iff_isPestovSofic`
  for every `G : Type`, with no countability hypothesis.  The carrier is required
  to be nonempty, so no normalized distance divides by zero.
- **The group notion.** Bowen and Chapman's Definition 1.4 phrases soficity of a
  finitely generated group through cosoficity of the invariant random subgroup
  1_N, and they note that 1_N is cosofic exactly when F/N is sofic.  So the
  classical definition in the challenge is the same notion.
- **Binders.** The only instance binder is `[Group G]`; no `DecidableEq`,
  `Fintype`, `Countable` or `Infinite` hypothesis enters either statement.
- **Finite generation.** The clause is `Group.FG` unfolded, and the solution
  closes it with `h.out`.

## 3. Who asked the question

- Ceccherini-Silberstein and Coornaert, *Cellular Automata and Groups*, Springer
  Monographs in Mathematics.
  - 1st ed. 2010 (DOI 10.1007/978-3-642-14034-1), Open Problems, p. 417: "(OP-11)
    Does there exist a surjunctive group which is non-sofic?"  The same list
    carries OP-10, the existence of a nonsofic group, and OP-5, Gottschalk's
    conjecture.
  - 2nd ed. 2023 (DOI 10.1007/978-3-031-43328-3), p. 527, reprints OP-11 as open,
    and its Comments record no progress on it.
- Arzhantseva and Gal, *On approximation properties of semidirect products of
  groups*, arXiv:1312.7682 v1 of 2013-12-30 (p. 3); Ann. Math. Blaise Pascal 27
  (2020) 125–130, DOI 10.5802/ambp.386, p. 127: it is unknown "whether there
  exists a non-sofic surjunctive group".
- Bowen and Chapman, arXiv:2511.06586, one version, 2025-11-10: "Problem 1.1
  ([Gro99, Wei00]). Are all surjunctive groups sofic?"  They present it as a
  problem that "arises from their work", the work of Gromov (1999) and Weiss
  (2000) showing that sofic groups are surjunctive.  We do not claim that Gromov
  or Weiss posed it; neither paper was read for this audit (§6).
- Checked, and none of them poses it:
  - Pestov, arXiv:0804.3968, §6, which gives the implication from sofic to
    surjunctive and does not ask about the converse;
  - Pestov–Kwiatkowska, arXiv:0911.4266, §8;
  - Capraro–Lupini, arXiv:1309.2034.

## 4. Earlier or independent answers: none found

- **Bowen–Chapman.** arXiv:2511.06586 has one version.
  - Their main theorem, as the title says, is that surjunctivity does not
    characterize cosoficity of invariant random subgroups.
  - Their Remark 1.7 notes that surjunctivity of the IRS 1_N is surjunctivity of
    the group F/N.
  - The paper leaves the group case, Problem 1.1, open.
- **Kun–Thom**, arXiv:2608.06222, all three versions (v1 2026-08-06, v2 2026-08-19,
  v3 2026-08-20).
  - Surjunctivity appears only where they recall Gromov's theorem.  Bowen, Chapman
    and Gottschalk do not appear.
  - The nonsoficity of the group double is Theorem A of v3.  In v2 it is Theorem B,
    under the hypothesis that G is sofic.
  - Theorem 4.1 is the normalization theorem, proved in the development, and
    Theorem E gives the explicit pair.
- **OpenAI**, *Ten Advances in Mathematics and Theoretical Computer Science*, updated
  6 August 2026, Chapter 3 "Nonsofic groups exist", p. 80: "We do not know whether
  R× is surjunctive."  As of that date, the doubles were not known to be
  surjunctive.
- **Semantic Scholar** lists 3 citations of arXiv:2608.06222 (2608.28772, 2608.02025,
  2608.14673) and 1 of arXiv:2511.06586.  None of them answers the question.
- **Other channels.** The arXiv `math.GR` listing for 2026-09, web searches and
  MathOverflow gave no public claim that a nonsofic group is surjunctive.  The
  arXiv full-text API was rate-limited, so that one channel is unchecked.

Our record, by the time each commit reached GitHub (the start of its first check
run; the git commit times are 6 to 10 seconds earlier):
- 03:24:37, the argument, through the permutational wreath product (`05a8aff7a`);
- 04:43 (commit time), the group double recorded as a second witness
  (`dd87a6b2b`);
- 22:43:16, the Lean endpoint (`92ad0059d`);
- 22:48:48, the Palomar surface (`c1e3df1ef`).

## 5. The product question

- **What was open.** Arzhantseva and Gal, print p. 128 (v1 p. 4), citing Weiss
  (2000), record as open whether a product of two surjunctive groups is
  surjunctive.  This covers direct products and free products, including free
  products with ℤ.
  - Their own theorem: a split extension with a finitely generated residually
    finite kernel and a surjunctive quotient is surjunctive.
  - So G × K is surjunctive whenever G is surjunctive and K is finitely generated
    and residually finite.  They note that even G × ℤ had been unknown.
- **Doucha and Gismatullin**, *On dual surjunctivity and applications*, Groups Geom.
  Dyn. 16 (2022) 943–961, DOI 10.4171/GGD/681, Conjecture 3.12 (3.10 in
  arXiv:2008.10565 v2): if G is surjunctive, then ℤ ∗ G is surjunctive, and
  likewise for dual surjunctivity.
- **On main:**
  - `GroupApproximation.Surjunctivity.isSurjunctive_symmetricDouble`
    (`GroupApproximation/Dynamics/DoubleFinitarySite.lean`): the symmetric double
    of a surjunctive group over any subgroup is surjunctive;
  - `GroupApproximation.Surjunctivity.doubleBotEquiv` and
    `isSurjunctive_coprodI_double` (`GroupApproximation/Dynamics/FreeProductSurjunctivity.lean`,
    `9ec5bd803`): the free product of two copies of a surjunctive group is
    surjunctive.
- **A consequence, checked on paper and NOT formalized.**
  - The argument:
    1. Let G be surjunctive and nontrivial, and let H = G ∗ G.  H is surjunctive,
       and so is H ∗ H, by the theorem above applied twice.
    2. For a ≠ 1 in the first factor of H and b ≠ 1 in the second, ab has infinite
       order.
    3. Inside H ∗ H, the subgroup generated by ⟨ab⟩ in the first copy and G in the
       second is ℤ ∗ G, by the normal form for free products.
    4. Surjunctivity passes to subgroups (`IsSurjunctive.subgroup`,
       `GroupApproximation/Dynamics/SurjunctivitySubgroup.lean`), so ℤ ∗ G is
       surjunctive.  For trivial G, ℤ ∗ G is ℤ, which is residually finite.
  - This gives the plain-surjunctivity half of Conjecture 3.12; the dual half is
    untouched.
  - The same argument with P = G × K shows that G ∗ K ≤ P ∗ P is surjunctive for
    K finitely generated and residually finite.
  - The Lean step still missing is the embedding A ∗ B ↪ H ∗ H for subgroups
    A, B ≤ H.
  - The registry prose claims neither statement.
- **Checked without finding a resolution:**
  - Phung, arXiv:2603.18183, 2111.13607, 2111.02588, 2112.08484 and 2403.05998;
  - arXiv:2310.09451;
  - Bradford–Fournier-Facio, arXiv:2211.01510;
  - Ersoy, arXiv:2604.19174;
  - Cannizzo, arXiv:1912.00541, withdrawn in v2 (2019-12-04);
  - the Semantic Scholar citation lists of arXiv:1312.7682 (11 entries) and
    arXiv:2008.10565 (6 entries);
  - Ceccherini-Silberstein–Coornaert 2023, Chapter 3 "Surjunctive Groups".  It
    proves that subgroups of surjunctive groups, locally surjunctive groups and
    locally residually finite groups are surjunctive, and that surjunctive
    quotients form a closed set in the space of quotients.  It states no closure
    under products.

## 6. Not read

- Weiss, *Sofic groups and dynamical systems*, Sankhyā Ser. A 62 (2000) 350–359,
  and Gromov, *Endomorphisms of symbolic algebraic varieties*, J. Eur. Math. Soc.
  1 (1999).  So this audit makes no claim about what either paper asks.
- Capobianco, *Not just the Garden of Eden: additional takes on cellular automata
  surjectivity*, Theoret. Comput. Sci. 1041 (2025) 115217,
  DOI 10.1016/j.tcs.2025.115217.
  - Only the abstract was read.  It describes a survey of surjectivity of cellular
    automata and its links to properties of groups.
  - The publisher's page refused scripted access, and the author's publication page
    could not be fetched.
- The arXiv full-text search channel, which was rate-limited.

So `formalization.yaml` says only that no later resolution of the product
question has been found.

## 7. The fidelity drivers

`wip/bowen-chapman/fidelity/` holds three drivers written in the challenge
vocabulary.  No lake target builds files under `wip/`.

- `BcxModelTests.lean`:
  - `IsSoficGroup` holds for finite groups, `Multiplicative ℤ`, `FreeGroup Bool`
    and every residually finite group;
  - `IsSurjunctive` holds for finite groups (from the challenge definition alone),
    `FreeGroup Bool` and every residually finite group;
  - further checks: an infinite-palette negative control, the separation and
    identity clauses, agreement with `Group.FG`, and the identity automaton;
  - `#print axioms` on both compared theorems.
- `BcxPestovEquivalence.lean`: `PestovModel`, `IsPestovSofic` and
  `isSoficGroup_iff_isPestovSofic`.
- `BcxSurjunctivityConverse.lean`: the challenge's surjunctivity is equivalent to
  the development's.

They compiled green on MSI on 2026-09-12, 21:28–21:31 CDT, against the origin/main
bytes of `d71ae9349`.  Since then, the only imported module that changed is
`Palomar/BowenChapmanSolution.lean`, by one docstring line.

A fourth driver, for the free-product corollary, is not landed.
`GroupApproximation/Dynamics/FreeProductSurjunctivity.lean` (`9ec5bd803`) carries
the same three declarations, with one renamed.

## 8. Credit

`formalization.yaml` credits the result in its source row "A finitely generated
surjunctive group that is not sofic" (`type: original-proof`,
`relationship: other`):
- Astra: "solved the problem, using a custom proof tool";
- Claude (Anthropic): "wrote all the prose: the narrative fields of this file for
  this result and the docstrings of the Palomar Bowen-Chapman modules".

`automation.notes` adds that Claude (Anthropic) also produced the Lean
formalisation under the author's direction, and that no Codex or GPT agent worked
on that result.  `project.authors` is `[Sauers]` and
`project.responsible_maintainers` is `[SauersML]`.

## 9. Simulated registry review

A review against the published Palomar policy found twelve defects in the
metadata as first drafted.  Their state at `1d67f09d0`:

| | defect | state |
|---|---|---|
| D1 | `project.description` covered only the LIX result | fixed: one abstract, Bowen–Chapman first |
| D2 | `status.scope` named only the LIX files | fixed: it names both Bowen–Chapman modules |
| D3 | the challenge docstring and the yaml said that Bowen and Chapman pose the problem | fixed: they print it with the references [Gro99, Wei00], as arising from that work.  Gromov and Weiss were deliberately not added as `problem-proposer` contributors, since neither paper was read (§6) |
| D4 | no `original-proof` row for this result | fixed |
| D5 | no group-theory or dynamics classification | fixed: math.GR and math.DS; MSC 20E06, 20E22, 20F65, 22D55, 37B15 |
| D6 | `project.name` named only the LIX result | fixed |
| D7 | the README said nothing about the result | fixed: section "A surjunctive group that is not sofic" |
| D8 | reproved inputs labelled `background` | fixed: the Kun, Kun–Thom and Ershov–Jaikin-Zapirain rows are `other`.  The Arzhantseva–Gal and Ceccherini-Silberstein–Coornaert rows cite only the open question and stay `background` |
| D9 | the OpenAI row used a chapter title as the document title | fixed |
| D10 | priority evidence omitted | fixed: OP-11, Arzhantseva–Gal p. 127 and the OpenAI p. 80 sentence are quoted |
| D11 | `automation.notes` described only the LIX result | fixed |
| D12 | minor | `review.notes` points to `research/artifacts/bowen-chapman-lean-review-2026-09-12.md`, which exists at the pinned commit, and states the axiom closure.  The Weiss 2000 and Rieffel 1987 rows still have no `id` |

## 10. Repository repairs made during the audit

- `829a38553`: 42 imports that had been appended after the module docstring of
  `GroupApproximation.lean` moved above it, since Lean accepts imports only before
  the first command.
- `e7c13785a`: `KunThom/SequentialComponentFamilyCompanion.lean` and
  `KunThom/ComponentCountingSequentialObjects.lean` both declared
  `GroupApproximation.SequentialComponentFamily.card_block_sdiff_objectImage_le`.
  The companion's copy is now `card_objectParent_block_sdiff_objectImage_le`, and
  no statement changed.
- The `Manuscript signature snapshots` run 34736055144 on `e7c13785a` built the
  whole root.  Its check step then failed on `metadata/NON_MF_CLAIM_SIGNATURES.md`,
  the non-MF manuscript's signature snapshot.
  - 26 committed entries are no longer generated, and 41 generated entries are not
    committed.  All 26 removals, and 21 of the additions, are in
    `Manuscript.OneSidedMFRadical`.
  - No entry is a Bowen–Chapman declaration.
  - One added entry, `GroupApproximation.isCDEOperatorMF_of_faithful_corona_map`, is
    declared in `GroupApproximation/Analysis/MFAlgebra.lean`, a file in the Palomar
    import closure.  The snapshot lists it anew; the file itself is identical at
    the pinned commit and at the tip.

  The snapshot was left to the manuscript's owners.
