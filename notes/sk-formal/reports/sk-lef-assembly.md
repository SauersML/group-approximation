# Lane sk-lef-assembly: `simple_kazhdan_sofic_group.tex`, section "LEF groups", cor:lef and cor:host statements and assemblies

Lead: session nonsofic-existence-49 (ROSTER-sk, "LEF LANES 21:22"; resumed 23:15 after the coordinator restart). Target: the origin/main tip of
the note, 37551fd93 (23:16), 767 lines, md5 b55c0d23b8c59e66d36df004a1df608b. The census on origin is 649cb1f80, regenerated at this md5.
Rows are keyed by its 12-hex hashes.

## CLAIM

CLAIM cor:lef and cor:host statements and assemblies GroupApproximation/Manuscript/SimpleKazhdanSofic/LEFCharacterization.lean

- Ownership check at 21:3x and again at 23:3x: no declaration on origin, in the shared tree or in `lanes/*.files` names a LEF host,
  `PrintedLEFSubgroupCharacterization`, a `cor:host` statement, or a module `LEFCharacterization`.
- `isLEF_of_injective` (`Sofic/LEF`), ct-two-ended's `printedMarkedLimitLEFStatement` (`MarkedLimitLEF`), `countable_of_fg` and
  `countable_fg_subgroups` (`Sofic/ContinuumMultiplicityCore`), and `Higman.RecursivePresentation` (`Higman/Program`) are consumed by name.
- 23:15 ruling from main: sk-universal is not resumed and this lane absorbs its scope. There was nothing to absorb: its registration has an
  empty `.files`, and it has no report, no landing, no attic copy and no shared-tree draft. Its scope is the last statement of cor:host.

CLAIM restricted direct sum (tex l.430–434) GroupApproximation/Manuscript/SimpleKazhdanSofic/LEFRestrictedSum.lean

CLAIM cor:lef second statement, solvable word problem, heredity (tex l.317–319, l.439–459) GroupApproximation/Manuscript/SimpleKazhdanSofic/LEFSolvableWordProblem.lean

CLAIM countably many recursive presentations (tex l.435–436) GroupApproximation/Manuscript/SimpleKazhdanSofic/LEFRecursivePresentationClasses.lean

CLAIM solvable word problem gives a recursive presentation GroupApproximation/Manuscript/SimpleKazhdanSofic/SolvableWordProblemRecursivePresentation.lean

CLAIM instances of the last statement of cor:host (tex l.324–327) GroupApproximation/Manuscript/SimpleKazhdanSofic/LEFHostInstances.lean

CLAIM lamplighter host combination GroupApproximation/Manuscript/SimpleKazhdanSofic/LEFLamplighterCombination.lean

CLAIM closed cor:lef and cor:host endpoints GroupApproximation/Manuscript/SimpleKazhdanSofic/LEFCharacterizationClosed.lean

- 09:2x–10:0x:
  - LANDED 0da57c90d `LEFLamplighterCombination` (probe 0914-092422-61787 GREEN, 4 audits classical).
  - sk-lef-action landed the closed `printedLamplighterHost` (7c8024160). Its Prop `PrintedLamplighterHost` is word for word this lane's
    `LamplighterHostStatement`.
  - New module `LEFCharacterizationClosed` closes cor:lef's first statement and cor:host's three statements (main clauses), and states cor:lef's
    second statement over its two residual pieces.
  - The census regenerated at tip 8b36733d7 (9cb80166d, md5 29d63f79…). Rows are keyed there.
  - Key split with ms-traces-1 at l.288–338: this lane holds 3670fa959e0e, 022271399cfb, 01a45cdd9370, cc439ae277d4, 9cdf19db0ef4, 9b1a6e7489a1
    and 61dddc00d418. ms-traces-1 holds 83394521b2d5, fd312b860bb5, 2745cd64eada, 8212b1470040, fc84c012b409 and d00f0309aff7.
  - Reconciliation after the ~09:36 outage: nothing was half-landed. The last landing is 0da57c90d. ct-involution adopted `LEFHostInstances`
    (217926394) and `HostInstancePieces`.

- 09:3x: skf-consequences landed its statement Props at 04544e6d6: `Lamplighter.PrintedLamplighterAffineSolvableWordProblem` and
  `Lamplighter.PrintedLamplighterHostSolvableWordProblem` (G_Δ = `elementaryGroup (Fin 3) (LampRing Δ)` has solvable WP whenever Δ does).
  `LEFLamplighterCombination` names the concrete host piece `LamplighterHostStatement`. Its spelling was sent to sk-lef-action, whose
  thm:general application should produce it. The module derives `LEFLamplighterStatement`, `LEFLamplighterSolvableWordProblemStatement`, and
  both statements of cor:lef over it.
- Boundary agreed with skf-consequences at 09:1x: it takes l.445–455 (the WP of Λ and G_Δ, module `LamplighterWordProblem`) and the rows
  581584337a04, 7bfa078c0bed, e3cd35e16e2f and 14148c1b4df0, which this lane dropped from its row file. This lane combines its SWP theorem with
  sk-lef-action's host into `LEFLamplighterSolvableWordProblemStatement` once both land.
- Interfaces agreed at 08:3x:
  - skf-degrees: `HasSolvableWordProblem` over `wordProblemOracle` (landed 8be083fcd).
  - oa-expanders: owns the second choice of Δ (`LevelShiftDelta.levelDelta`, `LEFSecondChoiceStatement`). This lane takes its word problem
    over a family `levelGen t : Option ι → Equiv.Perm (Γ × ℤ)`.

## Split agreed with ms-intro-3 (~21:30, still valid)

- This lane owns the statement Props and their closure. ms-intro-3 writes no Lean for the abstract's LEF sentence or the intro paragraph on
  lamplighter actions, and lands their census rows over this lane's endpoints.

## Ledger (tip 37551fd93, section "LEF groups", l.295–437)

| key | l. | sentence (abridged) | grade | carrier / owner |
|---|---|---|---|---|
| 197333c03a92 | 297–301 | Every countable group embeds in a f.g. simple group [Gorjuskin, Schupp], even in a simple quotient of a torsion-free hyperbolic Kazhdan group [CFF 1.5], so one simple Kazhdan group contains Higman's universal f.p. group [Higman]. | attribution | prior work, not a step |
| 8b4f6b0857f1 | 301–305 | Kionke–Schesler [1.2] with Wilson: one simple LEF group contains every f.p. RF group. | attribution | prior work, not a step |
| 42f4246af4ac | 305–306 | They raised the question which groups embed in f.g. simple amenable groups. | attribution | prior work |
| 3670fa959e0e | 306–307 | For LEF groups the next corollary answers the analogous question, with a Kazhdan host. | structural | roadmap to cor:lef |
| 488b860770fb | 307–310 | It parallels the theorem of Boone and Higman ... | attribution | prior work |
| 19d10ddcbec2 | 313–316 | cor:lef | partial | `PrintedLEFSubgroupCharacterization`, `printedLEFSubgroupCharacterization_of_pieces` |
| cc439ae277d4 | 320 | Every countable LEF group is a subgroup of such a group. | partial | `PrintedCountableLEFHost`, `printedCountableLEFHost_of_pieces` |
| 9cdf19db0ef4 | 320–322 | A set of f.g. groups lies in one such group iff its members are LEF and represent countably many isomorphism classes. | partial | `PrintedLEFFamilyHost`, `printedLEFFamilyHost_of_pieces` |
| 31ffcc3c38e6 | 322–325 | So one such group contains every recursively presented f.g. LEF group, for instance every f.p. RF group and every G_Y whose language is recursive. | partial | `PrintedRecursivelyPresentedLEFHost`, `printedRecursivelyPresentedLEFHost_of_pieces`; the two instances wait on sk-malcev/Vershik–Gordon names and skf-degrees' WP ≤_T L(Y) |
| 61dddc00d418 | 329–330 | Limits of finite groups in the space of marked groups are LEF, and so are their subgroups. | formalized (planned) | `printedMarkedLimitSubgroupsLEF` over `printedMarkedLimitLEFStatement` |
| 79e6fe57addb … 11a7360569b8 | 330–354 | Part (i): the words w_j, the algebraic ultraproduct, Δ = ⟨a,b⟩ with Γ ≤ [Δ,Δ] | owner sk-lef-ultra | piece `LEFUltraproductEmbeddingStatement` |
| ed367be4322a … 358e51e6a815 | 356–394 | Parts (ii)–(iii): the lamplighter action, R_Δ matricial, then thm:general | owner sk-lef-action (with sk-lef-models, sk-lef-simplicity) | piece `LEFLamplighterStatement` |
| 66cb283340f3, 816030a10c14, cbce9a479de2 | 396–402 | Part (iv): diag(u_ξ,1,1), [Λ,Λ] ↪ G_Δ | owner ms-intro-2 (`LEFDiagonalCommutators`, attic) | feeds `LEFLamplighterStatement` |
| 0ccc4462441b | 402–404 | This proves cor:lef and the first statement of cor:host. | structural | the two assemblies |
| 6f1b3edd435b | 404–407 | For the second, apply the first to the restricted direct sum ..., a countable LEF group, as finite subsets lie in finite products. | partial | this lane; piece `RestrictedSumLEFStatement` (to be proved here) |
| 4d817ab1caf8 | 407–408 | Conversely, a countable group has countably many f.g. subgroups. | formalized (planned) | `countable_fg_subgroups`, inside `lefFamily_countableClasses_of_host` |
| b88e89d11935 | 408–409 | There are countably many recursive presentations. | partial | this lane; piece `RecursivePresentationClassesStatement` (to be proved here) |
| 3bb068935fc5, 32a05a9577a8 | 412–417 | w_g for the topological full group, its derived subgroup in G_X | owner ms-intro-2 (same identities) | not this lane |
| f5bd2ed413cf | 419–426 | Every group as in the last statement of cor:host has unsolvable word problem [KMS 4.21; Rauzy]. | open | unowned at 23:3x, for main to rule |
| 46e5c2778909 … 5d1cbe7da012 | 428–437 | The groups G_X do not suffice: SL_3(ℤ) lies in no G_X (distortion argument; CFKP attribution). | open | unowned at 23:3x, for main to rule |

## Statement Props and pieces (module `Manuscript/SimpleKazhdanSofic/LEFCharacterization`)

- `IsLEFHost E`: "such a group". E is infinite, f.g., simple, `HasKazhdanPropertyT.{0,0}`, and a limit in the space of marked groups of simple
  `SL (κ ℓ) F₂` whose Cayley graphs form expanders, in MainAssembly's `IsMarkedLimit`/`IsExpanderFamily`. "SL_N(F₂)" is read up to reindexing by
  a finite type, so thm:general's `Fin 3 × Fin N` plugs in directly.
- `PrintedLEFSubgroupCharacterization` (cor:lef). "Subgroup of" means an injective homomorphism into the host.
- `PrintedCountableLEFHost`, `PrintedLEFFamilyHost.{u}` and `PrintedRecursivelyPresentedLEFHost` (cor:host's three statements).
  - "Represent countably many isomorphism classes" means some countable family of groups contains an isomorphic copy of every member.
  - "Recursively presented f.g." means `Group.FG` plus `Nonempty (Higman.RecursivePresentation Γ)`, which is equivalent by the Tietze argument
    in that structure's docstring.
- Pieces:
  - `LEFUltraproductEmbeddingStatement` (sk-lef-ultra, sent 23:3x);
  - `LEFLamplighterStatement` (sk-lef-action, sent 23:3x);
  - `RestrictedSumLEFStatement` and `RecursivePresentationClassesStatement` (this lane).

## Log

- 21:49: claim landed (e75bb3f65), spelled at 9047d0d3c.
- 22:00: first draft written, spelled at 9047d0d3c, never probed. Superseded by the restructure at c8b6021ca.
- 23:32: resumed. Re-ledgered at 37551fd93, sent the piece spellings to sk-lef-ultra and sk-lef-action, reported to main.
- 00:28: probe 0914-002812-94212 GREEN (BUILT, compiled, exit 0). The closed endpoint's `#audit_closed_axioms` gate is part of that build.
  I have not read the remote axiom lines of the `_of_pieces` audits yet, because the MSI master dropped right after the probe.
- 00:3x: LANDED ad79bfbc2 `Manuscript/SimpleKazhdanSofic/LEFCharacterization.lean` and queued it for wiring. Attic copy b6ed6884f,
  ledger 88db2a211. Census rows for the section's 14 keys are in `metadata/sk-census-rows/sk-lef-assembly.tsv`.
- Next: prove `RestrictedSumLEFStatement` and `RecursivePresentationClassesStatement`, then carry the two "for instance" clauses of cor:host over
  the Vershik–Gordon/RF ⇒ LEF names and skf-degrees' WP ≤_T L(Y), once those land.
- 01:1x: the note changed again after landing: 4eee46fb3 (23:40) and 696c4b602 (23:51), 841 lines, md5 0648e5f876e467e21ebf475e08b8ee92. The census on
  origin is still 649cb1f80 (at 37551fd93).
  - cor:lef has a new second statement (l.317–319): "It is LEF with solvable word problem if and only if it is a subgroup of such a group with
    solvable word problem." `PrintedLEFSubgroupCharacterization` carries only the first statement. The second gets its own statement Prop
    and assembly in a new module, and the landed module stays unchanged.
  - New proof paragraphs: a second choice of Δ that keeps a solvable word problem (l.358–382), the solvable word problem of Δ and of G_Δ
    (l.439–459), and the Osajda remark (l.462–465). Owners are for main to rule; these are in the ledger below once the census regenerates.
  - Of my 14 census rows, 11 sentences survive verbatim at the tip and are kept. 488b860770fb (Boone–Higman sentence, rewritten with Thompson),
    0ccc4462441b ("This proves ...", rewritten) and 6f1b3edd435b ("For the second, ...", rewritten) are dropped until the census is regenerated.
- 01:3x: the remote axiom lines of probe 0914-002812-94212 were read. All 8 audits of LEFCharacterization are [propext, Classical.choice,
  Quot.sound], and the log has 0 sorryAx.
- 02:0x ruling from main at tip 696c4b602:
  - this lane takes l.439–459 (the solvable word problem of Δ, Λ and G_Δ, heredity, and cor:lef's second statement), using the spelling agreed
    with skf-degrees: `HasSolvableWordProblem Γ := ∃ (ι : Type) (_ : Primcodable ι) (_ : Finite ι) (s : ι → Γ), closure (range s) = ⊤ ∧
    Partrec (wordProblemOracle s)`;
  - l.358–382 (the second choice of Δ) goes to oa-expanders;
  - l.419–437 (unsolvable word problem of the host; SL₃(ℤ) lies in no G_X) goes to audit-nm-4;
  - the Osajda remark l.462–465 is graded by this lane.
- Osajda remark grading (l.462–465): **partial, not attribution.** It asserts a new consequence: cor:lef applied to Osajda's finitely generated
  residually finite non-exact groups gives infinite simple Kazhdan LEF groups that are not exact. Its step inputs:
  - RF ⇒ LEF: `isLEF_of_residuallyFinite`, closed;
  - cor:lef: partial, above;
  - the existence of f.g. RF non-exact groups [OsajdaRF]: no carrier;
  - property A passes to subgroups: `Analysis/ExactnessPermanence` defines `HasPropertyA` but proves no subgroup permanence.
  The row lands once skf-census regenerates at the tip.
- 08:4x: probe 0914-084048-4317 GREEN, both `LEFRestrictedSum` and `LEFSolvableWordProblem` BUILT on the first try, then landed and queued for
  wiring.
  - `restrictedSumLEFStatement : RestrictedSumLEFStatement` is closed. The restricted direct sum is the subgroup of finitely supported elements.
    It is countable because each element is determined by its finite graph in `Σ j, H j`, and it is LEF because finite subsets lie in finite
    products of finite models.
  - `printedSolvableWordProblemHeredity` is closed: finitely generated subgroups of groups with solvable word problem have solvable word problem.
    It goes through skf-degrees' `wordProblemOracle_comp_injective` and `turingReducible_wordProblemOracle_of_generates`, then
    `partrec_iff_forall_turingReducible`.
  - `printedLEFSolvableWordProblemCharacterization_of_pieces` assembles cor:lef's second statement over
    `LEFSolvableWordProblemEmbeddingStatement` (oa-expanders' second choice of Δ, plus this lane's solvable WP of Δ) and
    `LEFLamplighterSolvableWordProblemStatement` (the solvable WP of G_Δ, this lane over sk-lef-action's R_Δ).
- 08:5x: probe 0914-084626-5847 GREEN, both modules BUILT; landed 2616814eb and queued for wiring. Audits are [propext, Classical.choice,
  Quot.sound] with 0 sorryAx.
  - `recursivePresentationClassesStatement : RecursivePresentationClassesStatement` is closed. A recursively presented Γ is
    `PresentedGroup (relatorSetOf gen)` (`Higman.presentedGroupEquiv`); the kernel membership of reduced words is r.e. and so is the domain of
    a program `c` (`exists_code_dom_iff`, through `Nat.Partrec.Code.exists_code`). Hence Γ ≃* `CodeGroup c`, and `Code` is countable.
  - `LEFCharacterizationAssembly`: cor:lef (first statement) and the three statements of cor:host rest only on `LEFLamplighterStatement`.
- 09:1x: LANDED b7e8fc938 `SolvableWordProblemRecursivePresentation` (probe 0914-091203-16383 GREEN, wire-queued).
  `nonempty_recursivePresentation_of_hasSolvableWordProblem` depends on [propext, Classical.choice, Quot.sound], and the log has 0 sorryAx.
  The first probe failed at one `rfl` because the definition was not unfolded; `unfold letterToFamily` fixed it.
  The same commit drops the four G_Δ word-problem rows (now skf-consequences').
- 09:1x ruling from main: the "for instance" clauses of cor:host go to ct-involution (module `HostForInstance`). This lane's unlanded,
  unregistered draft `LEFHostInstances.lean` (instance statements, pieces `FinitelyPresentedRecursivePresentationStatement` and
  `GenValueGeneratesStatement`, assemblies) was offered to it for adoption. This lane keeps row 31ffcc3c38e6 and adds ct-involution's carriers
  when they land.
- 09:2x: the note changed at f34e9c0b1 (09:05, "Shorten ... and apply the final audits"): 772 lines, md5 c909343ec38f3d3e7976342073509639. The
  census on origin is still aa6f988f4 (at 696c4b602). Fidelity check of this lane's statements against the tip:
  - cor:lef now reads "whose Cayley graphs with respect to the images of a fixed generating set form a family of expanders". `IsLEFHost` already
    requires `IsMarkedLimit s σ ∧ IsExpanderFamily σ` over the images `σ ℓ` of the marking `s`, so no respelling is needed.
  - cor:lef's second statement, cor:host's three statements and the proof steps carried here are unchanged in content.
  - The two proof sentences "Conversely, a countable group has countably many finitely generated subgroups" and "There are countably many
    recursive presentations" are merged into one sentence.
  - The attribution paragraph moved after the corollaries ("Each property alone was known. …") and gained a new opening ("Kionke and Schesler
    asked …").
  - The Osajda remark is gone, so row fdf7d6e33044 is obsolete.
  - 8 of the 18 row sentences changed text: 197333c03a92, 42f4246af4ac, 4cc7b9e7d709, 19d10ddcbec2, 31ffcc3c38e6, 4d817ab1caf8, b88e89d11935 and
    fdf7d6e33044. They are held until skf-census regenerates at f34e9c0b1.
- Ownership 09:0x: main assigned the whole piece `LEFSolvableWordProblemEmbeddingStatement` to sk-lef-ultra (module `LEFSecondDelta`), including
  l.439–444 (the WP of the second choice of Δ). Its spelling is frozen as landed in eb53a0116. This lane keeps l.444–455 (the WP of Λ and G_Δ)
  and the "for instance" clauses of cor:host.
- Ownership 08:5x: l.358–382 (second choice of Δ) moved from oa-expanders to sk-lef-ultra. The `levelGen` interface agreed with oa-expanders
  was forwarded to sk-lef-ultra.
- 08:4x: sk-lef-ultra closed `lefUltraproductEmbeddingStatement` (LEFLevelEmbedding, 563dac8bc). cor:lef and the first statement of cor:host now
  rest only on `LEFLamplighterStatement`.
- 08:30: resumed after the laptop reboot wiped /private/tmp. New infra at `f907d0cb…/scratchpad/nm`. The path is re-registered; the green records
  are lost, so the next landing re-probes. LEFCharacterization's local bytes equal origin's.
