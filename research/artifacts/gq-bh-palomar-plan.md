# Boone–Higman Palomar megasubmission: recon and plan

Lane `bh-palomar-plan`, 2026-09-18. Read-only recon of origin/main (no builds). This is a
plan, not a claim. It answers the user order of 09-18 ~10:00: "let's prepare Palomar
megasubmission for all BH results, in addition to new breakthrough discoveries".

## 0. What is already on main

**Palomar surface.**
- One submission = one Comparator configuration (repo, immutable commit, one config path).
  `theorem_names` may list many theorems.
  - The challenge compiles against frozen Mathlib with Mathlib-only imports.
  - Hard cap 100 KiB / 1000 lines; warning above 32 KiB / 300 lines.
  - Permitted axioms `propext`, `Quot.sound`, `Classical.choice`. NanoDa is always on.
- `formalization.yaml` (v0.4) describes ONE configuration at a time. Today that is
  `Palomar/comparator-surjunctive-nonsofic.json`, not Pestov.
  - `PALOMAR_METADATA_CONFIGS` in `scripts/check_palomar_submission.py` pins it.
  - `PALOMAR_CONFIGS` lists 9 live pairs; `PALOMAR_PENDING_CONFIGS` lists skeleton pairs
    (currently only lix-strong).
  - The workflows are `.github/workflows/palomar-check.yml` and `palomar-comparator.yml`.
- **A BH pair already exists:** `Palomar/MetabelianBooneHigman{Challenge,Solution,ModelTests}.lean`
  with `Palomar/comparator-metabelian-boone-higman.json` (0db476348, 09-13).
  - Theorems: `MetabelianBooneHigman.finitely_presented_metabelian_embeds_in_finitely_presented_simple`
    (BBMZ 5.3(7)) and `..._finitely_generated_...`.
  - The challenge is Mathlib-only: `Group.IsFinitelyPresented`, `Group.FG`, `IsSimpleGroup`,
    `commutator`, plus two shared-block defs (`IsMetabelianGroup`,
    `EmbedsInFinitelyPresentedSimpleGroup`).
  - The Solution is a SKELETON: it proves only the `_of` forms from
    `GroupApproximation.BooneHigman.FinitelyGeneratedMetabelianStatement`.
  - The config is in NEITHER gate tuple, so `check_palomar_submission.py` does not see it.
    It should be added to `PALOMAR_PENDING_CONFIGS`.

**Lean development.**
- `GroupApproximation/BooneHigman/` has 819 files, 793 of them in `Metabelian/`.
- `Statement/Basic.lean` (Mathlib-only) defines T1 `FinitelyPresentedMetabelianStatement`,
  T2 `FinitelyGeneratedMetabelianStatement` and T3 `FinitelyGeneratedLinearStatement`
  (f.g. subgroups of `GL (Fin n) K`, any field K).
- `Products/Assembly.lean`: T2 ⇐ `MetabelianPiecesStatement` ∧ `FPSelfSimilarEnvelopeStatement`
  (Zaremsky 2405.09722 Thm 1.1).
- `Products/Hosts.lean`: T3 ⇐ `LinearHostStatement` ∧ the same envelope statement.
  `LinearHostStatement` is not discharged anywhere.
- **Latest wiring:** `Metabelian/ChainWiredFrontierThree.lean` (093b018ce, 09-17). T1 follows
  from 10 named gap Statements; the file itself marks each as classically true:
  1. `PureCharPrimeEHighModuleStatement`
  2. `SuslinLocalHorrocksStatement`
  3. `VdKRowExtensionStatement`
  4. `PolyK2CubeNilLocalStatement`
  5. `FieldK2.BruhatBigCellStatement`
  6. `CharZeroK2PosStabGenStatement`
  7. `CharZeroK2CubeGapPosStatement`
  8. `HigmanVSwapSectionStatement`
  9. `RNRelatorsFiniteCoreStatement`
  10. `GenTorsionVPerfectStatement`
- **Owner.** Another Claude session runs `bh-met-*` lanes: 360 BooneHigman commits since
  09-18 00:00, session id ending `…LbuV`. It is actively closing these gaps
  (e.g. 2b7546df7 "Suslin monic stabilization, local case"). Treat
  `GroupApproximation/BooneHigman/**` and the metabelian pair as ITS paths.
- **Reusable pieces:**
  - `GroupApproximation/BooneHigman/V/` (7 files: V on Cantor space, supports, transitivity,
    cone swaps);
  - `GroupApproximation/GroupTheory/HigmanThompson/` (18 files: Brown presentation, compact
    core, germs);
  - `GroupApproximation/TypeA2/` (the type (A) definition `IsTypeA2`, finite-presentation
    retracts and extensions, from the FFWZ 5.8 pair).

## 1. Candidate BH results

"Lit" means bh-lit's survey (d7b638fef), flag F1. That flag marks results the repo calls
ESTABLISHED while the literature still lists them open. "Verify" means an adversarial check
is running (bh-verify-metabelian, bh-verify-linear, bh-verify-artin). Per
[[lean-only-after-solving]], formalize a Tier A item only after its verify lane reports
"chain holds".

| Tier | Result (node) | Named problem | Lit | Verify | Lean distance |
|---|---|---|---|---|---|
| A1 | f.p. metabelian embed in f.p. simple (`fp-metabelian-groups-satisfy-boone-higman`) | BBMZ 5.3(7) | open in lit (F1) | bh-verify-metabelian | 10 gaps; owned by the other session |
| A2 | f.g. metabelian (T2) | 5.3(7), stronger form | same | same | same chain |
| A3 | f.g. linear over ANY field (`finitely-generated-linear-groups-satisfy-boone-higman`, ff3174b2a) | beyond the survey (5.3(5) is GL_n(Q) itself) | open in lit (F1) | bh-verify-linear | needs `LinearHostStatement`: char-0 coordinates to GL over Z[1/m][t̄] (exists in `Coordinates/`, `CharZeroCoords*`), char-p Nagata host (`CharPCoords*`, `CharPHost/`), and full, not only quasi-linear, host assembly; shares the envelope half with A1 |
| B1 | spherical Artin incl. E6–E8, F4, H3, H4 (`spherical-artin-…`, `e-type-artin-…`) | part of 5.3(13) | open in lit (F1) | bh-verify-artin | via linearity (Krammer / Digne / Cohen–Wahl) plus A3; formalizing faithfulness of Krammer-type representations is very large |
| B2 | Problem 2.7 / Kourovka 14.10(c): explicit f.p. St_10(R_L) ⊇ every GL_n(Q) (`gl-n-q-explicit-natural-fp-overgroup`) | Kourovka 14.10(c) (P. de la Harpe), BBMZ 2.7 | refereed here | — | needs St_N(R) f.p. for f.p. R at rank ≥ 5 (repo's rank-five node), R_L by generators and relations, and the Leavitt-pair centralizer embedding; about 2–4 kLOC, independent of A1 |
| B3 | B̃_n, C̃_n Artin, even-FC (PBH) | part of 5.3(13) | open in lit (F1) | bh-verify-artin | needs twisted Brin–Thompson SV_G f.p. simple (BFFHZ / Zaremsky): not started, very large |
| C | 09-18 lane results: rf soluble finite rank (2075eddaf), CAT(0) with a tree factor (61db7e38a), full-Cantor-host PBH reformulation, free products iff joint embedding (800873ca4), BS(1,3) ≤ 3V, 2V_τ | mostly corollaries of imports (Pyber–Segal, BLIW Thm C, BFFHZ) | lane proofs | none | import-heavy except free products iff JE (elementary normal forms; Mathlib has `Monoid.Coprod` / `CoprodI.NormalWord`) and BS(1,3) ≤ 3V (needs a 3V definition) |

Items that are theorems of other authors (hyperbolic groups, Aut(F_n), BS(m,n), Zaremsky's
f.g. subgroups of GL_n(Q)) are not candidates on their own, per the 09-13 rule "do not
formalize open problems first solved by others". They enter only as Lean inputs.

## 2. Challenge rendering (ONE megaconfig)

Proposal: `Palomar/BooneHigmanChallenge.lean`, `Palomar/BooneHigmanSolution.lean`,
`Palomar/BooneHigmanModelTests.lean` and `Palomar/comparator-boone-higman.json`, namespace
`BooneHigman`. The shared block reuses the metabelian block byte for byte and adds only
what each theorem needs.

- `EmbedsInFinitelyPresentedSimpleGroup G := ∃ (S : Type) (_ : Group S),
  Group.IsFinitelyPresented S ∧ IsSimpleGroup S ∧ ∃ f : G →* S, Function.Injective f`.
- `IsMetabelianGroup G := ⁅commutator G, commutator G⁆ = ⊥`.
- **Theorem names:**
  - `fp_metabelian_embeds` and `fg_metabelian_embeds` (A1, A2);
  - `fg_linear_embeds : ∀ (K : Type) [Field K] (n : ℕ) (H : Subgroup (GL (Fin n) K)),
    H.FG → EmbedsInFinitelyPresentedSimpleGroup H` (A3; T3 verbatim);
  - later `explicit_fp_overgroup_of_all_gl_n_q` (B2), which needs the inline defs
    `leavittResolventRing` (a `RingQuot` of `FreeAlgebra ℤ (Fin 6)` by the 9 relators) and
    `SteinbergGroup n R` (a `PresentedGroup` on `x_ij(r)` symbols). "Prefer theorem
    statements to definitions" still allows this, because the explicit group IS the problem.
  - **Rejected alternative:** a Prop saying only "some f.p. group contains every GL_n(Q)".
    That is trivially Higman-true and does not render 2.7.
- **Solvable word problem.** It is not needed: every class above has solvable word problem
  automatically, and BBMZ 5.3 asks only for the embedding (the survey's Thm 5.1 form).
  - If the full conjecture or a conditional form is ever stated, render it as
    `∃ n (π : FreeGroup (Fin n) →* G), Function.Surjective π ∧
    ComputablePred (fun w : List (Fin n × Bool) => π (FreeGroup.mk w) = 1)`.
  - `List (Fin n × Bool)` is `Primcodable` in Mathlib. Add a model test that ℤ satisfies it.
- **Other class renderings, if they are ever needed:**
  - Artin groups: `PresentedGroup` of braid relations from a Mathlib `CoxeterMatrix`, with
    E8 etc. as literal matrices.
  - BS(m,n): a `PresentedGroup` on 2 generators.
- **Size.** Each theorem is about 10 lines and the shared block is under 60 lines, so the
  whole challenge stays under 300 lines, well within the warning line.
- **Model tests:** BS(1,2), ℤ≀ℤ and ℤ² are metabelian; `GL (Fin 2) ℚ`-subgroups are f.g.
  where expected; `IsSimpleGroup` of a known f.p. simple group.

## 3. Lean dependency graph and sizing

- **A1/A2** (other session): Frontier Three's 10 Statements. They are classical (van der
  Kallen stability, Suslin/Horrocks, Bruhat big cell for K_2(F_p)=0, Higman's V
  presentation/simplicity, Röver–Nekrashevych relators). This is the critical path of the
  whole megasubmission. The pace is visible in the commit log (dozens of commits a day).
- **A3** = A1's envelope half plus a full `LinearHostStatement`. New work:
  1. f.g. subring coordinates to `GL_N(ℤ[1/m][t̄])` or `GL_N(F_p[s̄])` (partly in
     `Coordinates/`, `CharZeroCoords*`, `CharPCoords*`);
  2. an affine self-similar host for `E_N` over those rings, with its finite presentation
     (the K_2 control in `ElemFPCharZero*` / `ElemFP*`);
  3. assembling T3 from these rather than from quasi-linear pieces.

  Estimate: medium, since it reuses most of A1's modules. Scouting must confirm which
  modules already cover the full linear case.
- **B2:** St_N(R) f.p. for f.p. R and N ≥ 5, the direct proof node's relation families
  (B1)/(B2) and 630 generators for St_10(F_6), plus the ring R_L and the embedding.
  Independent of A1. Estimate 2–4 kLOC.
- **B1/B3:** Krammer faithfulness, or twisted Brin–Thompson SV_G f.p. simple. Each is a
  multi-week Mathlib-scale build. Defer.
- **C:** free products iff JE, about 1–2 kLOC on `Monoid.Coprod` normal forms. The rest is
  import-heavy; defer.

## 4. Proposed lane split (our session; disjoint paths)

| Lane | Owns | Job |
|---|---|---|
| bh-pal-surface | `Palomar/BooneHigman{Challenge,Solution,ModelTests}.lean`, `Palomar/comparator-boone-higman.json`, `scripts/PalomarBooneHigman{Axioms,ChallengeType,SolutionType}.lean`, gate tuple rows | Write the Mathlib-only challenge and model tests, and a skeleton Solution with `_of` forms from `Statement.API`. Register the config in `PALOMAR_PENDING_CONFIGS`, and the metabelian config too. |
| bh-pal-t3-scout | report only | Map exactly which `BooneHigman/**` modules already give `LinearHostStatement` pieces, and what is missing for the full linear case. |
| bh-pal-t3-a / -b / -c | new dir `GroupApproximation/BooneHigmanLinear/` | char-0 host, char-p host, and T3 assembly, consuming BooneHigman only through interface lemmas. Launch after the scout. |
| bh-pal-steinberg | `GroupApproximation/SteinbergFP/` | B2: St_N(R) f.p. for N ≥ 5, R_L, and the St_10 embedding of GL_n(ℚ). |
| bh-pal-coprod | `GroupApproximation/BHClosure/` | C: free-product closure iff JE (elementary). |
| bh-pal-integrate | root `GroupApproximation.lean` insertions, wiring | Batch root imports above the `/-!` line; run the cyclecheck overlay and the duplicate-declaration scan before each wave; trigger the Palomar check. |
| bh-pal-yaml | `formalization.yaml` (only on the user's go) | Rewrite the metadata for the BH config when its Solution loses every hypothesis. |

**MSI build protocol**, from memory; every lane follows it:
- Trusted builds only through `scripts/remote-build.sh`, which holds the fleet mutex.
  Single-file iteration may use lock-free `lake env lean`.
- `LEAN_NUM_THREADS=8`. Touch the sources after rsync.
- End each remote command with a sentinel, and verify md5 on the remote inside the same
  invocation.
- A red or green from an unmutexed build is not evidence either way.
- Root imports go above the docstring. Before landing, check the root with
  `awk '/^\/-!/…'`.
- Never cancel prover CI runs. No local builds. Use the lander only, and never `git fetch`
  in lanes.

## 5. Blockers and user decisions

1. **One submission per config.** `formalization.yaml` now describes surjunctive-nonsofic.
   A "megasubmission" is either one BH config with many `theorem_names` (proposed), or
   several BH configs submitted separately. Switching the yaml is the user's call. It
   should happen only when that Solution is hypothesis-free, since a pending pair publishes
   nothing.
2. **Cross-session ownership.** The metabelian chain and its pair belong to session
   `…01M3P…` (bh-met lanes). Decide whether the BH megapair wraps that pair's endpoint
   (proposed: import `Statement.API` only) or whether the user merges the two campaigns.
   Our lanes must not write under `GroupApproximation/BooneHigman/`.
3. **Scope rule conflict.** The 09-13 rule is "only open problems we solved". The 09-18
   order is "all BH results". Imported-theorem classes (Artin via linearity, PBH via
   BFFHZ/BLIW, hyperbolic) would each need a large literature formalization. Recommend
   A1–A3 plus B2 now and deferring B1/B3/C, unless the user wants the literature
   formalized.
4. **Verification first.** A1, A3 and B1 are flagged by bh-lit F1 as open in the
   literature. Formalize them (or at least submit them) only after bh-verify-* report the
   chains hold.
5. **Gate hygiene.** `comparator-metabelian-boone-higman.json` is invisible to the gate;
   add it to `PALOMAR_PENDING_CONFIGS`.
6. **Surface rules.** American English. No `research/*.md` references on the submission
   surface. Credit wording as in the current yaml `sources` block (contributors listed by
   role; "under the user's direction"). Human names only in authors/maintainers.
7. **Ops.** Disk dropped under the lander's 2 GiB floor earlier today. Lean builds happen
   on MSI only.
