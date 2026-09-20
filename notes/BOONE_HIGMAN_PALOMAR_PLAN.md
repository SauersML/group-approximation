# One combined Boone–Higman Palomar submission

Plan updated September 20, 2026, following the user's decision to make one BH
megasubmission. This is the current release plan. Earlier scope and “stage 1”
notes remain records of prior planning, not separate release commitments.

The user has now explicitly selected the strongest results and open-question
answers in the three September 20 manuscripts for this same submission, using
them as correct working proofs with repairs as needed. The
[selected additions and exact statements](BOONE_HIGMAN_PALOMAR_SELECTED_SCOPE.md)
are part of the intended package. They are not candidates waiting for another
scope approval or an independent-referee prerequisite; Lean proof and release
verification obligations remain.

The deliverable is one immutable repository revision, one Comparator
configuration (`Palomar/comparator-boone-higman.json`), one challenge/solution
pair, and metadata describing exactly the selected theorems. Development can
proceed in milestones, but the four-theorem checkpoint is not the planned final
submission. Palomar supports multiple selected declarations in one entry and
reviews them together: [submission contract](https://github.com/PalomarRegistry/PalomarSubmission#readme).

## Intended mathematical scope

The headline package is linear and metabelian embeddings, the self-similar host
theorem, graph-product closure, and the ascending-HNN consequence. Retain the
four current construction/permutation-group endpoints. Assess the related
structural results below for inclusion in the same entry before freezing the
manifest. An unresolved intended result remains an explicit blocker or scope
decision; it must not silently become a conditional theorem or a separate entry.

| Result family | Intended statement | Current evidence and remaining work |
| --- | --- | --- |
| Linear groups | Every finitely generated linear group over any field satisfies BH; include the stronger PBH form once its bridge is closed. | [Written proof](../research/finitely-generated-linear-groups-satisfy-boone-higman-proof.md). `CharZero/RouteNoSuslin.lean` removes S1; P1, Z1 and H1 remain. |
| Self-similar hosts | Every finitely generated linear group embeds in a finitely presented self-similar group, answering LISW Q1.11. | `linearHost_noSuslin` needs P1 and Z1. The [existing Palomar bridge](../GroupApproximation/BHPalomar/LinearSelfSimilar.lean) still uses the older S1/P1/Z1 route and needs to be updated. H1 is not needed. |
| Metabelian groups | Finitely generated metabelian groups satisfy BH, with the finitely presented form identifying BBMZ 5.3(7); include PBH when proved. | [Current solution skeleton](../Palomar/MetabelianBooneHigmanSolution.lean) assumes the development endpoint. Close the common linear/envelope chain and integrate these declarations into the combined pair. |
| Graph products | PBH is closed under graph products over every finite graph, answering BFFHZ Q3.1. | [Current endpoint](../GroupApproximation/BHPalomar/GraphProducts/Main.lean) assumes `EnvelopeInput`. Product closure and the retract-amalgam construction are already supplied in the development. |
| Ascending HNN extensions | Every injective endomorphism of a finite-rank free group has a mapping torus satisfying PBH and embedding in a simple F∞ group. | [Written proof](../research/ascending-hnn-of-free-groups-bh-proof.md). Locate reusable Hall/HNN and BLIW developments, then formalize and expose the exact endpoint; no such theorem is currently selected by the combined configuration. |
| Concrete rational-linear host | `St_10(R_L)` is finitely presented and contains every `GL_n(ℚ)`. | Existing selected declaration `BooneHigman.explicit_fp_overgroup_of_all_gl_n_q`. Retain the concrete construction and use the narrower novelty wording below. |
| Class-transposition results | Kourovka 17.59, Kourovka 21.75, and Kohl's factorization conjecture. | Existing selected declarations `BooneHigman.kourovka_17_59`, `BooneHigman.kourovka_21_75`, and `BooneHigman.kohl_factorization_conjecture`. Factorization is a consequence, not a separate independent mechanism. |
| Spherical Artin groups | Deduce BH/PBH from the linear theorem and faithful linear representations. | [Written consequence](../research/spherical-artin-groups-satisfy-permutational-boone-higman.md). A standalone selected theorem also requires formalizing the relevant linearity theorem; it cannot inherit that theorem merely through a citation. |
| Twisted Brin–Thompson finiteness | Conjecture H and the abstract extension, including finite n ≥ 3. | [Written criterion](../research/twisted-brin-thompson-type-fn-criterion.md). Independently audit the interval-filtration proof, then inventory and close its Lean dependencies. |
| Mixed identities | Thompson T gives a negative answer to BFFHZ Q3.3. | [Written result](../research/thompson-t-mixed-identities-are-not-finitely-normally-generated.md); partial development under `GroupApproximation/BHPalomar/MixedIdentities/`. Trace all remaining hypotheses before selecting an endpoint. |
| Action kernels | FFWZ Q5.8 and Q5.9, with their exact distinct quantifiers. | Q5.8 has an existing [Palomar solution](../Palomar/TypeA2Solution.lean). Q5.9 requires auditing the repaired Bartholdi–Mitrofanov recursion and both claimed parts before formalization. The Q5.8 formal witness and the diagonal-normalizer written witness are different constructions; document which one is certified. |

Before scope freeze, reconcile the remaining class-transposition questions and
other candidates in the [research ledger](../research/artifacts/gq-bh-results-summary.md).
Record an explicit include/defer/prior-work decision for each relevant candidate.
That ledger's counts are not the submission's theorem count or proof status.
Broader Euclidean-building results require a separate geometry audit and a
comparison with the September 2026 literature before inclusion.

## Novelty and statement fidelity

The September 20 comparison supports likely novelty, not a certified priority
claim. Preserve these distinctions in the README, manuscript and final metadata:

- The all-field linear theorem extends [Zaremsky's rational-linear result](https://arxiv.org/html/2405.09722v2).
  The self-similar host answers [LISW Q1.11](https://arxiv.org/html/2510.01952v1),
  not their stronger finiteness-preserving quasi-retract question Q1.10.
- Metabelian and spherical-Artin conclusions are consequences of the linear
  theorem and credited existing structure results. The [BH survey](https://arxiv.org/html/2306.16356v3)
  identifies the metabelian problem.
- Graph-product closure answers [BFFHZ Q3.1](https://arxiv.org/html/2503.21882v2).
  The HNN result is a new embedding/deduction using [BLIW](https://arxiv.org/html/2408.05673v2),
  not an original proof of their host theorem.
- Conjecture H's remaining finite-n direction and the action-kernel questions
  are explicitly discussed in [FFWZ](https://arxiv.org/html/2603.24687v2).
  The kernel obstructions do not disprove BH or settle BH versus PBH.
- For the rational-linear host, credit [Mikaelian's earlier announcement, §1.4](https://arxiv.org/html/2507.04347v8).
  Describe the common explicitly presented Steinberg construction; do not claim
  the first explicit finitely presented overgroup. This host is not asserted simple.
- The Titz–Witzel PBH examples are already in [Le Bars–Leibtag–Vigdorovich](https://arxiv.org/html/2609.17129v1).
  Known rational-linear cases, free-by-cyclic cases, and literature-only simple
  group constructions are background or consequences, not additional new results.

No selected theorem may take the desired conclusion, a literature theorem still
unproved in Lean, or a renamed gap statement as an extra assumption. Ordinary
mathematical hypotheses such as finite generation and injectivity remain part
of the intended statement. Review the definitions as well as theorem types:
faithfulness, finiteness, characteristic, universes and simplicity must match
the mathematical claims.

## Work order and completion criteria

The [September 20 Lean progress report](BOONE_HIGMAN_LEAN_PROGRESS_2026-09-20.md)
records the new checked proofs, import reductions and precise remaining
mathematical obligations. It does not certify the combined submission.

1. **Freeze the statement inventory.** Give each intended endpoint its exact
   quantifiers, source question, written proof, Lean declaration or missing
   declaration, dependency list, novelty category and decision. This table is
   the starting inventory, not a claim that every listed declaration exists.
   Audit the delicate finiteness, kernel and building arguments before investing
   in their full formalizations. Group consequences under their main mechanism.

2. **Close the shared linear and metabelian dependencies.** Use
   [RouteNoSuslin](../GroupApproximation/BooneHigmanLinear/CharZero/RouteNoSuslin.lean),
   which already bypasses the older route's S1 absorption input:
   P1 is `∀ p, p.Prime → Metabelian.ElemFP.PolyK2NilGapStatementOver (ZMod p) 4`;
   Z1 is `Metabelian.ElemFPCharZero.CharZeroK2SplitGapStatement`;
   H1 is `Metabelian.Envelope.HigmanVCStepBCoreStatement`.
   First locate any already completed proofs deeper in the development, then
   discharge what remains. Closing P1/Z1 gives the self-similar host theorem;
   adding H1 gives the BH linear/metabelian endpoints. Separately close the
   stronger PBH bridge. Completion means closed declarations whose dependency
   axioms have been audited, not just compiling conditional assembly lemmas.

3. **Close PBH closure and the remaining selected results.** Prove
   `GraphProducts.EnvelopeInput` from formalized BFFHZ ingredients, compose it
   with the existing graph-product proof, and close the HNN reduction and its
   host inputs. Reuse the same action/envelope machinery for the other selected
   results. Literature inputs are proof obligations even when they are not
   advertised as new theorems.

4. **Integrate one submission surface.** Extend
   `Palomar/BooneHigmanChallenge.lean` and `Palomar/BooneHigmanSolution.lean`, with
   one shared definition block and one selected theorem list. Merge the
   metabelian and Q5.8 surfaces into it, preserving the mathematical statements
   and credit. After replacing references, remove the redundant standalone BH
   configurations, wrappers and gate entries; keep reusable development modules.
   Do not manufacture unconditional wrappers while proofs remain open. Update
   the Comparator JSON, `formalization.yaml`, model controls, axiom driver and
   challenge/solution type-report drivers in the same integration change.
   Rewrite the metadata title and abstract around the final combined result;
   remove release-stage language and record actual contributor roles.

5. **Wire verification to the selected package.** The inspected tree has BH Lake
   targets, but they are absent from `defaultTargets` and the explicit build list
   in `.github/workflows/palomar-comparator.yml`. The prefix loop in
   `scripts/check_palomar_statement_match.sh` also omits `BooneHigman`, despite
   existing BH type-report drivers. Fix these omissions. Ensure the combined
   manifest, `status.main_results`, both type-report drivers and
   `scripts/PalomarBooneHigmanAxioms.lean` name exactly the same theorem set.
   Run the metadata gate with PyYAML available; a skipped YAML check is not a pass.
   Check challenge size early: the current local gate caps it at 1,000 lines and
   100 KiB. Recheck the current registry policy before freezing the release.

6. **Replay and release the complete package.** Build the selected modules and
   model controls, compare elaborated statements, audit every selected theorem
   transitively, and run Comparator plus independent NanoDa replay. The current
   [registry verifier](https://github.com/PalomarRegistry/PalomarSubmission#readme)
   requires both kernels; local source checks alone do not reproduce that check.
   Run the pinned official full preflight on the immutable candidate revision,
   recording its verifier revision, configuration, reports and resource use.
   The combined import closure must fit the actual verification budget. Submit
   that one configuration only after the entire selected package passes.

## Release checklist

The [September 20 manuscript integration](../research/artifacts/boone-higman-cairn-integration-2026-09-20.md)
adds selected scope to this same submission plan: the strengthened direct RN
quotient obstruction and polynomially twisted solvable-group envelopes, with
their subsidiary results. Keep these attached to one combined BH package;
their inclusion in its verified theorem list requires complete Lean proofs,
with mathematical details repaired during implementation. The supplied proofs use explicit classical
inputs, and the polynomial script verifies only finite formulas. No new
unconditional Palomar declarations or submission entries are created from
these manuscripts alone.

The subsequent [Beyond polynomial germs draft](../research/artifacts/beyond-polynomial-germs/beyond_polynomial_germs.md)
adds selected mapping-torus, recurrence, noncommuting matrix-profile, scalar
germ-classification, and nonlinear-example results. Its compact-core SingFix
theorem is an independent proposed mechanism using BHM Theorem 2.1; the earlier
polynomial normal-filtration theorem is not assumed as a proved input. These
results share the same Lean and single-submission requirements above. The
selection and corollary grouping are fixed in the linked scope inventory.

- [ ] Final selected scope includes the headline results, with explicit decisions on all other candidates.
- [ ] Each result has a source, proof, accurate novelty statement and matching Lean semantics.
- [ ] All selected solution declarations exist without unfinished mathematical inputs.
- [ ] Transitive axiom closures use only `propext`, `Classical.choice` and `Quot.sound`.
- [ ] One BH configuration, pair and metadata theorem list; redundant BH surfaces are retired.
- [ ] Shared definitions match; the challenge uses only registry-allowed dependencies and fits its limits.
- [ ] BH build targets and elaborated-statement checks run in CI.
- [ ] Source/metadata checks, builds, model controls and statement comparisons pass.
- [ ] Comparator and NanoDa pass for every selected declaration on the candidate revision.
- [ ] Official full preflight report, resource measurements and revision are recorded.
- [ ] README and metadata describe exactly the final scope and actual review status.
- [ ] One combined entry is submitted and its identifier recorded.

Targeted MSI compilation and axiom audits are recorded in the progress report.
The combined package has not passed Comparator, independent replay, external
mathematical review or Palomar acceptance.
