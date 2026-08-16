# Non-MF manuscript: exhaustive proof-step ledger

Spec document: `non_mf_groups_exist.tex`.  Formal development: `GroupApproximation/`.

**Audited revision.**

| | |
| --- | --- |
| commit | `050f2c8358664f53214dd2bc2df4bfc00dc450f5` |
| `git hash-object non_mf_groups_exist.tex` | `33a0b08c87fed2acf358c9145d97b54a3ab3b281` |
| sha256 of the file | `c9d652df435846455a80423074ac62eb9b9a31af8eb85d74900207ea3e06c06d` |
| `wc -l` | 4196 |

The blob above is the **working-tree** blob at re-scan time: a peer session had the
file dirty, so it is not yet reachable from any commit.  `git hash-object` of the file
must reproduce it exactly for the rows below to be read as current.  (An earlier scan
in this audit did land on a clean tree, at blob `55e425cf`; both scans are recorded
because the rows were reconciled across them.)

**No row is keyed on a line number.**  Every row is anchored either on a `\label`
or on a verbatim phrase from the claim itself that occurs exactly once in the
comment-stripped manuscript, and the checker re-locates each anchor on every run.
Insertions anywhere in the preamble or body move no row.  (Verified live: the file
grew by several hundred lines during this audit while the gate stayed green.)

**Concurrent editing.**  Ten sessions share this checkout and the manuscript was
being rewritten while it was being read.  Nothing below is reported as a manuscript
defect: the `Edit` column is `NO` on all 505 rows, and every discrepancy the ledger
records is a gap on the Lean side or a mismatch between the two, never a claim that
the TeX is wrong.  Two observations about the TeX itself — the badge placement noted
in finding 5, and the retired paragraphs noted in a few rows — may simply be
mid-edit; they are flagged as things to re-check, not as errors.

The manuscript was under active revision throughout this audit: it grew from
3854 to 4262 lines, Theorem `thm:signfree` (`E/⟨w⟩` is not MF) was added, the
soficity of `W/⟨ζ⟩` moved into a corollary and back into
Theorem `thm:commutinglamp`, Question 1 was rewritten from "is `E/⟨w⟩` MF?" to
"what is `Rad_MF(E)`?", two new Section 12 endpoints appeared, and the badge
macro was reworked into margin notes.  Every row below was reconciled against
the revision named above, and the new material was audited on the same terms as
the rest.

`scripts/check_non_mf_proof_ledger.py` is what keeps the ledger attached to a
moving manuscript.  It re-derives the printed-statement digest of every anchored
environment and re-locates every prose probe, so a later revision cannot silently
invalidate rows — it names them.  When a printed statement really has been
reworded, re-read the rows on that anchor and then re-pin deliberately with
`--repin-digests`, which logs every digest it moves.  Prose probes are never
auto-repaired: a relocated paragraph is a claim that may have changed, and it
keeps failing until a human looks.

## What this document is, and why the existing gates are not enough

The repository already runs two synchronization gates over this manuscript:

* `scripts/check_non_mf_refs.py` — every `\leanverified{module}{decl}` badge resolves
  to a declaration that exists in the tree, in the named module;
* `scripts/check_non_mf_claim_manifest.py` — every numbered theorem-like environment
  occurs exactly once in `docs/NON_MF_NUMBERED_CLAIMS.json`, with a digest of its
  printed statement and at least one exact Lean mapping.

Both currently pass (94/94 badges, 55/55 numbered claims).  Neither answers the
question this ledger exists to answer:

> Has every fact used in the *proof* of each printed assertion been formally
> established, and is every inferential step the **same step** as the one printed?

Badge resolution is not evidence.  `exact <someTheorem>` certifies that *a* true
theorem exists with the advertised outer proposition; it says nothing about whether
the Lean proof travelled the printed road, whether the objects are the printed
objects, or whether some hypothesis is quietly importing an unformalized theorem.
This ledger is the step-level answer.  It covers *all* substantive mathematical
assertions of the manuscript, not only the 55 numbered environments: unnumbered
remarks, proof-bearing paragraphs, displayed constructions, and every inferential
step inside every printed proof.

## The grading standard

Four labels.  There is **no** "acceptable literature input" category.

| Label | Meaning |
| --- | --- |
| `EXACT` | Same assertion, same objects, same inference, fully Lean-proved. |
| `MISMATCH` | Lean proves it differently, substitutes an equivalent object, restricts the quantifier, reorders substantively, or strengthens/weakens so as to bypass the printed step. |
| `MISSING` | No complete Lean proof — **including** anything currently represented by an assumption, a conditional theorem, a literature interface, an axiom, a `sorry`, or supplied existence/reduction data. |
| `UNDER-SPECIFIED` | The printed text is a prose route with no determinate step content to bind; Lean supplies a proof the sentence merely gestures at.  `EXACT` would overstate what was checked, `MISMATCH` would blame Lean for the manuscript's compression. |

`UNDER-SPECIFIED` is the project-wide fourth mark introduced by
`docs/P13_STEP_AUDIT.md` and adopted here.  It is a claim about the *manuscript*,
not about Lean, and it is deliberately not a pass: a route sentence that no
determinate obligation can be read off is a place where "1:1" has no meaning yet.

The project is 1:1 with the manuscript only when **every** row is `EXACT` in both the
statement column and the proof column.  That is not the present state, and the
`MISMATCH`, `MISSING` and `UNDER-SPECIFIED` rows below are the correct output of the
audit, not a defect of it.

Two rules were applied uniformly, and they account for most of the non-`EXACT` rows:

1. **Quantifier scope is part of the assertion.**  Where the manuscript says "let `H`
   be a (countable) group" and the Lean statement reads `{H : Type}` — i.e. `Type 0`
   only — the Lean assertion is strictly narrower than the printed one and the row is
   `MISMATCH`, noted `univ0`.  The transfer "every countable group is isomorphic to
   one in `Type 0`, and the property is isomorphism-invariant" is true and routine,
   but it is not in the development, so it may not be assumed here.  Rows whose Lean
   statement really is universe-polymorphic (`∀ (G : Type u) …`) are not so marked.
2. **A step is `EXACT` only if a Lean declaration performing that step was read.**
   If the enclosing printed theorem is Lean-proved by a *different* decomposition, its
   individual printed steps are `MISMATCH` (the Lean proof does not go through them),
   even though the enclosing conclusion may itself be `EXACT`.  If the enclosing
   theorem is not Lean-proved at all, its steps are `MISSING`.

## Method

The TeX was read in full, in order.  For every claim the tree was searched starting
from the `\leanverified` badges, then `docs/NON_MF_NUMBERED_CLAIMS.json`,
`docs/NON_MF_CLAIM_DECLS.txt`, and direct grep.  Where a Lean declaration exists it
was opened and its proof read, together with the helper lemmas the proof delegates to,
to the depth needed to decide the proof-route column.  Declaration names in the `Lean`
column are written relative to the root namespace `GroupApproximation`, matching the
manuscript's own margin-note convention.

## Related audits, and what they overturned here

Three peer documents audit overlapping surfaces.  This ledger **cross-references
rather than duplicates** them: where one of them went deeper than this sweep did, its
verdict wins and the affected rows are marked `CORRECTED against …` in the `Note`
column.  Fifteen rows were corrected that way, all of them downgrades.

| Document | Surface | Relation to this ledger |
| --- | --- | --- |
| `docs/P13_STEP_AUDIT.md` | `sec:group`, `prop:literal-base-T`, `thm:p13-complete`, `rem:classical-base` | Overturns 8 rows: `BT.04` (split into `BT.04`–`BT.04d`), `BT.08`, `BT.08b`, `BT.09b`, `BT.13`, and `BT.19`–`BT.23b`.  Read it for the P13 material at full depth. |
| `docs/COLLAPSE_STEP_AUDIT.md` | `def:invwitness`, `thm:collapse` Steps 1–6, `rem:collapse-finite-stage` | Overturns 7 rows: `CO.04b`, `CO.07`, `CO.09`, `CO.09b`, `CO.11`, `CO.14`, `CO.14b`, `CO.14c`.  Read it for the collapse ladder at full depth, and for its findings S1–S8 about the manuscript. |
| `docs/NON_MF_CONDITIONAL_INVENTORY.md` | every badge's dependency surface | The authority on the `Deps` column: 7 of 100 badged declarations are mathematically conditional, 5 more carry a badge defect that is not conditionality.  Where its verdict and this ledger's `Deps` disagree, believe it. |

The correction pattern is worth naming, because it is the honest answer to "which rows
are least confident".  Every overturned row is one where I marked `EXACT` at a
granularity **coarser than the printed sentences** — one ledger row spanning four
printed assertions (`BT.04`), or a six-step ladder audited through module structure and
docstrings rather than through the 260-line proof body (`CO.*`).  Both peers read the
bodies and found real deviations.  Rows I audited at printed-sentence granularity, by
opening the proof, have held.

## Headline findings

1. **The printed proof of Theorem 3.1 is not the formalized proof.**  Section 3 prints
   an ultraproduct argument: the Hilbert-space ultraproduct `K_ω`, the norm
   ultraproduct `B_ω = ∏_ω B(K_n)`, faithfulness of its action, finiteness of `B_ω`
   (no proper isometries), a Kazhdan projection `P ∈ B_ω` obtained by continuous
   functional calculus at the isolated spectral point `1`, the one-sided compression
   `P ≤ Q = VPV*`, the isometry `σ = r + (1−Q)`, and `Q = P` by finiteness.  **None of
   that is in the development.**  There is no `C*`-ultraproduct of `B(K_n)`, no
   Murray–von Neumann comparison, no Kazhdan projection in an ultraproduct.  Lean's
   `KazhdanAsymptoticCommutant.transport` runs the *Appendix B* proof instead:
   finite-stage spectral projection `cornerProjection = spectralAbove(hermitianAverage …) θ`,
   the robust-gap eigenvalue exclusion, spectral capture, and the equal-rank flip
   `KazhdanCornerMatrices.norm_one_sub_mul_flip` (`‖(1−p)q‖ ≤ ε/√(1−ε²)`).
   Consequently the finite-stage appendix is `EXACT` in all 18 of its rows, while of
   the 30 rows of Section 3's printed proof 16 are `MISSING` and 10 are `MISMATCH` —
   even though the theorem's *conclusion* is genuinely proved.
2. **The other analytic spines are route-faithful, with two audited exceptions.**  The
   finite-normal Reynolds corner, the normal-Kazhdan moving spectral subspace, the
   Appendix A tensor-power normalization (including the printed `8 < Nδ²` constant),
   the Appendix B error bookkeeping, and the soficity of `W` (including the `2|k|/N`
   wrap-around estimate) all follow the printed road.  **Withdrawn on peer evidence:**
   my earlier verdicts that the involutive collapse ladder and the property-`(T)`
   bridge follow it step for step.  `docs/COLLAPSE_STEP_AUDIT.md` finds nine deviations
   in the collapse — the sharpest being that Step 6 is re-derived inline and neither
   cited transport theorem is ever invoked — and `docs/P13_STEP_AUDIT.md` finds that
   the printed spectral localization of Step 1 is absent (a Neumann/Richardson
   iteration with a weaker constant stands in its place) and that the "circumcenter"
   of Step 3 is a minimal-norm point of a closed convex hull.  The printed constants
   `κ/64`, `1/64`, `3/64`, `1/8` do match.
3. **36 rows carry a literature dependency; about a dozen of those are used in a
   deduction rather than cited for scholarship.**  The load-bearing ones: exactness of
   `C*_red(W)` (GHW, KW1, KW2), amenable ⇒ MF (TWW, used for the sharpness of the
   Kazhdan hypothesis in Theorem C), the simple sofic envelope (ES05), Adian–Rabin
   (Rabin58), Neumann's continuum family (Ne), nonamenability of infinite Kazhdan
   groups and nonnuclearity of `C*_red` of a nonamenable group (BHV, Lance), and the
   general amenable-quotient case of Elek–Szabó (only the `ℤ` case is formalized).
   The remaining literature rows are the "relation to prior work" attributions, which
   feed no deduction; their notes say so.  The manuscript declares the load-bearing
   ones itself; the ledger records all of them as `MISSING`, per the standard.
4. **Four rows are conditional by construction** — the torsion-free full-radical
   endpoints of Question 2 take `Nonempty (DefectRoutingData D)`, `ContinuumMultiplicity`
   takes Neumann's family as a quantified hypothesis, and Remark C.4's maximal-algebra
   endpoint is stated over a `StrictKazhdanCompression` datum.  All are labelled
   conditional in the TeX where the TeX mentions them.
5. **One badge under-certifies its remark** — *possibly mid-edit, re-check.*  The
   badge macro was being rewritten into margin notes during this audit, so badge
   placement is exactly the kind of thing that may still be in flight.
   Remark C.4 (`rem:maxinfinite`) asserts
   that for a group with strict Kazhdan compression the maximal algebra is not stably
   finite, carries no faithful trace, and is neither RFD nor MF, with `E` as the running
   example.  Its badge names `QuasiRegularWitness.baseVector_apply_base`, which says
   only that the point mass at the base coset takes the value `1` there.  The
   substantive content does exist in `Analysis/MaximalCStarProperCompression.lean`, but
   it is stated over a `StrictKazhdanCompression` datum and is instantiated
   (`Sofic/ChosenMaximalCStarInfinite.lean`) for the *Chosen* presentation, not for the
   literal eight-generator `E` of Definition 7.1.
6. **Universe scope.**  30 of the 56 `MISMATCH` statements are `MISMATCH` for `univ0`
   alone — the Lean statement fixes `Type 0` where the manuscript quantifies over all
   (countable) groups.  These are the cheapest rows in the ledger to close: either make
   the statements universe-polymorphic, or prove the countable-group transfer once and
   route every printed statement through it.
7. **The material added during the audit is in good shape.**  Theorem `thm:signfree`
   (`E/⟨w⟩` is not MF, so `{1,w}` is a *proper* subgroup of `Rad_MF(E)`), Corollary
   `cor:signfreesofic`, the dimension-free adjoint gap in Section 12, and the
   faithfully-traced coordinate no-go are all `EXACT` in both columns, step by step —
   including the parity argument that reduces the eight `(ℤ/2)³` conjugates of `d` to
   the marked word.

## Corpus hygiene (verified)

`sorry`: 0.  `axiom`: 0.  `native_decide`: 0.  Checked across `GroupApproximation/`.

## Status counts

<!-- LEDGER-COUNTS -->
| Column | EXACT | MISMATCH | MISSING | UNDER-SPECIFIED | total |
| --- | --- | --- | --- | --- | --- |
| statement | 396 | 71 | 63 | 1 | 531 |
| proof | 407 | 47 | 71 | 6 | 531 |
<!-- END-LEDGER-COUNTS -->

## Anchors

`env` anchors are labelled environments; the digest is the SHA-256 of the printed
statement, normalized exactly as in `scripts/check_non_mf_claim_manifest.py`
(environment delimiters, `\label`, and `\lean…` badges removed, whitespace collapsed),
truncated to 16 hex characters.  `sec` and `eq` anchors are labels only.  `prose`
anchors are unlabelled passages, located by a verbatim probe that must occur exactly
once in the comment-stripped manuscript; the probe is the drift detector.

<!-- LEDGER-ANCHORS -->
| Anchor | Kind | Locator | Digest |
| --- | --- | --- | --- |
| app:equivalences | sec | app:equivalences | - |
| app:finite-stage | sec | app:finite-stage | - |
| eq:corona | eq | eq:corona | - |
| eq:unitary-corona | eq | eq:unitary-corona | - |
| eq:unitary-corona-iso | prose | `Polar decomposition shows that` | - |
| eq:intrinsicdefect | eq | eq:intrinsicdefect | - |
| eq:involution-reversal | eq | eq:involution-reversal | - |
| eq:pinning | eq | eq:pinning | - |
| eq:sl3presentation | eq | eq:sl3presentation | - |
| eq:gamma-presentation | eq | eq:gamma-presentation | - |
| eq:generator-mass | eq | eq:generator-mass | - |
| prop:mf-equivalences | env | prop:mf-equivalences | 8fcbf4fc050755b2 |
| lem:lift | env | lem:lift | 721a3d635e21456f |
| lem:unitarycorona | env | lem:unitarycorona | acf85808aae67e89 |
| lem:finitecompare | env | lem:finitecompare | fc2a55b505fb0455 |
| lem:ultrafinite | env | lem:ultrafinite | 2bb52124d79d67fb |
| thm:kazhdan-transport | env | thm:kazhdan-transport | 36a5391cd928c3d3 |
| rem:finite-stage | env | rem:finite-stage | 34f3ec75670bdc39 |
| thm:transport-variants | env | thm:transport-variants | 70528198cea81006 |
| def:pattern | env | def:pattern | fbd43a8db929ff69 |
| def:invisible | env | def:invisible | f705f5984fdb3e68 |
| thm:criterion | env | thm:criterion | 4815ce19ed65a026 |
| thm:sign-criterion | env | thm:sign-criterion | 27a3e86c5351bfb6 |
| cor:generaltransport | env | cor:generaltransport | 13cf502a17267ad9 |
| thm:compression-radical | env | thm:compression-radical | f4e9fb766fe58572 |
| thm:normal-kazhdan | env | thm:normal-kazhdan | c365c0923105d3d0 |
| thm:abstract-nk | env | thm:abstract-nk | d93135ce6813697c |
| cor:intrinsic-nk | env | cor:intrinsic-nk | 74911f7eaffe314f |
| thm:kazhdan-clifford | env | thm:kazhdan-clifford | 0e8f49d2bd0f95a2 |
| rem:ff-realization | env | rem:ff-realization | 7dc2c4c67a341ebb |
| thm:A | env | thm:A | b22f1bb6c3a6afd1 |
| cor:uniform | env | cor:uniform | 043923ba46739c21 |
| cor:scaling-family | env | cor:scaling-family | 9370bcd0aa550f6e |
| thm:B | env | thm:B | 1a4fa9647cbcb3e2 |
| cor:notRFD | env | cor:notRFD | 754e7536fa06cde2 |
| rem:invariantsize | env | rem:invariantsize | aaae6ba6be6c706c |
| rem:chaincondition | env | rem:chaincondition | 1353d0d0ae9d8202 |
| def:E | env | def:E | 82744070e0aa91e5 |
| fig:compression-pattern | env | fig:compression-pattern | f0481ba0527fcf7f |
| prop:literal-base-T | env | prop:literal-base-T | 4955bce3c162ac27 |
| thm:p13-complete | env | thm:p13-complete | 32cf3b27267b128d |
| rem:classical-base | env | rem:classical-base | 3b14e3f10eb77180 |
| con:clifford | env | con:clifford | 9113a55c13a6227d |
| lem:linear | env | lem:linear | d64613d28a87f958 |
| prop:witness | env | prop:witness | 1a168e6eb3a8fb32 |
| lem:square | env | lem:square | 36940cc67e41844e |
| thm:C | env | thm:C | ee29ee959c43ba8b |
| def:radical | env | def:radical | c72c325fa0b06592 |
| lem:portable | env | lem:portable | 3cd3c8cd3e2d8419 |
| prop:univquot | env | prop:univquot | 7821f139d506b59e |
| cor:exactradical | env | cor:exactradical | cba1a12eca30acd6 |
| cor:pullback | env | cor:pullback | 8e8da0badc33b150 |
| prop:mfclosure | env | prop:mfclosure | 0cae9b9c9bafd14e |
| prop:sounditeration | env | prop:sounditeration | 85d7c0d6325a5de3 |
| cor:nofaithful | env | cor:nofaithful | c7cc4db7be975a5e |
| lem:permanence | env | lem:permanence | 5ec86a47bd0ca09d |
| cor:quotclosure | env | cor:quotclosure | 0945a411d7c96988 |
| prop:stabradical | env | prop:stabradical | 8143f23d621fe254 |
| def:invwitness | env | def:invwitness | df90cf17c2822610 |
| thm:collapse | env | thm:collapse | 88224a2caa8373a7 |
| rem:collapse-finite-stage | env | rem:collapse-finite-stage | a82d36046165c6dd |
| thm:projection-collapse | env | thm:projection-collapse | f8010458149ae59b |
| thm:torsion-collapse | env | thm:torsion-collapse | f46ea426294bbea1 |
| thm:commutinglamp | env | thm:commutinglamp | 789f8f26adab44b9 |
| cor:collapsequot | env | cor:collapsequot | bb1a2c2130afbac5 |
| thm:saturation | env | thm:saturation | 43eab2fa31ed26b9 |
| thm:D | env | thm:D | 3fbefcf7b1eaf4da |
| lem:faithfultrace | env | lem:faithfultrace | ed20bbd1df60ef72 |
| thm:E | env | thm:E | 0b84f58a967cd3a6 |
| thm:Esofic | env | thm:Esofic | 917c4fa5ef0893d9 |
| thm:markedclosed | env | thm:markedclosed | f666d6dd719b2ff9 |
| prop:horn | env | prop:horn | 3e2c6bb45f9627c7 |
| cor:cylinder | env | cor:cylinder | 847c38b2b21a9d92 |
| cor:undecidable | env | cor:undecidable | f9931601b5263c4e |
| prop:maximal-cstar | env | prop:maximal-cstar | 9d6deff51f869323 |
| prop:proper-isometry | env | prop:proper-isometry | 0243b2ca55a4d584 |
| rem:maxinfinite | env | rem:maxinfinite | d7117de503faf52d |
| p:abstract-refute | prose | `refutes the conjecture that every countable group is MF` | - |
| p:abstract-mechanism | prose | `the commutant becomes an asymptotic commutant in normalized Hilbert--Schmidt norm` | - |
| p:abstract-W | prose | `is itself finitely generated, sofic and not MF, so neither soficity nor` | - |
| p:intro-history | prose | `Residually finite groups satisfy the conjecture through their finite quotients` | - |
| p:intro-thom | prose | `In his 2018 ICM address, Thom asked for which Schatten` | - |
| p:intro-nonsofic | prose | `a nonsofic group was constructed by OpenAI` | - |
| p:intro-collapse-pointer | prose | `subsection gives a second application of one-sided compression` | - |
| p:intro-convention | prose | `Throughout, ``MF'' means this property, in the operator-norm sense` | - |
| p:intro-commutator | prose | `Throughout, $[g,h]=ghg^{-1}h^{-1}$` | - |
| p:intro-inputs | prose | `below, by an exact rational sum-of-squares certificate` | - |
| p:intro-slofstra | prose | `Slofstra's hyperlinear-profile construction uses a Clifford group` | - |
| p:intro-bekka | prose | `passage from operator norm to the Hilbert--Schmidt conjugation` | - |
| p:intro-slofstra-quotients | prose | `his quotients by the elements sent to the identity by all exact` | - |
| p:intro-dglt | prose | `Central extensions and rigidity of approximate representations also drive` | - |
| p:intro-cde | prose | `Carri\'on--Dadarlat--Eckhardt, who also give` | - |
| p:intro-final | prose | `therefore leaves open whether the group itself embeds` | - |
| p:prelim-complement | prose | `Complement correction gives the injective unitary homomorphism` | - |
| p:prelim-notation | prose | `We use without comment:` | - |
| p:prelim-defs | prose | `An \emph{operator-norm asymptotic representation} of $H$` | - |
| p:prelim-unit | prose | `Taking $g=h=1$ gives` | - |
| p:prelim-cmax | prose | `the maximal group $C^*$-algebra $\Cmax(H)$ is` | - |
| p:transport-display | prose | `In the right-hand column, $p\sim q$ is Murray--von Neumann equivalence` | - |
| p:transport-weights | prose | `The dimension weight $w_n=d_n$ recovers` | - |
| p:transport-tensors | prose | `Invariant tensors of type $(p,q)$ may be identified with Hilbert--Schmidt intertwiners` | - |
| p:conj-datum-remark | prose | `Both conditions are relations among generators` | - |
| p:conj-reynolds-only | prose | `The averaging-corner argument used only one property` | - |
| p:conj-two-element | prose | `there the averaging operator is` | - |
| p:conj-intrinsic-def | prose | `It depends only on the pair $(H,L)$, not on a choice of datum` | - |
| p:nk-finite-recovers | prose | `Finite groups have property~\textup{(T)}, so $K=F$ recovers` | - |
| p:nk-join | prose | `The subgroup generated by \emph{all} normal property-` | - |
| p:constr-tietze | prose | `The endomorphism $\alpha$ is injective because` | - |
| p:constr-role-of-a | prose | `$e_1\notin2\mathbb Z^3$, and $a\notin\alpha(\Gamma)$ for the same` | - |
| p:A-defect-square | prose | `Let $H_1$ be a group and $d,a_1\in H_1$ with $d^2=1$` | - |
| p:A-consequences | prose | `The theorems of this section show that every finite normal subgroup of` | - |
| p:B-applied | prose | `Applied to $H=E$, Theorem~\ref{thm:B} sends $w$ to the identity in` | - |
| p:B-deligne | prose | `In the terminology of \cite[Definition~1.2]{BDL}` | - |
| p:B-subgroup-valued | prose | `The same calculation proves the final, subgroup-valued assertion` | - |
| p:B-why-corona | prose | `An MF model is only asymptotically multiplicative, so its coordinate fixed spaces are not invariant subspaces` | - |
| p:group-sixgen | prose | `The eight-generator presentation is used because it displays` | - |
| p:group-tietze32 | prose | `eliminate $v_3=xv_1x^{-1}$` | - |
| p:group-figure | prose | `they do not constrain the commutators` | - |
| p:base-p13-aux | prose | `completeness of the thirteen-relator presentation` | - |
| p:witness-telescope | prose | `Form the direct limit $T=\varinjlim(\bar\Gamma,\bar\alpha)$` | - |
| p:witness-scope | prose | `each of its elements involves only finitely many Clifford generators` | - |
| p:A-marked-radical | prose | `consequently $\{1,w\}$ is a proper subgroup of` | - |
| p:A-corner-ranks | prose | `The coordinate averaging corner of` | - |
| p:C-sharpness | prose | `The realized Clifford quotient in Theorem~\ref{thm:C} is amenable` | - |
| p:C-approx | prose | `In every finite group the doubling relation makes the image of` | - |
| p:radical-presentation | prose | `For a presentation $G=\langle X\mid R\rangle=F/N$` | - |
| p:radical-sound-rules | prose | `are sound rules in this sense` | - |
| p:stability-def | prose | `there are genuine finite-dimensional unitary representations` | - |
| p:stability-axis | prose | `For a stable group the two radicals therefore agree` | - |
| p:collapse-wreath | prose | `In a permutational wreath product` | - |
| p:collapse-relcomm | prose | `The witness here need not come from a group element` | - |
| p:collapse-lamp-intro | prose | `by its central involution all lamps commute` | - |
| p:collapse-route-closed | prose | `is sofic and is not MF` | - |
| p:collapse-universal | prose | `is the universal MF quotient of $H$` | - |
| p:saturation-remark | prose | `A group as in (2) admits no nontrivial finite-dimensional unitary` | - |
| p:D-preamble | prose | `Every MF algebra is stably finite` | - |
| p:D-base-injective | prose | `$\mathcal B\to E$ is injective` | - |
| p:E-extension | prose | `MF groups are not closed under extensions.` | - |
| p:E-zext | prose | `canonical projections gives a surjection $W\to\Z$` | - |
| p:E-exact | prose | `The same witness gives a concrete separable exact example` | - |
| p:E-simple | prose | `There is a countable simple sofic group` | - |
| p:markedlimit-intro | prose | `The explicit clopen cylinder constructed in the next subsection` | - |
| p:horn-intro | prose | `can be read as one first-order fact` | - |
| p:undec-markov | prose | `make MF a Markov` | - |
| p:undec-adianrabin | prose | `run over a group built from a machine` | - |
| p:mult-products | prose | `The groups $E\times\mathbb Z^{k}$ for $k\ge0$ are` | - |
| p:mult-continuum | prose | `Beyond finite presentation, pairing $E$` | - |
| p:limits-opnorm | prose | `The proof is specific to the operator norm.` | - |
| p:limits-dilution | prose | `amplification by an identity block separates the two` | - |
| p:limits-alekseev | prose | `This is a limitation of the method, not a tracial nonapproximation` | - |
| p:limits-trace | prose | `Finite dimensionality of the coordinates is essential in a second,` | - |
| p:questions-torsion | prose | `The finite-normal criterion has a precise torsion limitation` | - |
| p:q1 | prose | `What is $\operatorname{Rad}_{\mathrm{MF}}(E)$?` | - |
| p:q2 | prose | `Is there a torsion-free finitely presented non-MF group?` | - |
| p:q3 | prose | `are not decided by the operator-norm method: the adjoint spectral estimates` | - |
| p:q4 | prose | `Does MF imply hyperlinearity?` | - |
| p:appA-localmodel | prose | `An \emph{approximate unitary representation} for a countable group` | - |
| p:appC-construction | prose | `is the completion of the group ring` | - |
| p:appC-universal | prose | `Injectivity comes from the left regular representation, uniqueness from` | - |
| p:appC-separate | prose | `The maximal and reduced algebras separate already at the level of` | - |
| thm:signfree | env | thm:signfree | 1aeef33c21dab5e1 |
| p:signfree-second | prose | `non-MF group. \begin{corollary}[collapse computes the radical]` | - |
| p:limits-adjointgap | prose | `The failure is exact and dimension-free` | - |
| p:limits-nogo | prose | `matrix coordinates are replaced by finite faithfully traced unital` | - |
<!-- END-LEDGER-ANCHORS -->

## Steps

Column key.  `Stmt` = statement status; `Proof` = proof-route status; `Obj` = object
identity (`literal` / `substituted`); `Deps` = dependency status (`unconditional` /
`conditional-data` / `literature-input` / `open`); `Source` = external source the TeX
cites for the step, `-` if none; `Edit` = whether a TeX edit is permitted (`NO`
everywhere: the TeX is the specification and does not move).

<!-- LEDGER-STEPS -->
| Step | Anchor | Claim | Lean | Stmt | Proof | Obj | Deps | Source | Edit | Note |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| INT.01 | p:abstract-refute | an explicit finitely presented group E is not MF, refuting the MF conjecture | `LiteralNonMFEndpoint.manuscriptTheoremA` | EXACT | EXACT | literal | unconditional | - | NO | concrete group in Type 0, so no universe gap |
| INT.02 | p:abstract-refute | C*_red(E) is separable, stably finite, not MF | `LiteralNonMFEndpoint.manuscriptTheoremD` | EXACT | EXACT | literal | unconditional | - | NO | - |
| INT.03 | p:abstract-mechanism | rigidity: if tΓt⁻¹ ⊆ Γ then conjugation by t preserves the HS asymptotic commutant of Γ | `KazhdanAsymptoticCommutant.manuscriptKazhdanTransport` | MISMATCH | MISMATCH | literal | unconditional | - | NO | univ0; and the Lean route is Appendix B, not the printed §3 ultraproduct proof |
| INT.04 | p:abstract-mechanism | in E this forces the commutator u to converge to 1 in normalized HS norm | `LiteralNonMFEndpoint.kazhdanPinning` | EXACT | MISMATCH | literal | unconditional | - | NO | route via Appendix B |
| INT.05 | p:abstract-mechanism | an explicit Clifford-group quotient makes the central involution w = u² equal to −1 | `LiteralNonMFLinearWitness.literal_mark_ne_one` | EXACT | EXACT | literal | unconditional | - | NO | - |
| INT.06 | p:abstract-mechanism | the construction applies to any f.p. property-(T) group with a proper injective self-embedding | `KazhdanCliffordConstruction.kazhdanCliffordConstruction` | EXACT | EXACT | literal | unconditional | - | NO | - |
| INT.07 | p:abstract-W | W is finitely generated, sofic, hyperlinear and not MF | `NonMFImpact.witness_sofic_hyperlinear_nonMF` | EXACT | EXACT | literal | unconditional | - | NO | - |
| INT.08 | p:abstract-W | C*_red(W) is in addition exact | - | MISSING | MISSING | - | literature-input | GHW, KWPermanence, KWExact | NO | no definition of exact C*-algebra in the development; the TeX says so |
| INT.09 | p:intro-history | residually finite groups are MF through their finite quotients | `isOperatorMF_of_residuallyFinite` | EXACT | EXACT | literal | unconditional | - | NO | - |
| INT.10 | p:intro-history | LEF groups are MF | - | MISSING | MISSING | - | literature-input | CDE | NO | context only, not used in a deduction |
| INT.11 | p:intro-history | all amenable groups are MF, by quasidiagonality | - | MISSING | MISSING | - | literature-input | TWW | NO | used in a deduction at CY.12 |
| INT.12 | p:intro-history | MF is known for many amalgamated free products | - | MISSING | MISSING | - | literature-input | Schafhauser, Shulman, GKEMP | NO | scholarship only |
| INT.13 | p:intro-history | C*_red(F₂) is MF (Haagerup–Thorbjørnsen) | - | MISSING | MISSING | - | literature-input | HT | NO | scholarship only |
| INT.14 | p:intro-history | the negative solution of CEP supplies abstract stably finite non-MF algebras | - | MISSING | MISSING | - | literature-input | MIPRE, FGH | NO | scholarship only |
| INT.15 | p:intro-thom | Schatten p-approximation fails for p = 2, for 1 < p < ∞, and for p = 1 | - | MISSING | MISSING | - | literature-input | DGLT, LuO, BDL | NO | scholarship only |
| INT.16 | p:intro-nonsofic | the Hamming case was disproved in 2026 (OpenAI, Fournier-Facio, Kun–Thom) | - | MISSING | MISSING | - | literature-input | OAI, FFF, KT | NO | scholarship only |
| INT.17 | p:intro-thom | this paper settles the operator-norm case, proves sofic ⇏ MF, and gives an explicit stably finite non-MF reduced algebra | `NonMFImpact.witness_sofic_hyperlinear_nonMF`; `LiteralWitnessConsequences.literalWitness_reducedGroupCStar_stablyFinite_nonMF` | EXACT | EXACT | literal | unconditional | - | NO | - |
| INT.18 | p:intro-convention | the fixed convention: MF = the operator-norm notion of Carrión–Dadarlat–Eckhardt | `IsCDEOperatorMF` | EXACT | EXACT | literal | unconditional | - | NO | definition matches eq:corona and the strict-increase convention |
| INT.19 | p:intro-convention | stronger conventions exist (GKEMP trace recovery; PMF of MdlS) | - | MISSING | MISSING | - | literature-input | GKEMP, MdlS | NO | scholarship only |
| INT.20 | p:intro-commutator | group commutator convention [g,h] = ghg⁻¹h⁻¹ | `Mathlib:commutatorElement` | EXACT | EXACT | literal | unconditional | - | NO | Mathlib's `⁅g,h⁆` is this convention |
| INT.21 | p:intro-collapse-pointer | second application of one-sided compression: orbit collapse computes the MF radical | `ManuscriptExactWrappers.manuscriptInvolutiveCollapse`; `ManuscriptExactWrappers.manuscriptDefectSaturation` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0 |
| INT.29 | p:intro-collapse-pointer | applied to E itself this shows E/⟨w⟩ is again not MF, so the marked sign certifies an obstruction surviving its removal | `LiteralSignFreeQuotient.signFreeQuotient_not_isCDEOperatorMF` | EXACT | EXACT | literal | unconditional | - | NO | added to the manuscript during this audit |
| INT.22 | p:intro-inputs | the proof of Theorem A is self-contained modulo the exact rational SOS certificate and machine-checked word computations | `LiteralP13HodgeCertificate.cleanP13Certificate` | EXACT | EXACT | literal | unconditional | - | NO | certificate is kernel-checked, no `native_decide` |
| INT.23 | p:intro-slofstra | Slofstra's precedents for the Clifford group, central involution, shift and HNN doubling | - | MISSING | MISSING | - | literature-input | SlofstraProfile, SlofstraVidick, BDL | NO | scholarship only |
| INT.24 | p:intro-bekka | the π⊗π̄ framework of Bekka and Bekka–Valette, and Dadarlat's HS almost-invariant projections | - | MISSING | MISSING | - | literature-input | BekkaAmenable, BekkaValette, Dadarlat | NO | scholarship only |
| INT.25 | p:intro-slofstra-quotients | Slofstra's invisible-element quotients precede the MF-radical language | - | MISSING | MISSING | - | literature-input | SlofstraCorrelations, Fritz | NO | scholarship only |
| INT.26 | p:intro-dglt | central extensions drive the DGLT Frobenius obstruction; BDL treat the finite-central case by a character-isotypic corner | - | MISSING | MISSING | - | literature-input | DGLT, BDL, GR, Gl19 | NO | scholarship only |
| INT.27 | p:intro-cde | CDE provide the group-MF framework, and an amenable MF group that is not residually finite | - | MISSING | MISSING | - | literature-input | CDE | NO | scholarship only |
| INT.28 | p:intro-final | failure of MF for the group algebra does not by itself prevent a corona embedding; for E the element w dies in every corona representation | `LiteralNonMFEndpoint.literal_mark_mem_manuscriptCoronaMFResidual` | EXACT | EXACT | literal | unconditional | - | NO | - |
| PRE.01 | eq:corona | definition of the norm matrix corona Q = ∏M_{d_n} / ⊕M_{d_n} | `NormMatrixCStarCorona` | EXACT | EXACT | literal | unconditional | - | NO | bounded ℓ∞ product modulo the c₀ ideal |
| PRE.02 | eq:unitary-corona | definition of the coordinate model U_cor((d_n)) | `NormMatrixCoronaUnitary` | EXACT | EXACT | literal | unconditional | - | NO | - |
| PRE.03 | eq:unitary-corona-iso | the denominator is normal, and polar correction gives a canonical isomorphism κ | `normMatrixCoronaUnitaryEquiv` | EXACT | EXACT | literal | unconditional | - | NO | normality is the subgroup construction `nullCofiniteOpSubgroup`; the claim lost its equation number when the paragraph was tightened, so the anchor is now the sentence rather than a `\label` |
| PRE.04 | prop:mf-equivalences | corona definition ⟺ unitary-sequence definition ⟺ local models with separation 1; arbitrary ⟺ strictly increasing dimensions | `ManuscriptExactWrappers.manuscriptMFDefinitionEquivalences` | EXACT | EXACT | literal | unconditional | - | NO | proof deferred to Appendix A, rows AE.* |
| PRE.05 | p:prelim-complement | complement correction u ↦ e(u) + (1 − e(1)) is an injective homomorphism U(A) → U(B) | `nonUnitalStarAlgHomUnitaryMap`; `nonUnitalStarAlgHomUnitaryMap_injective` | EXACT | EXACT | literal | unconditional | - | NO | - |
| PRE.06 | p:prelim-notation | normalized trace, operator norm, normalized HS norm on M_r(ℂ) | `hsNormSq`; `Mathlib:Matrix.l2_opNorm_mul` | EXACT | EXACT | literal | unconditional | - | NO | `hsNormSq` is tr_r(x*x); the manuscript's ‖x‖₂ is its square root |
| PRE.07 | p:prelim-notation | the three unnamed inequalities: ‖x‖₂ ≤ ‖x‖, the trace bound on the normalized trace, and ‖uxv‖₂ = ‖x‖₂ for unitaries | `hsDistSq_le_sq_l2_opNorm`; `hsNormSq_mul_left`; `hsNormSq_mul_right` | MISMATCH | MISMATCH | literal | unconditional | - | NO | the trace bound has no located declaration; the other two are present |
| PRE.08 | lem:lift | every unitary of Q lifts to a sequence of unitaries | `ManuscriptExactWrappers.manuscriptUnitaryLifting` | EXACT | EXACT | literal | unconditional | Loring | NO | - |
| PRE.09 | lem:lift | proof step: lift to a bounded sequence; unitarity gives ‖x_n*x_n − 1‖ → 0 | `unitaryCoronaToCStarCoronaUnitary_surjective` | EXACT | MISMATCH | literal | unconditional | - | NO | Lean proves surjectivity of the canonical map directly; the printed bounded-lift step is not a separate declaration |
| PRE.10 | lem:lift | proof step: once ‖x_n*x_n − 1‖ ≤ 1/2, polar correction u_n = x_n(x_n*x_n)^{-1/2} is unitary with ‖u_n − x_n‖ ≤ 2‖x_n‖‖x_n*x_n − 1‖ → 0 by CFC | - | MISSING | MISSING | - | unconditional | Loring | NO | the explicit polar-correction estimate with this constant is not a located declaration |
| PRE.11 | lem:lift | proof step: set u_n = 1 at the finitely many remaining indices | - | MISSING | MISSING | - | unconditional | - | NO | finite-exception patching is not separately stated |
| PRE.12 | lem:unitarycorona | κ is a canonical group isomorphism U_cor((d_n)) → U(Q) | `ManuscriptExactWrappers.manuscriptUnitaryCoronaEquivalence` | EXACT | EXACT | literal | unconditional | - | NO | includes the formula on represented sequences, which the TeX also displays |
| PRE.13 | lem:unitarycorona | proof step: the kernel is exactly the null unitary sequences, giving injectivity | `normMatrixCoronaUnitaryEquiv` | EXACT | EXACT | literal | unconditional | - | NO | the quotient is by that subgroup by construction |
| PRE.14 | lem:unitarycorona | proof step: surjectivity is Lemma lem:lift | `unitaryCoronaToCStarCoronaUnitary_surjective` | EXACT | EXACT | literal | unconditional | - | NO | - |
| PRE.15 | p:prelim-defs | definitions: corona representation, detection, operator-norm asymptotic representation | `OpAlmostRepresentation` | EXACT | EXACT | literal | unconditional | - | NO | the Lean structure carries exactly the printed asymptotic multiplicativity |
| PRE.16 | p:prelim-defs | a countable group is MF iff it admits an injective corona representation for a strictly increasing dimension sequence | `IsCDEOperatorMF` | EXACT | EXACT | literal | unconditional | - | NO | - |
| PRE.17 | p:prelim-unit | taking g = h = 1 gives ‖U_n(1) − 1‖ → 0 automatically | `KazhdanCornerMatrices.map_one_vanishing` | EXACT | EXACT | literal | unconditional | - | NO | - |
| PRE.18 | p:prelim-unit | coordinate unitary lifts of a corona representation of a countable group form such a sequence | `normMatrixCorona_lift_eventually_multiplicative` | EXACT | EXACT | literal | unconditional | - | NO | - |
| PRE.19 | p:prelim-cmax | C*_max(H) is constructed with its universal property in Appendix C | `manuscriptUniverseRelativeMaximalGroupCStar` | MISMATCH | MISMATCH | substituted | unconditional | - | NO | the Lean object is universe-relative, as the TeX itself says; the printed "the maximal group C*-algebra" is the class-sized one |
| TRA.01 | p:transport-display | the finite-set implication: a subset of a finite set of equal cardinality is the whole set | `Mathlib:Finset.eq_of_subset_of_card_le` | EXACT | EXACT | literal | unconditional | - | NO | not separately restated in the development |
| TRA.02 | p:transport-display | the finite-dimensional implication: V ⊆ W with dim V = dim W forces V = W | `fixedSubmodule_conjugate_eq` | EXACT | EXACT | literal | unconditional | - | NO | used exactly as the middle column of the display, in Theorem B |
| TRA.03 | p:transport-display | the C*-implication: p ≤ q with p ∼ q in a finite algebra forces p = q | - | MISSING | MISSING | - | unconditional | - | NO | no Murray–von Neumann comparison anywhere in the development |
| KT.00 | thm:kazhdan-transport | Theorem 3.1 as printed: forward transport of the HS asymptotic commutant along a one-sided conjugator | `KazhdanAsymptoticCommutant.manuscriptKazhdanTransport` | MISMATCH | MISMATCH | literal | unconditional | - | NO | univ0 (Γ, H : Type); the conclusion is proved, but by the Appendix B route |
| KT.01 | thm:kazhdan-transport | suppose the conclusion fails: fix γ₀, δ > 0 and an infinite I ⊆ ℕ with the commutator ≥ δ on I | - | MISSING | MISSING | - | unconditional | - | NO | the Lean proof is direct, not by contradiction along a subsequence |
| KT.02 | thm:kazhdan-transport | fix a free ultrafilter ω on ℕ with I ∈ ω | - | MISSING | MISSING | - | unconditional | - | NO | - |
| KT.03 | thm:kazhdan-transport | the adjoint model: regard M_{d_n}(ℂ) as K_n = L²(M_{d_n}, tr) with Ad U_n(g)ξ = U_n(g)ξU_n(g)* | `OpAlmostRepresentation.adjoint`; `conjDouble`; `KazhdanCompressorCorner.gammaRowVec` | EXACT | EXACT | literal | unconditional | - | NO | `conjDouble_mulVec_rowVec` is the printed identification |
| KT.04 | thm:kazhdan-transport | operator-norm almost multiplicativity makes g ↦ Ad U_n(g) an operator-norm asymptotic representation (finite-stage π⊗π̄) | `OpAlmostRepresentation.adjoint`; `KazhdanAsymptoticCommutant.adjointSequence_mul_hs` | EXACT | EXACT | literal | unconditional | BekkaValette | NO | - |
| KT.05 | thm:kazhdan-transport | form the Hilbert-space ultraproduct K_ω of the K_n along ω | - | MISSING | MISSING | - | unconditional | - | NO | - |
| KT.06 | thm:kazhdan-transport | form the norm ultraproduct B_ω = ∏_ω B(K_n) acting on K_ω | - | MISSING | MISSING | - | unconditional | - | NO | no C*-ultraproduct of bounded operators exists in the tree |
| KT.07 | thm:kazhdan-transport | the action of B_ω on K_ω is faithful (unit vectors nearly attaining the norm) | - | MISSING | MISSING | - | unconditional | - | NO | - |
| KT.08 | thm:kazhdan-transport | consequence: ran P ⊆ ran Q for projections of B_ω gives QP = P, i.e. P ≤ Q | - | MISSING | MISSING | - | unconditional | - | NO | - |
| KT.09 | thm:kazhdan-transport | π(g) = [Ad U_n(g)]_ω is a homomorphism H → U(B_ω) | - | MISSING | MISSING | - | unconditional | - | NO | - |
| KT.10 | thm:kazhdan-transport | B_ω is finite: σ*σ = 1 gives ‖σ_n*σ_n − 1‖ → 0 along ω, polar correction gives unitaries w_n, σ = [w_n]_ω is unitary | - | MISSING | MISSING | - | unconditional | - | NO | this is the load-bearing finiteness step of the printed proof; nothing corresponds to it |
| UF.01 | lem:ultrafinite | the norm ultraproduct is finite: an isometry of it is a unitary | `kt_06_ultraproduct_finite` | EXACT | EXACT | literal | unconditional | - | NO | the manuscript factored this out of the transport proof, so KT.10 above -- which records it as MISSING inside `thm:kazhdan-transport` -- is now covered here on its own anchor; header closed 2026-08-16 |
| FC.01 | lem:finitecompare | in a Dedekind-finite star ring, P ≤ Q for Q = VPV* with V unitary forces Q = P | `kt_10_finiteness_reverses` | EXACT | EXACT | literal | unconditional | - | NO | the ring-theoretic form (`PQ = P` and `QP = P`); this is the step Step 6 of `thm:collapse` cites for the reverse inclusion, and KT.08 above is its in-proof counterpart |
| KT.11 | thm:kazhdan-transport | property (T) provides a finite symmetric generating S ∋ 1 and a Kazhdan constant κ ∈ (0,1] | `KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair` | EXACT | EXACT | literal | unconditional | - | NO | used verbatim at the head of `transport` |
| KT.12 | thm:kazhdan-transport | let h be the Hermitian part of the S-average of the π(ι(s')) | `KazhdanCornerMatrices.hermitianAverage` | MISMATCH | MISMATCH | substituted | unconditional | - | NO | Lean's average lives at each finite stage, not in an ultraproduct |
| KT.13 | thm:kazhdan-transport | Fix and Fix^⊥ are invariant under each π(ι(s')), hence under h; h = 1 on Fix | - | MISSING | MISSING | - | unconditional | - | NO | no ultraproduct fixed subspace |
| KT.14 | thm:kazhdan-transport | a unit ξ ∈ Fix^⊥ is moved by ≥ κ by some generator | `IsKazhdanPair` | MISMATCH | MISMATCH | substituted | unconditional | - | NO | the finite-stage analogue is inside `hermitianAverage_eventually_no_intermediate_eigenvalues` |
| KT.15 | thm:kazhdan-transport | for that generator Re⟨π(ι(s'))ξ,ξ⟩ ≤ 1 − κ²/2, every other term ≤ 1 | - | MISSING | MISSING | - | unconditional | - | NO | - |
| KT.16 | thm:kazhdan-transport | averaging gives ⟨hξ,ξ⟩ ≤ 1 − κ²/(2·card S) | - | MISSING | MISSING | - | unconditional | - | NO | the Lean threshold is 1 − κ²/(4·card S), from the Appendix B argument, not this one |
| KT.17 | thm:kazhdan-transport | hence the spectrum of h lies in [−1, 1 − κ²/(2·card S)] ∪ {1} | `WeakMFVectorGNS.hermitianAverage_eventually_no_intermediate_eigenvalues` | MISMATCH | MISMATCH | substituted | unconditional | - | NO | the Lean statement is the eventual finite-stage eigenvalue exclusion at threshold κ²/(4·card S) |
| KT.18 | thm:kazhdan-transport | the spectral projection P of h at the isolated point 1 lies in B_ω by CFC and projects onto Fix | `KazhdanCompressorCorner.cornerProjection` | MISMATCH | MISMATCH | substituted | unconditional | - | NO | Lean uses `spectralAbove(hermitianAverage …) θ` at each stage |
| KT.19 | thm:kazhdan-transport | V = π(s), Q = VPV*; every vector of Fix is fixed by each π(sι(γ)s⁻¹) | `KazhdanCompressorCorner.one_sub_map_mul_rotated_vanishing` | MISMATCH | MISMATCH | substituted | unconditional | - | NO | the finite-stage rotated-corner statement |
| KT.20 | thm:kazhdan-transport | η is fixed by all π(sι(γ)s⁻¹) exactly when V*η ∈ Fix, so ran P = Fix ⊆ V·Fix = ran Q, i.e. P ≤ Q | `KazhdanCompressorCorner.one_sub_corner_mul_moved_vanishing` | MISMATCH | MISMATCH | substituted | unconditional | - | NO | finite-stage leakage bound in place of the exact inequality |
| KT.21 | thm:kazhdan-transport | r = V*Q satisfies r*r = Q, rr* = P; r = rQ and r = Qr | - | MISSING | MISSING | - | unconditional | - | NO | - |
| KT.22 | thm:kazhdan-transport | σ = r + (1 − Q) has σ*σ = 1: σ is an isometry | - | MISSING | MISSING | - | unconditional | - | NO | - |
| KT.23 | thm:kazhdan-transport | finiteness of B_ω makes σ unitary, and σσ* = P + (1 − Q) forces Q = P | `KazhdanCornerMatrices.norm_one_sub_mul_flip` | MISMATCH | MISMATCH | substituted | unconditional | - | NO | the substitute is the equal-rank flip ‖(1−p)q‖ ≤ ε/√(1−ε²), an approximate statement about finite-rank projections |
| KT.24 | thm:kazhdan-transport | ξ = [ξ_n]_ω is well defined by the uniform operator-norm bound | - | MISSING | MISSING | - | unconditional | - | NO | - |
| KT.25 | thm:kazhdan-transport | by unitary invariance the commutator hypothesis says each π(ι(γ)) fixes ξ, so ξ ∈ Fix | `KazhdanAsymptoticCommutant.capture_vanishing` | MISMATCH | MISMATCH | substituted | unconditional | - | NO | finite-stage spectral capture instead of exact membership |
| KT.26 | thm:kazhdan-transport | Q = P gives Vξ ∈ V·Fix = ran Q = ran P = Fix | - | MISSING | MISSING | - | unconditional | - | NO | - |
| KT.27 | thm:kazhdan-transport | the vector of U_n(s)x_nU_n(s)* is Ad U_n(s)ξ_n, so the commutator norm → 0 along ω | `MarkedCompressionVectorChain.transported_displacement_le` | MISMATCH | MISMATCH | substituted | unconditional | - | NO | the finite-stage displacement chain, with explicit constants |
| KT.28 | thm:kazhdan-transport | since the failing subsequence was arbitrary, the full sequence converges | - | MISSING | MISSING | - | unconditional | - | NO | not needed on the Lean route, which is direct |
| KT.29 | thm:kazhdan-transport | the reduction of the printed hypothesis (HS commutator vanishing) to the Lean displacement form x_n − U x_n U* | `KazhdanAsymptoticCommutant.manuscriptKazhdanTransport` | EXACT | EXACT | literal | unconditional | - | NO | done in the wrapper, by unitary invariance of ‖·‖₂ |
| RFS.01 | rem:finite-stage | the ultrafilter gives no rate; Appendix B proves the theorem a second time, quantitatively at each coordinate | `KazhdanAsymptoticCommutant.transport` | EXACT | EXACT | literal | unconditional | - | NO | this remark is the accurate description of what Lean actually proves |
| RFS.02 | rem:finite-stage | the error bookkeeping is explicit in κ, \| S \| , the bound on x_n and the multiplicative defects, once the robust spectral-gap input is granted at each stage | `WeakMFVectorGNS.hermitianAverage_eventually_no_intermediate_eigenvalues` | EXACT | EXACT | literal | unconditional | - | NO | Lean is stronger: the gap input is proved, not granted |
| TV.01 | thm:transport-variants | (1) transport at an arbitrary nonnegative weight sequence w_n, both directions | `ScaledKazhdanTransport.scaled_transport_both` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0 (Γ, E : Type); `IsScaledAsymptoticCommutant`/`IsScaledMassBounded` are the printed Tr-conditions verbatim |
| TV.02 | thm:transport-variants | (2) intertwiner transport between two asymptotic representations at the d¹_n + d²_n normalization | `IntertwinerKazhdanTransport.manuscriptIntertwinerTransport` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0 |
| TV.03 | thm:transport-variants | (2) at every weight | `IntertwinerKazhdanTransport.scaled_intertwiner_transport` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0 |
| TV.04 | thm:transport-variants | proof (1): reweight the inner product by 1/w_n; w_n = 0 forces x_n = 0 | `ScaledKazhdanTransport.scaled_transport` | EXACT | EXACT | literal | unconditional | - | NO | - |
| TV.05 | thm:transport-variants | proof (1): "the ultraproduct proof applies verbatim" | - | MISSING | MISSING | - | unconditional | - | NO | there is no ultraproduct proof to apply; Lean reruns the finite-stage argument at the weight |
| TV.06 | thm:transport-variants | proof (2): W_n = U¹_n ⊕ U²_n is an operator-norm asymptotic representation, block norms being maxima | `IntertwinerKazhdanTransport.blockSumRep` | EXACT | EXACT | literal | unconditional | - | NO | - |
| TV.07 | thm:transport-variants | proof (2): the off-diagonal embedding has operator norm ‖x_n‖ and its commutator is the embedded intertwining defect | `IntertwinerKazhdanTransport.offDiagBlock`; `IntertwinerKazhdanTransport.isScaledAsymptoticCommutantOf_offDiag_iff` | EXACT | EXACT | literal | unconditional | - | NO | - |
| TV.08 | thm:transport-variants | proof (2): conjugation by W_n(s) acts on the embedded corner by x ↦ U¹_n(s) x U²_n(s)* | `IntertwinerKazhdanTransport.blockDiag_conj_offDiag` | EXACT | EXACT | literal | unconditional | - | NO | - |
| TV.09 | p:transport-weights | w_n = d_n recovers Theorem 3.1 with the bound relaxed to mass boundedness | - | MISSING | MISSING | - | unconditional | - | NO | no declaration derives thm:kazhdan-transport from the scaled form at w_n = d_n |
| TV.10 | p:transport-weights | the collapse proof uses a rank weight; the adjoint sector is the diagonal case of (2) | - | MISSING | MISSING | - | unconditional | - | NO | the collapse proof uses its own scale k_n; the identification is not stated |
| TV.11 | p:transport-tensors | tensor powers of unitaries are exactly multiplicative and satisfy ‖A^⊗p − B^⊗p‖ ≤ p‖A − B‖ | `opTensorPow`; `OperatorNormAmplification.exists_tensorPower_pair_far` | EXACT | EXACT | literal | unconditional | - | NO | - |
| TV.12 | p:transport-tensors | hence tensor powers of an asymptotic representation are asymptotic representations, and TV.02 applies to every pair: no asymptotic invariant tensors of any fixed type at any weight | `TensorPowerTransport.manuscriptFixedTensorTransport` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0 |
| CD.01 | def:pattern | definition of a Kazhdan conjugation datum (Λ, ι, t, c) with (M1) and (M2) | `ManuscriptExactWrappers.manuscriptMarkedKazhdanPattern` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0 on Gamma; H is polymorphic |
| CD.02 | def:pattern | d := tct⁻¹ and the defect subgroup N_comp = ⟨⟨[d, ι(λ)]⟩⟩_H, normal in H | `KazhdanCompressionCore.transported`; `KazhdanCompressionCore.defectNormal` | EXACT | EXACT | literal | unconditional | - | NO | `rfl` against the printed normal closure |
| CD.03 | p:conj-datum-remark | both conditions are relations among generators, so a datum can be read off a presentation | `LiteralNonMFEndpoint.inclusionData` | EXACT | EXACT | literal | unconditional | - | NO | demonstrated for the literal presentation |
| CD.04 | p:conj-datum-remark | the relations do not constrain the commutators [d, ι(λ)] | `LiteralNonMFLinearWitness.literal_mark_ne_one` | EXACT | EXACT | literal | unconditional | - | NO | witnessed, rather than asserted, by the Clifford model |
| CD.05 | def:invisible | definition of Hilbert–Schmidt invisibility | `ManuscriptExactWrappers.ManuscriptHSInvisible` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0 |
| CD.06 | def:invisible | the definition read as a characterization: g is invisible exactly when every operator-norm asymptotic representation and every cofinite-refining ultrafilter send g to 1 in the tracial ultraproduct | `ManuscriptExactWrappers.manuscriptHSInvisibleCharacterization` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0, as CD.05; the first conjunct is the printed definition and holds by Iff.rfl, and the theorem proves two further conjuncts the definition does not print (the subgroup form, and closure under 1, product and inverse) |
| FN.00 | thm:criterion | Theorem 4.4: every finite normal F ⊆ N_comp dies in every corona representation | `ManuscriptExactWrappers.manuscriptFiniteNormalObstructionCriterion` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0; the printed proof route is followed |
| FN.01 | thm:criterion | K₂ = {g : ‖U_{g,n} − 1‖₂ → 0} is a normal subgroup of H | `nullUnitarySubgroup`; `AsymptoticUnitaryRepresentation.toUltraproductHom` | EXACT | EXACT | literal | unconditional | - | NO | realized as the kernel of the tracial-ultraproduct homomorphism |
| FN.02 | thm:criterion | c centralizes ι(Λ), so its lifts lie in the HS asymptotic commutant of ι(Λ) | `KazhdanCompressorCorner.compressionDefect_hsDistSq_vanishing` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FN.03 | thm:criterion | apply Theorem 3.1 with x_n = U_{c,n} to put the lifts of d = tct⁻¹ in the commutant | `KazhdanCompressionCore.compressionDefects_hsTrivial` | EXACT | MISMATCH | literal | unconditional | - | NO | the transport it invokes is the Appendix B one |
| FN.04 | thm:criterion | therefore [d, ι(λ)] ∈ K₂ for every λ, and normality gives N_comp ⊆ K₂ | `KazhdanCompressionCore.compressionDefects_eq_one_in_hyperlinearHom`; `KazhdanCompressionCore.defectNormal_le_ker` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FN.05 | thm:criterion | convergence of the full sequence gives triviality along every ultrafilter refining the cofinite filter | `KazhdanCompressionCore.compressionDefects_eq_one_in_hyperlinearHom` | EXACT | EXACT | literal | unconditional | - | NO | the `hcof` hypothesis is exactly the printed one |
| FN.06 | thm:criterion | suppose Θ is nontrivial on F; choose coordinate unitary lifts and form p_n = \| F \| ⁻¹ Σ_{f∈F} V_{f,n} | `FiniteNormalAverageCorner.exists_corner_with_finite_sum_vanishing` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FN.07 | thm:criterion | (p_n) is asymptotically self-adjoint and idempotent, and normality makes it asymptotically central for Θ(H) | `FiniteNormalAverageCorner.exists_corner_with_finite_sum_vanishing` | EXACT | EXACT | literal | unconditional | - | NO | internal to the corner construction |
| FN.08 | thm:criterion | the Hermitian part is asymptotically idempotent, so its spectrum clusters at {0,1}; round at 1/2 by CFC to genuine projections at distance o(1) | `FiniteNormalAverageCorner.exists_corner_with_finite_sum_vanishing` | EXACT | EXACT | literal | unconditional | BDL | NO | internal to the corner construction |
| FN.09 | thm:criterion | the rounded projections inherit asymptotic centrality; let q_n be their complements | `FiniteNormalAverageCorner.exists_corner_with_finite_sum_vanishing` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FN.10 | thm:criterion | nontriviality of Θ on F forces q_n ≠ 0 along infinitely many coordinates; retain and relabel them | `FiniteNormalAverageCorner.exists_corner_with_finite_sum_vanishing`; `OpAlmostRepresentation.reindex` | EXACT | EXACT | literal | unconditional | - | NO | the relabelling is `reindex` with a monotone stage function |
| FN.11 | thm:criterion | compress every lift to q_nM_{d_n}q_n ≅ M_{r_n} and polar-correct; almost-multiplicativity survives | `FiniteNormalAverageCorner.exists_corner_with_finite_sum_vanishing` | EXACT | EXACT | literal | unconditional | BDL | NO | - |
| FN.12 | thm:criterion | (∗) the finite average vanishes on the corner in operator norm | `FiniteNormalAverageCorner.exists_corner_with_finite_sum_vanishing` | EXACT | EXACT | literal | unconditional | - | NO | this is the returned `OpNormVanishing` conclusion |
| FN.13 | thm:criterion | tracial vanishing applies to the corner representation: ‖W_{f,n} − 1‖₂ → 0 for every f ∈ F | `KazhdanCompressionCore.finiteNormal_le_normMFResidual_of_hyperlinear_killed` | EXACT | EXACT | literal | unconditional | - | NO | the `hcloseU`/`hclose'` block |
| FN.14 | thm:criterion | F finite ⇒ the maximum of \| F \| null sequences is null ⇒ Σ_f W_{f,n} → \| F \| ·1 in normalized HS norm | `FiniteNormalAverageCorner.false_of_finite_sum_vanishing_of_hsTrivial` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FN.15 | thm:criterion | contradiction with (∗), because operator-norm convergence dominates normalized HS convergence | `FiniteNormalAverageCorner.false_of_finite_sum_vanishing_of_hsTrivial` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FN.16 | thm:criterion | transport of the conclusion from the unitary-sequence corona to U(Q) by the polar-correction isomorphism | `KazhdanCompressionCore.finiteNormal_le_normMatrixCStarCoronaKernel` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CR.01 | p:conj-reynolds-only | the Reynolds corner uses only HS invisibility of every element of N_comp | `KazhdanCompressionCore.finiteNormal_le_normMFResidual_of_hyperlinear_killed` | EXACT | EXACT | literal | unconditional | - | NO | the abstracted hypothesis is exactly that |
| CR.02 | p:conj-two-element | for F = {1,ε} the average is ½(1 + V_{ε,n}) and the corner is the negative spectral corner, where ε = −1 exactly | `KazhdanCompressorCorner.false_of_markedOpAlmostRepresentation`; `LiteralNonMFEndpoint.negativeCorner_kazhdanTransport_contradiction` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CS.00 | thm:sign-criterion | Theorem 4.5 (central-sign criterion): ε = u² ≠ 1, ε² = 1, ε central ⇒ every corona representation kills ε and H is not MF | `KazhdanCompressionCore.manuscriptCentralSignCriterion` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0 |
| CS.01 | thm:sign-criterion | (Γ, ι, t, c) is a Kazhdan conjugation datum in H | `KazhdanCompressionCore` | EXACT | EXACT | literal | unconditional | - | NO | assembled inside the proof |
| CS.02 | thm:sign-criterion | u = [d, ι(a)] is one of the displayed generators of N_comp, so ε = u² ∈ N_comp | `KazhdanCompressionCore.defect_mem_defectNormal` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CS.03 | thm:sign-criterion | F = {1, ε} is finite, and normal because ε is central | `centralInvolutionSubgroup`; `centralInvolutionSubgroup_normal`; `centralInvolutionSubgroup_finite` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CS.04 | thm:sign-criterion | Theorem 4.4 gives Θ(ε) = 1 for every corona representation | `KazhdanCompressionCore.defectSquare_centralInvolution_mem_normMatrixCStarCoronaKernel` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CS.05 | thm:sign-criterion | since ε ≠ 1 no corona representation is injective, so H is not MF | `KazhdanCompressionCore.not_isOperatorMF_of_defectSquare_eq_centralInvolution` | EXACT | EXACT | literal | unconditional | - | NO | - |
| ID.01 | p:conj-intrinsic-def | G_comp(L) = subgroup generated by the one-sided conjugators of L | `compressionSet`; `compressionGroup` | EXACT | EXACT | literal | unconditional | - | NO | - |
| ID.02 | eq:intrinsicdefect | 𝔇(H,L) = ⟨⟨[gzg⁻¹, ℓ] : g ∈ G_comp(L), z ∈ C_H(L), ℓ ∈ L⟩⟩_H | `compressionCentralizerDefectSet`; `compressionCentralizerDefect` | EXACT | EXACT | literal | unconditional | - | NO | generator set matches the display term for term |
| ID.03 | p:conj-intrinsic-def | 𝔇 depends only on (H,L), not on a choice of datum | `compressionCentralizerDefect` | EXACT | EXACT | literal | unconditional | - | NO | manifest from the definition |
| ID.04 | cor:generaltransport | Corollary 4.6: every g ∈ G_comp(L) acts in both directions on the bounded HS asymptotic commutant | `KazhdanAsymptoticCommutant.compressionGroup_transport_both` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0 |
| ID.05 | cor:generaltransport | forward transport for a one-sided conjugator s is Theorem 3.1 | `KazhdanAsymptoticCommutant.transport` | EXACT | MISMATCH | literal | unconditional | - | NO | Appendix B route |
| ID.06 | cor:generaltransport | reverse transport: P = VPV* gives V*PV = P, so the fixed subspace is preserved both ways | `KazhdanAsymptoticCommutant.transport_star` | EXACT | MISMATCH | literal | unconditional | - | NO | Lean reverses the *approximate* leakage bound (`one_sub_moved_mul_corner_vanishing`), not the exact projection identity |
| ID.07 | cor:generaltransport | in the finite-stage proof the equal-rank reversal reverses the one-sided containment, with displacement and concentration unchanged | `KazhdanCornerMatrices.norm_one_sub_mul_flip`; `KazhdanCompressorCorner.one_sub_moved_mul_corner_vanishing` | EXACT | EXACT | literal | unconditional | - | NO | - |
| ID.08 | cor:generaltransport | the elements acting in both directions form a subgroup, hence contain G_comp(L) | `KazhdanAsymptoticCommutant.asymptoticCommutantStabilizer`; `KazhdanAsymptoticCommutant.compressionGroup_le_asymptoticCommutantStabilizer` | EXACT | EXACT | literal | unconditional | - | NO | the subgroup is constructed with its three closure proofs |
| ID.09 | thm:compression-radical | Theorem 4.7: finite normal F ≤ 𝔇(H,L) dies in every norm matrix corona | `KazhdanAsymptoticCommutant.manuscriptCompressionRadical` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0 |
| ID.10 | thm:compression-radical | proof: z ∈ C_H(L) puts (U_{z,n}) in the commutant; Corollary 4.6 puts (U_{gzg⁻¹,n}) there | `KazhdanAsymptoticCommutant.finiteNormal_le_normMFResidual_of_le_compressionCentralizerDefect` | EXACT | EXACT | literal | unconditional | - | NO | - |
| ID.11 | thm:compression-radical | hence each generator [gzg⁻¹, ℓ] lies in K₂; normality gives 𝔇(H,L) ≤ K₂ | `compressionCentralizerDefect_le_ker` | EXACT | EXACT | literal | unconditional | - | NO | - |
| ID.12 | thm:compression-radical | the coordinate Reynolds corner of Theorem 4.4 applies verbatim | `KazhdanCompressionCore.finiteNormal_le_normMFResidual_of_hyperlinear_killed` | EXACT | EXACT | literal | unconditional | - | NO | literally the same declaration, as the TeX asserts |
| NK.00 | thm:normal-kazhdan | Theorem 4.9: normal property-(T) K ⊆ N_comp dies in every corona representation | `ManuscriptExactWrappers.manuscriptNormalKazhdanObstruction` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0 |
| NK.01 | p:nk-finite-recovers | taking K = F finite recovers Theorem 4.4, since finite groups have property (T) with the whole group and tolerance 1 | `hasKazhdanPropertyT_of_finite` | EXACT | EXACT | literal | unconditional | - | NO | the orbit-averaging proof is the printed one |
| NK.02 | thm:normal-kazhdan | N_comp ⊆ K₂ uses no finiteness, so every element of K is HS invisible | `KazhdanCompressionCore.compressionDefects_eq_one_in_hyperlinearHom` | EXACT | EXACT | literal | unconditional | - | NO | - |
| NK.03 | thm:normal-kazhdan | the image H̄ = Θ(H) is countable, hence MF, and Prop 2.4 along an exhaustion gives an asymptotic representation separating each fixed nontrivial element | `OperatorMFLocalNormalization.isNormApproximable_one` | EXACT | EXACT | literal | unconditional | - | NO | - |
| NK.04 | thm:normal-kazhdan | the datum and subgroup pass to Θ-images with normality and (T) preserved; K̄ nontrivial and inside the image defect | `HasKazhdanPropertyT.of_surjective` | EXACT | EXACT | literal | unconditional | - | NO | - |
| NK.05 | thm:normal-kazhdan | moving spectral subspace: cut sp(h_n) at θ = 1 − ε₀²/(4 \| S \| ); q_n = spectral projection for [−1,θ] | `KazhdanCompressorCorner.cornerProjection` | EXACT | EXACT | literal | unconditional | - | NO | same threshold constant as printed |
| NK.06 | thm:normal-kazhdan | on the top spectral subspace every model of every element of K̄ is operator-norm close to 1, by the Kazhdan displacement estimate | `KazhdanCompressorCorner.displacement_vanishing` | EXACT | EXACT | literal | unconditional | - | NO | - |
| NK.07 | thm:normal-kazhdan | if q_n = 0 eventually then every element of K̄ has ‖V_{k,n} − 1‖ → 0, contradicting operator-norm separation | `KazhdanCompressionCore.normalKazhdan_le_normMFResidual` | EXACT | EXACT | literal | unconditional | - | NO | - |
| NK.08 | thm:normal-kazhdan | tracial deficit: q_nh_nq_n ≤ θq_n, so some generator s₀ has compressed real renormalized trace ≤ θ | `KazhdanCompressionCore.normalKazhdan_le_normMFResidual` | EXACT | EXACT | literal | unconditional | - | NO | - |
| NK.09 | thm:normal-kazhdan | hence normalized HS distance ≥ √(2(1−θ)) − o(1) after polar correction; a subsequence fixes s₀ | `KazhdanCompressionCore.normalKazhdan_le_normMFResidual` | EXACT | EXACT | literal | unconditional | - | NO | - |
| NK.10 | thm:normal-kazhdan | normality makes the cut asymptotically central: conjugating h_n gives the average over gSg⁻¹ with the same Kazhdan constant | `KazhdanCompressionCore.normalKazhdan_le_normMFResidual` | EXACT | EXACT | literal | unconditional | - | NO | - |
| NK.11 | thm:normal-kazhdan | the two Appendix B estimates apply symmetrically, giving two-sided almost containment and ‖[q_n, V_{g,n}]‖ → 0 | `KazhdanCompressorCorner.displacement_vanishing`; `KazhdanAsymptoticCommutant.capture_vanishing` | EXACT | EXACT | literal | unconditional | - | NO | - |
| NK.12 | thm:normal-kazhdan | compress every model to the moving corner and polar-correct, keeping s₀ at a definite HS distance | `KazhdanCompressionCore.normalKazhdan_le_normMFResidual` | EXACT | EXACT | literal | unconditional | - | NO | - |
| NK.13 | thm:normal-kazhdan | contradiction: tracial vanishing applies to the corner, making s₀ HS invisible | `KazhdanCompressionCore.normalKazhdan_le_normMatrixCStarCoronaKernel_of_hyperlinear_killed` | EXACT | EXACT | literal | unconditional | - | NO | - |
| NK.14 | thm:abstract-nk | Theorem 4.10: the same conclusion from HS invisibility of a subgroup D, taken as hypothesis | `ManuscriptExactWrappers.manuscriptAbstractNormalKazhdanObstruction` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0; the invisibility hypothesis is a property of the ambient group, not an imported theorem |
| NK.15 | thm:abstract-nk | every operator-norm almost representation of H̄ composes with Θ, so Θ(D) inherits invisibility | `KazhdanCompressionCore.normalKazhdan_le_normMatrixCStarCoronaKernel_of_hyperlinear_killed` | EXACT | EXACT | literal | unconditional | - | NO | - |
| NK.16 | cor:intrinsic-nk | Corollary 4.11: normal (T) subgroup of 𝔇(H,L) dies in every corona representation | `ManuscriptExactWrappers.manuscriptIntrinsicNormalKazhdanRadical` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0 |
| NK.17 | p:nk-join | the subgroup generated by all normal (T) subgroups of 𝔇(H,L) also lies in the kernel of every corona representation | `ManuscriptExactWrappers.manuscriptIntrinsicNormalKazhdanPart` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0 |
| KC.01 | thm:kazhdan-clifford | the presentation with one redundant generator ε, central involution, ε = u², u = [tct⁻¹, a] | `KazhdanCliffordConstruction.mark` | EXACT | EXACT | literal | unconditional | - | NO | - |
| KC.02 | p:constr-tietze | rigidity forces u ∼₂ 1 while the Clifford model makes u² = −1 | `KazhdanCliffordConstruction.kazhdanCliffordConstruction` | EXACT | MISMATCH | literal | unconditional | - | NO | rigidity is supplied by the Appendix B transport |
| KC.03 | p:constr-tietze | Tietze elimination: since d is an involution, u² = [d, ada⁻¹], and centrality of u² forces (u²)² = 1 | `commutator_conjugate_eq_commutator_sq_of_sq_eq_one`; `KazhdanCliffordConstruction.mark_sq` | EXACT | EXACT | literal | unconditional | - | NO | - |
| KC.04 | thm:kazhdan-clifford | Theorem 5.1: E(Γ,α,a) is finitely presented, Γ embeds, w is a nontrivial central involution, every corona representation kills w, and E is not MF | `KazhdanCliffordConstruction.kazhdanCliffordConstruction` | EXACT | EXACT | literal | unconditional | - | NO | Γ₀ is a `Type` but the printed hypothesis "finitely presented" already forces countability; no wider quantifier is printed |
| KC.05 | thm:kazhdan-clifford | finite presentability from a relative finite presentation: free product of Γ with F(t,c) modulo the finitely many displayed relations | `KazhdanCliffordConstruction.Extension`; `KazhdanCliffordConstruction.kazhdanCliffordConstruction` | EXACT | EXACT | literal | unconditional | - | NO | - |
| KC.06 | eq:involution-reversal | with b = ada⁻¹, both d and b involutions, w = [d,b] = (db)², direct cancellation gives dwd⁻¹ = w⁻¹ | `commutator_conjugate_eq_commutator_sq_of_sq_eq_one` | EXACT | EXACT | literal | unconditional | - | NO | - |
| KC.07 | thm:kazhdan-clifford | centrality also gives dwd⁻¹ = w, whence w = w⁻¹ and w² = 1: the relation w² = 1 is redundant | `KazhdanCliffordConstruction.mark_sq` | EXACT | EXACT | literal | unconditional | - | NO | - |
| KC.08 | thm:kazhdan-clifford | realize G = ⟨Γ,t \| tγt⁻¹ = α(γ)⟩ as a mapping telescope; Γ_∞ = direct limit of Γ →^α Γ →^α ⋯ | `MappingTelescope.Telescope` | EXACT | EXACT | literal | unconditional | - | NO | - |
| KC.09 | thm:kazhdan-clifford | injectivity of α passes to the limit, so the level-zero map embeds Γ in Γ_∞ | `MappingTelescope.level_injective` | EXACT | EXACT | literal | unconditional | - | NO | - |
| KC.10 | thm:kazhdan-clifford | applying α levelwise induces an injective endomorphism σ of Γ_∞, surjective because a level-k element is σ of the same element at level k+1, hence an automorphism | `MarkedCompression.shiftHom` | EXACT | EXACT | literal | unconditional | - | NO | - |
| KC.11 | thm:kazhdan-clifford | put G = Γ_∞ ⋊_σ ℤ with stable letter t; then tγt⁻¹ = α(γ) for γ ∈ Γ | `MarkedCompression.Vertical`; `MarkedCompression.vertical_compress` | EXACT | EXACT | literal | unconditional | - | NO | - |
| KC.12 | thm:kazhdan-clifford | X = G/Γ; let G permute the Clifford generators (e_x) and send c to e_Γ | `MarkedCompression.Cosets`; `CliffordAlgebraLamp.lampGroup` | EXACT | EXACT | literal | unconditional | - | NO | - |
| KC.13 | thm:kazhdan-clifford | then d ↦ e_{tΓ} and ada⁻¹ ↦ e_{atΓ} | `MarkedCompression.conj_inl_lamp` | EXACT | EXACT | literal | unconditional | - | NO | - |
| KC.14 | thm:kazhdan-clifford | the two cosets are distinct: equality would give t⁻¹at ∈ Γ, i.e. a ∈ α(Γ) | `MarkedCompression.moved_cosets_ne` | EXACT | EXACT | literal | unconditional | - | NO | - |
| KC.15 | thm:kazhdan-clifford | hence the two Clifford generators anticommute and w ↦ (e_{tΓ}e_{atΓ})² = −1 | `CliffordLamp.commutator_lamp_lamp`; `KazhdanCliffordConstruction.mark_ne_one` | EXACT | EXACT | literal | unconditional | - | NO | - |
| KC.16 | thm:kazhdan-clifford | the Clifford sign is central, so the map respects every defining relation | `CliffordAlgebraLamp.zGen_mem_center` | EXACT | EXACT | literal | unconditional | - | NO | - |
| KC.17 | thm:kazhdan-clifford | it follows simultaneously that w ≠ 1 and that the canonical map of Γ is injective | `KazhdanCliffordConstruction.iota_injective` | EXACT | EXACT | literal | unconditional | - | NO | - |
| KC.18 | thm:kazhdan-clifford | by the central-sign criterion every corona representation maps w to 1; since w ≠ 1 none is faithful | `KazhdanCompressionCore.manuscriptCentralSignCriterion` | EXACT | EXACT | literal | unconditional | - | NO | invoked verbatim in the Lean proof |
| KC.19 | p:constr-role-of-a | a ∈ Γ makes fixed-space transport force d to commute asymptotically with the image of a | `KazhdanCompressionCore.compressionDefects_hsTrivial` | EXACT | MISMATCH | literal | unconditional | - | NO | Appendix B route |
| KC.20 | p:constr-role-of-a | a ∉ α(Γ) moves the Clifford generator to a different HNN coset, where anticommutation produces −1 | `MarkedCompression.moved_cosets_ne` | EXACT | EXACT | literal | unconditional | - | NO | - |
| KC.21 | rem:ff-realization | Fournier-Facio's f.p. torsion-free (T) group P contains every f.p. torsion-free group, in particular P₁ × P₂ | - | MISSING | MISSING | - | literature-input | FFF | NO | personal communication plus FFF; nothing formal |
| KC.22 | rem:ff-realization | hence α : P ≅ P₁ ≤ P and any a ∈ P₂ \ {1} satisfy the hypotheses of Theorem 5.1 | - | MISSING | MISSING | - | literature-input | FFF | NO | conditional on KC.21 |
| KC.23 | rem:ff-realization | E(P,α,a) contains involutions whatever the base | - | MISSING | MISSING | - | literature-input | FFF | NO | - |
| TA.00 | thm:A | Theorem A: w ≠ 1 in E, and Θ(w) = 1 for every homomorphism E → U_cor((d_n)); E is not MF and neither C*_max(E) nor C*_red(E) is MF | `LiteralNonMFEndpoint.manuscriptTheoremA` | EXACT | EXACT | literal | unconditional | - | NO | fully unconditional; the strongest row in the ledger |
| TA.01 | thm:A | the defining relations make w central; with c² = 1 centrality implies w² = 1 | `LiteralNonMFPresentation.mark_central`; `LiteralNonMFPresentation.mark_sq` | EXACT | EXACT | literal | unconditional | - | NO | - |
| TA.02 | cor:uniform | Corollary 5.4: there are δ > 0 and finite F₀ ⊂ E with a uniform local obstruction ‖φ(w) − 1‖ < 1 in every dimension | `LiteralUniformObstruction.literal_uniform_operatorNorm_obstruction` | EXACT | EXACT | literal | unconditional | - | NO | - |
| TA.03 | cor:uniform | proof: otherwise choose models violating the conclusion for δ = 1/n along an exhaustion | `uniform_invisibility` | EXACT | EXACT | literal | unconditional | - | NO | - |
| TA.04 | cor:uniform | these form an asymptotic representation whose values at w stay ≥ 1 from the identity; its corona class detects w, contradicting Theorem A(2) | `uniform_invisibility` | EXACT | EXACT | literal | unconditional | - | NO | - |
| TA.05 | cor:uniform | the compactness argument is not quantitative; an effective modulus remains open | - | MISSING | MISSING | - | open | - | NO | the TeX states it is open |
| TA.06 | cor:scaling-family | Corollary 5.6: for every m ≥ 2, E_m is finitely presented, w_m a nontrivial central involution killed by every corona homomorphism; E_m is not MF | `ScalingFamilyEndpoint.manuscriptTheoremFamily` | EXACT | EXACT | literal | unconditional | - | NO | - |
| TA.07 | cor:scaling-family | proof: replace diag(2,2,2,1) by diag(m,m,m,1), conjugating v_i to v_i^m and fixing x,y,z | `ScalingFamilyPresentation.stable_conjugates_base_into_base` | EXACT | EXACT | literal | unconditional | - | NO | - |
| TA.08 | cor:scaling-family | its inverse sends v₁ to translation by e₁/m, not integral, so the two Clifford sites remain distinct and w_m ↦ −1 | `ScalingFamilyEndpoint.cliffordSign_blackHole` | EXACT | EXACT | literal | unconditional | - | NO | - |
| TA.09 | cor:scaling-family | the Kazhdan base, the one-sided conjugation argument and the central-sign criterion are independent of m | `ScalingFamilyEndpoint.scalingFamily_not_isCDEOperatorMF` | EXACT | EXACT | literal | unconditional | - | NO | - |
| TA.10 | p:A-defect-square | d = tct⁻¹, u = [d, v₁], w = u², so w lies in the compression defect and the criterion applies at the marked word | `LiteralNonMFEndpoint.mark_eq_compressionDefect_sq`; `LiteralNonMFEndpoint.literalInvolutionSubgroup_le_defectNormal` | EXACT | EXACT | literal | unconditional | - | NO | - |
| TA.11 | p:A-defect-square | for a detecting corona representation, the negative corner gives a model with w = −1 exactly, while transport gives u ∼₂ 1 and hence w ∼₂ 1 | `LiteralNonMFEndpoint.negativeCorner_kazhdanTransport_contradiction` | EXACT | MISMATCH | literal | unconditional | - | NO | the transport half runs the Appendix B route |
| TA.12 | prop:witness | nontriviality of w is witnessed by a representation into ClLamp ⋊ (telescope of the exact rational affine model) | `LiteralNonMFLinearWitness.realization` | EXACT | EXACT | literal | unconditional | - | NO | - |
| TA.13 | p:A-consequences | for E the datum is (ℬ, ι, t, c) and the relevant finite normal subgroup of the defect is {1, w} | `LiteralNonMFEndpoint.inclusionData`; `LiteralNonMFEndpoint.literalInvolutionSubgroup` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FD.00 | thm:B | Theorem B, first clause: every finite-dimensional π over every field kills [tct⁻¹, a(tct⁻¹)a⁻¹] | `ManuscriptExactWrappers.manuscriptTheoremB` | EXACT | EXACT | literal | unconditional | - | NO | fully universe-polymorphic in k, V, H |
| FD.01 | thm:B | Theorem B, second clause: every such π sends the entire subgroup 𝔇(H,Γ) to the identity | `ManuscriptExactWrappers.manuscriptTheoremB` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0: the second conjunct fixes `H : Type` while the first is polymorphic |
| FD.02 | thm:B | let C be the commutant of π(Γ), a linear subspace of End_k(V) | `repCommutant` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FD.03 | thm:B | let u = π(t) and Φ(x) = uxu⁻¹, a linear automorphism of End_k(V) | `sandwich` | EXACT | EXACT | literal | unconditional | - | NO | `sandwich (π t) (π t⁻¹)`, with injectivity proved from the two-sided inverse |
| FD.04 | thm:B | claim C ⊆ Φ(C): for x ∈ C put y = u⁻¹xu, then π(γ)y = u⁻¹π(tγt⁻¹)xu = u⁻¹xπ(tγt⁻¹)u = yπ(γ) | `map_marked_commutator_eq_one` | EXACT | EXACT | literal | unconditional | - | NO | the `transport` and `hle` blocks of the Lean proof |
| FD.05 | eq:pinning | Φ is a linear isomorphism, so dim Φ(C) = dim C < ∞, and C ⊆ Φ(C) forces C = Φ(C) = uCu⁻¹ | `map_marked_commutator_eq_one` | EXACT | EXACT | literal | unconditional | - | NO | `hrank` via `Submodule.equivMapOfInjective`, then `Submodule.eq_of_le_of_finrank_le` |
| FD.06 | thm:B | π(c) ∈ C because c centralizes Γ | `map_marked_commutator_eq_one` | EXACT | EXACT | literal | unconditional | - | NO | the `hcC` block |
| FD.07 | thm:B | by the pinning, π(tct⁻¹) = uπ(c)u⁻¹ ∈ C | `map_marked_commutator_eq_one` | EXACT | EXACT | literal | unconditional | - | NO | the `hdC` block |
| FD.08 | thm:B | since a ∈ Γ, π(tct⁻¹) commutes with π(a), so π(a(tct⁻¹)a⁻¹) = π(tct⁻¹) | `map_marked_commutator_eq_one` | EXACT | EXACT | literal | unconditional | - | NO | the `hda`/`hfix` block |
| FD.09 | thm:B | hence the marked commutator is the commutator of an element with itself, so it is 1 | `map_marked_commutator_eq_one` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FD.10 | p:B-subgroup-valued | the elements whose conjugation preserves C in both directions form a subgroup containing every one-sided conjugator, hence G_comp(Γ) | `compressionGroup_le_commutantStabilizer` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FD.11 | p:B-subgroup-valued | so π(gzg⁻¹) ∈ C commutes with every π(ℓ); each displayed generator of 𝔇 lies in ker π; normality gives 𝔇(H,Γ) ≤ ker π | `map_compressionCentralizerDefect_generator_eq_one`; `compressionCentralizerDefect_le_ker` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FD.12 | cor:notRFD | E admits no injective homomorphism into GL(V) for any finite-dimensional V over any field | `LiteralFiniteDimensionalObstruction.manuscriptFiniteDimensionalConsequences` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FD.13 | cor:notRFD | every finite-dimensional linear representation maps w to the identity | `LiteralFiniteDimensionalObstruction.manuscriptFiniteDimensionalConsequences` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FD.14 | cor:notRFD | every homomorphism to a finite group maps w to the identity | `LiteralFiniteDimensionalObstruction.manuscriptFiniteDimensionalConsequences` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FD.15 | cor:notRFD | proof of the finite-target clause: compose with the faithful left regular representation over ℚ and evaluate at the identity basis vector | `LiteralFiniteDimensionalObstruction.map_literal_mark_eq_one_of_finite` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FD.16 | p:B-applied | consequently finite-dimensional representations do not separate points of E, no finite quotient witnesses w ≠ 1, and the infinite Clifford witness cannot be replaced by a finite-dimensional one | `LiteralFiniteDimensionalObstruction.manuscriptFiniteDimensionalConsequences`; `LiteralNonMFLinearWitness.literal_mark_ne_one` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FD.17 | p:B-deligne | w makes E a group of Deligne type in the sense of BDL, realizing their proposal at the operator-norm endpoint | - | MISSING | MISSING | - | literature-input | BDL | NO | terminology import; no formal content |
| FD.18 | rem:invariantsize | the abstract invariant-size principle: a conjugation-invariant ℕ-valued size separating nested subgroups admits no strict one-sided compression | `ManuscriptExactWrappers.manuscriptInvariantSizePrinciple` | EXACT | EXACT | literal | unconditional | - | NO | universe-polymorphic |
| FD.19 | rem:invariantsize | cardinality on subgroups of a finite group qualifies, so no finite quotient detects strict one-sided compression | - | MISSING | MISSING | - | unconditional | - | NO | the instantiation at cardinality is not stated |
| FD.20 | rem:invariantsize | the finite-dimensional case is not the same principle: dim End_H(V) is order-reversing and does not separate, e.g. A₄ < S₄ have the same commutant k·1 | - | MISSING | MISSING | - | unconditional | - | NO | the A₄ < S₄ counterexample is not formalized |
| FD.21 | rem:invariantsize | what the proof of Theorem B uses is the principle one level down, on the commutant | `map_marked_commutator_eq_one` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FD.22 | rem:chaincondition | an order isomorphism of a poset with no infinite strictly ascending chain fixes every weakly upward-moved point, and dually | `manuscriptChainConditionRigidity` | EXACT | EXACT | literal | unconditional | - | NO | both directions, universe-polymorphic |
| FD.23 | rem:chaincondition | consequently for every finite-dimensional σ over every field the fixed subspaces of Γ and of tΓt⁻¹ coincide | `manuscriptChainConditionRigidity` | EXACT | EXACT | literal | unconditional | - | NO | third conjunct |
| FD.24 | rem:chaincondition | applied to tensor constructions: compression creates no invariant tensors of any finite type | `TensorInvariantRigidity.manuscriptTensorInvariantRigidity` | EXACT | EXACT | literal | unconditional | - | NO | tensor, dual, Hom and product representations |
| FD.25 | rem:chaincondition | taking the invariant to be the Zariski closure gives equal algebraic envelopes for Γ and tΓt⁻¹ | `ClosedEnvelopeCompression.manuscriptEnvelopeCompressionBlind` | MISMATCH | MISMATCH | substituted | unconditional | - | NO | univ0; and the Lean statement quantifies over an abstract `Closed` predicate, as the TeX itself says |
| FD.25b | rem:chaincondition | the chain condition itself, for Zariski-closed subgroups of GL(V) over an arbitrary field, from the Hilbert basis theorem | `ZariskiClosedSubgroup.manuscriptZariskiRepresentationEnvelopeClosed` | EXACT | EXACT | literal | unconditional | - | NO | proved rather than quoted; FD.25 beside it is the envelope-blindness step and keeps its own status |
| FD.26 | rem:chaincondition | that closed subgroups of GL(V) in the Zariski topology satisfy the chain condition is classical and is quantified over, not proved | - | MISSING | MISSING | - | literature-input | - | NO | the TeX states this explicitly |
| FD.27 | p:B-why-corona | an MF model is only asymptotically multiplicative, so coordinate fixed spaces are not literal invariant subspaces; operator-norm control keeps the adjoint actions almost multiplicative; (T) supplies an almost-fixed spectral subspace; the equal-rank reversal turns one-sided compression into equality | `KazhdanCompressorCorner.cornerProjection`; `KazhdanCornerMatrices.norm_one_sub_mul_flip` | EXACT | EXACT | literal | unconditional | - | NO | this paragraph describes the Appendix B route, which is the formalized one |
| GP.01 | eq:sl3presentation | the linear presentation ℛ = ⟨x,y,z \| eight relators⟩ | `LiteralBaseRotationRetract.rotationRelators` | EXACT | EXACT | literal | unconditional | CRW, CLV | NO | eight relators, term for term |
| GP.02 | eq:gamma-presentation | the base ℬ on v₁,v₂,v₃,x,y,z with the twenty displayed relators | `LiteralNonMFPresentation.baseRelators`; `LiteralNonMFPresentation.baseRelators_card` | EXACT | EXACT | literal | unconditional | - | NO | list and cardinality 20 both checked |
| GP.03 | def:E | the eight-generator, forty-one-relator presentation of E, with w the displayed word | `LiteralNonMFPresentation.manuscriptLiteralPresentation` | EXACT | EXACT | literal | unconditional | - | NO | generator indexing, all four relator families, `relators.card = 41`, and the marked word all `rfl` |
| GP.04 | def:E | the relator count decomposes as 20 base + 6 stable-letter + c² + 6 c-commutation + 8 centrality | `LiteralNonMFPresentation.relators_card` | EXACT | EXACT | literal | unconditional | - | NO | - |
| GP.05 | def:E | the defining relations make w central, and centrality with c² = 1 gives w² = 1 | `LiteralNonMFPresentation.mark_central`; `LiteralNonMFPresentation.mark_sq` | EXACT | EXACT | literal | unconditional | - | NO | - |
| GP.06 | def:E | the base relations give tι(ℬ)t⁻¹ ⊆ ι(ℬ) and [c, ι(ℬ)] = 1 | `LiteralNonMFPresentation.stable_conjugates_base_into_base`; `LiteralNonMFPresentation.lamp_commutes_base` | EXACT | EXACT | literal | unconditional | - | NO | - |
| GP.07 | p:group-sixgen | E is generated by the six elements v₁, x, y, z, t, c | `LiteralSixGenerator.literal_rank_le_six` | EXACT | EXACT | literal | unconditional | - | NO | stated as `Group.rank ≤ 6` |
| GP.07b | p:group-sixgen | the six-generator form is finitely presented and non-MF | `LiteralSixGenerator.literal_sixGenerated_finitelyPresented_nonMF` | EXACT | EXACT | literal | unconditional | - | NO | the declaration the badge on this paragraph actually names |
| GP.08 | p:group-tietze32 | there is a Tietze-equivalent six-generator presentation with thirty-two relators | `LiteralTietzePresentation.manuscriptTietzeSixGeneratorPresentation` | EXACT | EXACT | literal | unconditional | - | NO | explicit list of length 32 with an isomorphism matching generators |
| GP.09 | p:group-tietze32 | proof: eliminate v₃ = xv₁x⁻¹ and v₂ = x²v₁x⁻², the x-action relation follows from x³ = 1, and the v₂,v₃ relations follow from those for v₁ with [t,x] = 1 and x³ = 1; deleting nine leaves thirty-two | `LiteralTietzePresentation.exists_sixGenerator_thirtyTwo_presentation` | EXACT | EXACT | literal | unconditional | - | NO | - |
| GP.10 | p:group-figure | the relations force d = tct⁻¹ to commute with tι(ℬ)t⁻¹ and do not constrain [d, ι(v₁)dι(v₁)⁻¹] | `LiteralNonMFPresentation.lamp_commutes_base`; `LiteralNonMFLinearWitness.literal_mark_ne_one` | EXACT | EXACT | literal | unconditional | - | NO | the negative half is witnessed by the Clifford model |
| GP.11 | fig:compression-pattern | the figure's content: the one-sided conjugation configuration and w = [d,ι(v₁)]² since d² = 1 | `LiteralNonMFEndpoint.mark_eq_compressionDefect_sq` | EXACT | EXACT | literal | unconditional | - | NO | - |
| BT.00 | prop:literal-base-T | Proposition 7.2: the twenty-relator base ℬ has property (T) in both the real-orthogonal and complex-unitary formulations | `LiteralBaseP13PropertyTBridge.manuscriptBaseHasKazhdanPropertyT` | EXACT | EXACT | literal | unconditional | - | NO | both formulations, the second universe-polymorphic in the representation universe |
| BT.01 | prop:literal-base-T | Step 1: P₁₃ on six generators with the thirteen displayed relators | `LiteralP13HodgeCertificate.manuscriptP13Presentation` | EXACT | EXACT | literal | unconditional | - | NO | all thirteen relator letter lists pinned |
| BT.02 | prop:literal-base-T | Step 1: an exact SOS certificate with integer matrix data, verified by denominator-free rational arithmetic, proves the degree-one Hodge estimate with gap 1/500 | `LiteralP13HodgeCertificate.cleanP13Certificate`; `LiteralP13HodgeCertificate.p13_hodge_gap` | EXACT | EXACT | literal | unconditional | Ozawa, NetzerThom | NO | kernel-checked; the exact residual data is confined to the private proof and the public gap is exactly 1/500 |
| BT.03 | prop:literal-base-T | Step 1: testing on coboundaries gives ‖Δξ‖² ≥ (1/500)⟨Δξ,ξ⟩ in every orthogonal representation | `LiteralP13HodgeCertificate.p13_generatorLaplacian_quadratic_gap` | EXACT | EXACT | literal | unconditional | - | NO | same constant as printed |
| BT.04 | prop:literal-base-T | Step 1: the gap places sp(Δ) in {0} ∪ [1/500,∞) | - | MISSING | MISSING | - | unconditional | - | NO | CORRECTED against docs/P13_STEP_AUDIT.md T1.04, which overturns my earlier EXACT: no spectrum is formed anywhere in the chain.  Lean substitutes `PositiveOperatorGap.norm_le_of_quadratic_gap`, a damped Richardson/Neumann iteration, and obtains a strictly weaker constant |
| BT.04b | prop:literal-base-T | Step 1: the kernel of Δ is exactly the space of invariant vectors | `ExactHodgeCertificate.invariant_of_generatorLaplacian_eq_zero` | MISMATCH | MISMATCH | literal | unconditional | - | NO | CORRECTED against docs/P13_STEP_AUDIT.md T1.05: only the inclusion Δx = 0 ⇒ x invariant is proved; the printed equality is not |
| BT.04c | prop:literal-base-T | Step 1: hence an almost-fixed unit vector has small Laplacian energy and is close to an invariant vector | `ExactHodgeCertificate.Certificate.isKazhdanPair` | MISMATCH | MISMATCH | literal | unconditional | - | NO | CORRECTED against docs/P13_STEP_AUDIT.md T1.06: Lean takes the dual route — no invariant vectors, so some generator moves x — and never produces a nearby invariant vector |
| BT.04d | prop:literal-base-T | Step 1: this yields a Kazhdan pair, so P₁₃ has property (T) | `LiteralP13HodgeCertificate.p13_hasKazhdanPropertyT`; `ExactHodgeCertificate.certifiedKazhdanTolerance` | EXACT | EXACT | literal | unconditional | - | NO | explicit pair, unconditional |
| BT.05 | prop:literal-base-T | Step 2: the six explicit words in x,y,z; all thirteen P₁₃ relators map to the identity inside ℛ using only its eight relators | `LiteralBaseP13RotationQuotient.p13ToRotation` | EXACT | EXACT | literal | unconditional | - | NO | the six words match the printed ones letter for letter |
| BT.06 | prop:literal-base-T | Step 2: explicit words in the six images evaluate to z and to xy, and z, xy generate ℛ; hence the homomorphism is surjective | `LiteralBaseP13RotationQuotient.p13ToRotation_surjective` | EXACT | EXACT | literal | unconditional | - | NO | proof-carrying replay modules `RangeZ`, `RangeXY` |
| BT.07 | prop:literal-base-T | Step 2: property (T) passes to quotients, so ℛ has (T) | `HasKazhdanPropertyT.of_surjective` | EXACT | EXACT | literal | unconditional | - | NO | - |
| BT.08 | prop:literal-base-T | Step 3: x,y,z in ℬ satisfy the relators of ℛ, so ℛ maps to the linear subgroup they generate | `LiteralBaseRotationRetract.rotationEquivRotations` | MISMATCH | MISMATCH | substituted | unconditional | - | NO | CORRECTED against docs/P13_STEP_AUDIT.md T3.01: Lean uses an isomorphism `Rotation ≃* rotations` where the manuscript uses only a surjection |
| BT.08b | prop:literal-base-T | Step 3: the Kazhdan pair (S,κ) supplied by Step 2 | `LiteralBasePropertyTBridge.base_hasKazhdanPropertyT_of_rotation` | MISMATCH | MISMATCH | literal | unconditional | - | NO | CORRECTED against docs/P13_STEP_AUDIT.md T3.03: Lean carries an unstated κ ≤ 1 normalization the manuscript does not impose |
| BT.09 | prop:literal-base-T | Step 3: control set = S together with v₂ and v₃; v₁ = xv₂x⁻¹ needs no separate control | `LiteralBasePropertyTBridge.base_hasKazhdanPropertyT_of_rotation` | EXACT | EXACT | literal | unconditional | - | NO | `baseControlSet S = S ∪ {v₂, v₃}`, exactly as printed |
| BT.09b | prop:literal-base-T | Step 3: the third basis translation needs no separate control because v₁ = xv₂x⁻¹ and conjugation by the fixed unitary of x preserves displacements | - | MISSING | MISSING | - | unconditional | - | NO | CORRECTED against docs/P13_STEP_AUDIT.md T3.04: Lean omits v₁ for a different reason; the printed reason has no counterpart |
| BT.10 | prop:literal-base-T | Step 3(1): projecting ξ to the linear-fixed subspace gives p with ‖p − ξ‖ < 1/64, by the moving-projection estimate | `LiteralBasePropertyTBridge.exists_global_fixed_near` | EXACT | EXACT | literal | unconditional | - | NO | printed constants κ/64 and 1/64 appear verbatim |
| BT.11 | prop:literal-base-T | Step 3(2): three explicit words in x,y,z act on the lattice as elementary transvections, giving a two-conjugate normal form for every lattice element | `LiteralTranslationOrbit.conjugate_mem_translations`; `LiteralTranslationOrbit.e13` | EXACT | EXACT | literal | unconditional | - | NO | proved inside the presentation, as the TeX asserts |
| BT.12 | prop:literal-base-T | Step 3(2): a conjugate rvr⁻¹ displaces p exactly as v does; each control translation moves p by < 3/64; hence every translation moves p by ≤ 1/8 | `LiteralBasePropertyTBridge.exists_global_fixed_near` | EXACT | EXACT | literal | unconditional | - | NO | printed constants 3/64 and 1/8 appear verbatim |
| BT.13 | prop:literal-base-T | Step 3(3): bounded orbit ⇒ the Hilbert-space circumcenter argument gives a translation-fixed q with ‖q − p‖ ≤ 1/8 | `HilbertConvexFixedPoint.exists_fixed_of_orbit_displacement_le`; `HilbertConvexFixedPoint.closedConvexHull_orbit_stable` | MISMATCH | MISMATCH | substituted | unconditional | - | NO | CORRECTED against docs/P13_STEP_AUDIT.md T3.11: Lean uses the minimal-norm point of the closed convex hull of the orbit, not a circumcenter |
| BT.14 | prop:literal-base-T | Step 3(3): the linear subgroup normalizes the translations and fixes p, so η is fixed by it; together they generate ℬ, and ‖η − ξ‖ ≤ 1/8 + 1/64 < 1 keeps η ≠ 0 | `LiteralBasePropertyTBridge.base_hasKazhdanPropertyT_of_rotation` | EXACT | EXACT | literal | unconditional | - | NO | the final `hy : y ≠ 0` block |
| BT.15 | prop:literal-base-T | realification and complexification identify the real-orthogonal formulation with the complex-unitary one | `hasKazhdanPropertyT_iff_textbook` | EXACT | EXACT | literal | unconditional | - | NO | - |
| BT.16 | p:base-p13-aux | the auxiliary presentation of Step 1 presents the group it is modelled on | `P13DescentMaster.p13CompletenessEquiv` | EXACT | EXACT | literal | unconditional | - | NO | - |
| BT.17 | thm:p13-complete | Theorem 7.3: the canonical P₁₃ → SL₃(ℤ) is an isomorphism | `P13DescentMaster.p13CompletenessEquiv` | EXACT | EXACT | literal | unconditional | - | NO | `MulEquiv.ofBijective` of the two clauses below |
| BT.18 | thm:p13-complete | route: surjectivity is Euclidean elimination | `SL3ElementaryGeneration.toSL3_surjective` | EXACT | EXACT | literal | unconditional | - | NO | route audited at module granularity |
| BT.19 | thm:p13-complete | route: every unit-root word normalizes, by a descent on the lexicographic measure of its trajectory over the third basis column, into a norm-monotone word times an element of ⟨w₁₃,w₂₃⟩ | `P13WordDescent.Viol`; `P13DescentMaster.viol_succ_lt` | EXACT | UNDER-SPECIFIED | literal | unconditional | - | NO | CORRECTED against docs/P13_STEP_AUDIT.md §2: the printed "Proof route" is seven sentences, so lexicographic trajectory measure is present in Lean as the object of that name and used where the manuscript uses it, but the interior of the step is not determined by the print |
| BT.20 | thm:p13-complete | route: for a kernel word the monotone trajectory is squeezed at norm one, so every letter fixes the base column | `P13DescentMaster.side_le_of_top` | EXACT | UNDER-SPECIFIED | literal | unconditional | - | NO | CORRECTED against docs/P13_STEP_AUDIT.md §2: the printed "Proof route" is seven sentences, so the squeeze at norm one is present in Lean as the object of that name and used where the manuscript uses it, but the interior of the step is not determined by the print |
| BT.21 | thm:p13-complete | route: conjugating through the signed-swap tail lands the word in the parabolic ⟨e₁₂,e₂₁,e₃₁,e₃₂⟩, whose elements the matrix model separates by their semidirect normal form | `P13ParabolicKernel.exists_parabolic_form`; `P13ParabolicKernel.eq_one_of_mem_parabolic_of_map_eq_one` | EXACT | UNDER-SPECIFIED | literal | unconditional | - | NO | CORRECTED against docs/P13_STEP_AUDIT.md §2: the printed "Proof route" is seven sentences, so the parabolic subgroup is present in Lean as the object of that name and used where the manuscript uses it, but the interior of the step is not determined by the print |
| BT.22 | thm:p13-complete | route: the signed-swap subgroup is governed by a six-coset Schreier system whose Schreier elements are powers of the block Weyl element | `P13MonomialMachine.exists_rep_wpow`; `P13MonomialMachine.mem_Hpar_of_stab` | EXACT | UNDER-SPECIFIED | literal | unconditional | - | NO | CORRECTED against docs/P13_STEP_AUDIT.md §2: the printed "Proof route" is seven sentences, so the six-coset Schreier system is present in Lean as the object of that name and used where the manuscript uses it, but the interior of the step is not determined by the print |
| BT.23 | thm:p13-complete | route: the classical obstruction {−1,−1} = w⁴ is killed by the displayed relator, and with it the kernel | `P13WeylFourthPowers.w13_pow_four`; `P13WeylFourthPowers.w23_pow_four` | EXACT | UNDER-SPECIFIED | literal | unconditional | - | NO | CORRECTED against docs/P13_STEP_AUDIT.md §2: the printed "Proof route" is seven sentences, so the {−1,−1} = w⁴ obstruction is present in Lean as the object of that name and used where the manuscript uses it, but the interior of the step is not determined by the print |
| BT.23b | thm:p13-complete | the printed order of the route: normalize, then squeeze, then conjugate through the signed-swap tail | `P13DescentMaster.toSL3_injective` | MISMATCH | MISMATCH | literal | unconditional | - | NO | CORRECTED against docs/P13_STEP_AUDIT.md §2 (P13.08 vs P13.09–11): Lean inverts the order, and the audit finds the printed order is not executable as printed — the defect is on the TeX side |
| BT.24 | rem:classical-base | the eight relations present SL₃(ℤ), and ℬ is then the affine group ℤ³ ⋊ SL₃(ℤ) | `LiteralBaseCompleteness.baseAffineEquiv` | EXACT | EXACT | literal | unconditional | CRW, CLV, BHV | NO | the surjection ℬ → Γ̄ is proved bijective internally, as the TeX asserts |
| BT.25 | rem:classical-base | the presentations go back to CRW, the matrix-labelled generators to CLV, and property (T) of the affine group is classical | - | MISSING | MISSING | - | literature-input | CRW, CLV, BHV | NO | scholarship only; the TeX says the proofs here are independent |
| WI.01 | con:clifford | the real Clifford-algebra convention: generators c_x with c_x² = 1 and c_xc_y = −c_yc_x for x ≠ y; ClLamp(X) generated by −1 and the c_x | `ManuscriptExactWrappers.manuscriptCliffordConstruction` | EXACT | EXACT | literal | unconditional | - | NO | quadratic form, generators, and the generated subgroup all `rfl` |
| WI.02 | con:clifford | ζ = −1 is a nontrivial central involution; ClLamp(X) is a central extension of the elementary abelian 2-group on X | `CliffordAlgebraLamp.zGen_ne_one`; `CliffordAlgebraLamp.zGen_sq`; `CliffordAlgebraLamp.zGen_mem_center` | EXACT | EXACT | literal | unconditional | - | NO | - |
| WI.03 | con:clifford | every permutation of X acts by c_x ↦ c_{σx} and fixes ζ | `CliffordAlgebraLamp.cliffordLamp_permutation_package` | EXACT | EXACT | literal | unconditional | - | NO | - |
| WI.04 | lem:linear | the seven displayed 4×4 rational matrices and the dilation D = diag(2,2,2,1) | `ManuscriptExactWrappers.manuscriptLinearModel` | EXACT | EXACT | literal | unconditional | - | NO | each matrix is `rfl` against the printed entries |
| WI.05 | lem:linear | the six matrices satisfy all twenty relators of ℬ | `LiteralNonMFLinearWitness.matrixBaseGenerator_kills` | EXACT | EXACT | literal | unconditional | - | NO | - |
| WI.06 | lem:linear | ᾱ(u) = DuD⁻¹ is an injective endomorphism of Γ̄ squaring the translations and fixing x,y,z | `ExplicitLinearModel.conjD_injective`; `LiteralNonMFLinearWitness.conjD_v1G`; `LiteralNonMFLinearWitness.conjD_xG` | EXACT | EXACT | literal | unconditional | - | NO | all six equations |
| WI.07 | lem:linear | the matrix assigned to v₁ does not lie in range(ᾱ) | `ExplicitLinearModel.v1G_not_mem_range` | EXACT | EXACT | literal | unconditional | - | NO | - |
| WI.08 | lem:linear | proof: every generator and its computed inverse is integral, so Γ̄ ≤ GL₄(ℤ); D⁻¹v̄₁D has entry 1/2 in position (1,4) | `ExplicitIntegralLinearModel.gammaBar_residuallyFinite`; `ExplicitLinearModel.v1G_not_mem_range` | EXACT | EXACT | literal | unconditional | - | NO | - |
| WI.09 | p:witness-telescope | T = colim(Γ̄, ᾱ), V = T ⋊ ℤ with shift τ, level-zero map j, X = V/j(Γ̄) with root o | `MappingTelescope.Telescope`; `MarkedCompression.Vertical`; `MarkedCompression.Cosets` | EXACT | EXACT | literal | unconditional | - | NO | - |
| WI.10 | p:witness-telescope | the final assertion of the linear model states τo ≠ j(v̄₁)τo, so the Clifford generators at those sites anticommute | `MarkedCompression.moved_cosets_ne`; `CliffordLamp.commutator_lamp_lamp` | EXACT | EXACT | literal | unconditional | - | NO | - |
| WI.11 | prop:witness | Proposition 8.4: w ≠ 1 in E | `LiteralNonMFLinearWitness.literal_mark_ne_one` | EXACT | EXACT | literal | unconditional | - | NO | - |
| WI.12 | prop:witness | proof: form W = ClLamp(X) ⋊ V and define the map on generators by g ↦ j(ḡ), t ↦ τ, c ↦ c_o | `LiteralNonMFLinearWitness.realization` | EXACT | EXACT | literal | unconditional | - | NO | - |
| WI.13 | prop:witness | the exact checks give the twenty base and six stable-letter relations; the level-zero subgroup fixes o, so c_o commutes with every base generator and c_o² = 1 | `LiteralNonMFLinearWitness.realization` | EXACT | EXACT | literal | unconditional | - | NO | discharged as the fields of the realization datum |
| WI.14 | prop:witness | under the assignment tct⁻¹ ↦ c_{τo} and v₁(tct⁻¹)v₁⁻¹ ↦ c_{j(v̄₁)τo} | `MarkedCompression.conj_inl_lamp` | EXACT | EXACT | literal | unconditional | - | NO | - |
| WI.15 | prop:witness | the two sites are distinct, so w ↦ [c_{τo}, c_{j(v̄₁)τo}] = −1 = ζ | `LiteralNonMFLinearWitness.realization_marked_word`; `MarkedCompression.signAmbient_ne_one` | EXACT | EXACT | literal | unconditional | - | NO | - |
| WI.16 | prop:witness | ζ central in W, so the eight centrality relations hold; the assignment extends to E → W with w ↦ ζ ≠ 1 | `LiteralNonMFLinearWitness.literal_mark_ne_one` | EXACT | EXACT | literal | unconditional | - | NO | - |
| WI.17 | p:witness-scope | each group element involves only finitely many Clifford sites; the mapping telescope supplies the group and the range characterization separates the sites; no HNN normal-form theorem is needed | `CliffordLamp.isLocallyFiniteGroup_cliffordLamp`; `MarkedCompression.moved_cosets_ne` | EXACT | EXACT | literal | unconditional | - | NO | - |
| PA.01 | lem:square | Lemma 9.1: for d² = 1, [d, a₁da₁⁻¹] = [d, a₁]² | `commutator_conjugate_eq_commutator_sq_of_sq_eq_one` | EXACT | EXACT | literal | unconditional | - | NO | universe-polymorphic |
| PA.02 | lem:square | proof: b = a₁da₁⁻¹ is an involution, [d,a₁] = db, and (db)² = [d,b] | `commutator_conjugate_eq_commutator_sq_of_sq_eq_one` | EXACT | MISMATCH | literal | unconditional | - | NO | Lean discharges it by `simp only [commutatorElement_def, …]` then `group`, not through the printed b = db factorization |
| PA.03 | thm:A | proof of A(1): Proposition 8.4 | `LiteralNonMFLinearWitness.literal_mark_ne_one` | EXACT | EXACT | literal | unconditional | - | NO | - |
| PA.04 | thm:A | proof of A(2): pass from Θ : E → U_cor((d_n)) to the corona representation κ∘Θ | `LiteralNonMFEndpoint.literal_mark_eq_one_in_unitaryCorona` | EXACT | EXACT | literal | unconditional | - | NO | - |
| PA.05 | thm:A | apply the central-sign criterion with Γ = ℬ, ι, t, c ∈ E and a = v₁ | `LiteralNonMFEndpoint.literal_centralSignCriterion` | EXACT | EXACT | literal | unconditional | - | NO | the criterion is instantiated verbatim, with every hypothesis discharged from the presentation |
| PA.06 | thm:A | the hypotheses are the displayed relators: (T) of ℬ, the six stable-letter relators, the six c-commutation relators | `LiteralBaseP13PropertyTBridge.manuscriptBaseHasKazhdanPropertyT`; `LiteralNonMFPresentation.stable_conjugates_base_into_base`; `LiteralNonMFPresentation.lamp_commutes_base` | EXACT | EXACT | literal | unconditional | - | NO | - |
| PA.07 | thm:A | in E, d² = (tct⁻¹)² = tc²t⁻¹ = 1, so Lemma 9.1 identifies w as u² | `LiteralNonMFEndpoint.mark_eq_compressionDefect_sq`; `LiteralNonMFEndpoint.mark_eq_rootCommutator_sq` | EXACT | EXACT | literal | unconditional | - | NO | - |
| PA.08 | thm:A | centrality of w is a defining relator; with c² = 1 it forces w² = 1; and w ≠ 1 as the theorem states | `LiteralNonMFPresentation.mark_central`; `LiteralNonMFPresentation.mark_sq` | EXACT | EXACT | literal | unconditional | - | NO | - |
| PA.09 | thm:A | since κ is injective, Θ(w) = 1 | `LiteralNonMFEndpoint.literal_mark_eq_one_in_unitaryCorona` | EXACT | EXACT | literal | unconditional | - | NO | - |
| PA.10 | thm:A | an MF embedding of E would be an injective corona representation, impossible since w ≠ 1 dies | `LiteralNonMFEndpoint.literal_not_isCDEOperatorMF` | EXACT | EXACT | literal | unconditional | - | NO | - |
| PA.11 | thm:A | if C*_red(E) were MF, complement correction plus g ↦ λ_g would give an injective corona representation | `LiteralNonMFEndpoint.literal_reducedGroupCStar_not_isMFAlgebra` | EXACT | EXACT | literal | unconditional | - | NO | - |
| PA.12 | thm:A | the canonical map E → U(C*_max(E)) is injective because the left regular representation factors through it; so C*_max(E) is not MF either | `LiteralNonMFEndpoint.literal_maximalGroupCStar_not_isMFAlgebra`; `maximalGroupCStarUnitaryHom_injective` | MISMATCH | MISMATCH | substituted | unconditional | - | NO | the Lean maximal algebra is universe-relative (Appendix C), so the object is not the class-sized C*_max |
| PA.13 | p:A-marked-radical | w lies in the kernel of every corona representation, so every corona representation factors through E/⟨w⟩, and ⟨w⟩ = {1,w} is central | `LiteralNonMFEndpoint.literal_mark_mem_manuscriptCoronaMFResidual`; `LiteralNonMFEndpoint.coe_literalInvolutionSubgroup` | EXACT | EXACT | literal | unconditional | - | NO | - |
| PA.14 | p:A-marked-radical | by Theorem 4.4 the same holds in every countable group with a Kazhdan conjugation datum | `ManuscriptExactWrappers.manuscriptFiniteNormalObstructionCriterion` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0 |
| PA.15 | p:A-marked-radical | the sign is a certificate, not the source: the whole compression defect, in particular u = [d,ι(v₁)], is HS invisible in every operator-norm almost representation | `LiteralNonMFEndpoint.kazhdanPinning` | EXACT | MISMATCH | literal | unconditional | - | NO | Appendix B route |
| PA.16 | p:A-marked-radical | Section 11 develops the radical, and Theorem 11.29 places u itself inside it: Rad_MF(E) properly contains {1,w} | `LiteralSignFreeQuotient.signFree_collapse` | EXACT | EXACT | literal | unconditional | - | NO | replaces the former "whether E/⟨w⟩ is MF is open", which the manuscript retired during this audit |
| PA.17 | p:A-corner-ranks | the corner discards zero-rank coordinates and renormalizes on the corner, so the estimates are independent of r_n/d_n | `FiniteNormalAverageCorner.exists_corner_with_finite_sum_vanishing` | EXACT | EXACT | literal | unconditional | - | NO | the returned corner carries `B.modelNonempty` and its own normalized trace |
| CY.01 | thm:C | Theorem C: E_BS is finitely presented and w_BS ≠ 1 | `LiteralCyclicCalibration.manuscriptCyclicCalibration` | EXACT | EXACT | literal | unconditional | - | NO | three generators, seven relators, all `rfl`, plus `Group.IsFinitelyPresented` |
| CY.02 | thm:C | there is an explicit surjection onto the realized Clifford quotient sending w_BS to the nontrivial central sign | `LiteralCyclicCalibration.manuscriptCyclicCalibration` | EXACT | EXACT | literal | unconditional | - | NO | surjectivity, nontriviality, the value z_BS, and centrality are all conjuncts |
| CY.03 | thm:C | every finite-dimensional representation over every field maps w_BS to the identity | `LiteralCyclicCalibration.manuscriptCyclicCalibration` | EXACT | EXACT | literal | unconditional | - | NO | last conjunct |
| CY.04 | thm:C | proof: w_BS² = 1 is redundant because both conjugates are involutions and centrality forces it; deleting it gives a six-relator presentation of the same group | `LiteralCyclicCalibration.manuscriptCyclicCalibration` | MISMATCH | MISMATCH | literal | unconditional | - | NO | the redundancy is used, but the "six-relator presentation of the same group" is not stated anywhere in Lean |
| CY.05 | thm:C | the stable relation gives t⟨γ₀⟩t⁻¹ ⊆ ⟨γ₀⟩ and c centralizes the cyclic base | `LiteralCyclicCalibration.manuscriptCyclicCalibration` | EXACT | EXACT | literal | unconditional | - | NO | encoded by the displayed relators |
| CY.06 | thm:C | the same commutant argument as in Theorem B kills w_BS in every finite-dimensional representation | `LiteralCyclicCalibration.finiteDimensional_kill` | EXACT | EXACT | literal | unconditional | - | NO | routes through `map_marked_commutator_eq_one_units`, i.e. literally Theorem B |
| CY.07 | thm:C | nontriviality: use the affine realization of BS(1,2) and its coset action; the root site is fixed by the cyclic base and the sites of t and γ₀t are distinct | `LiteralCyclicCalibration.realization` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CY.08 | thm:C | attach Clifford generators and map c to the root lamp; all seven relators hold and w_BS ↦ −1 | `LiteralCyclicCalibration.quotientMap_mark_val`; `LiteralCyclicCalibration.mark_ne_one` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CY.09 | thm:C | restricting the target to the subgroup generated by the three images gives the asserted surjective realized quotient | `LiteralCyclicCalibration.quotientMap_surjective` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CY.10 | p:C-sharpness | the realized Clifford quotient is amenable, hence MF, and detects w_BS; so (T) cannot be omitted from the central-sign criterion | - | MISSING | MISSING | - | literature-input | TWW | NO | amenable ⇒ MF is quoted; no Lean amenability predicate is applied here |
| CY.11 | p:C-sharpness | BS(1,2) ≅ ℤ[1/2] ⋊ ℤ is solvable; the Clifford lamp group on its coset space is locally finite; the semidirect product is amenable | `CliffordLamp.isLocallyFiniteGroup_cliffordLamp` | MISMATCH | MISSING | literal | literature-input | - | NO | only local finiteness of the lamp is formal; solvability and amenability of the product are not |
| CY.12 | p:C-sharpness | the realized quotient, a subgroup of an amenable group, is amenable hence MF | - | MISSING | MISSING | - | literature-input | TWW | NO | - |
| CY.13 | p:C-sharpness | in radical language, w_BS ∉ Rad_MF(E_BS) | - | MISSING | MISSING | - | literature-input | TWW | NO | depends on CY.12 |
| CY.14 | p:C-approx | in every finite group the doubling relation identifies the images of ⟨γ₀²⟩ and ⟨γ₀⟩, so the marked word dies and neither group is residually finite | `CyclicBaseLEFObstruction.cyclicBase_exactModel_package` | EXACT | EXACT | literal | unconditional | - | NO | includes `¬ Group.ResiduallyFinite RealizedQuotient` |
| CY.15 | p:C-approx | the same equations transport through any exact local embedding, so neither group is LEF | `CyclicBaseLEFObstruction.cyclicBase_exactModel_package` | EXACT | EXACT | literal | unconditional | - | NO | both `¬ IsLEF` clauses |
| RA.01 | def:radical | Rad_MF(G₁) = ∩ ker Θ over corona representations, a normal subgroup | `ManuscriptExactWrappers.manuscriptMFRadical` | EXACT | EXACT | literal | unconditional | - | NO | universe-polymorphic |
| RA.02 | def:radical | the intersection does not change if arbitrary positive dimension sequences are allowed | `manuscriptCoronaMFInvisible_iff_actualCoronaMFInvisible` | EXACT | EXACT | literal | unconditional | - | NO | - |
| RA.03 | lem:portable | functoriality: φ(Rad_MF(G₁)) ⊆ Rad_MF(G₂) | `ManuscriptExactWrappers.manuscriptRadicalPortability` | EXACT | EXACT | literal | unconditional | - | NO | universe-polymorphic in both groups |
| RA.04 | lem:portable | in particular φ : E → G₂ with φ(w) ≠ 1 forces G₂ non-MF | `ManuscriptExactWrappers.manuscriptRadicalPortability` | EXACT | EXACT | literal | unconditional | - | NO | - |
| RA.05 | lem:portable | proof: Θ∘φ is a corona representation of G₁; for the second statement use w ∈ Rad_MF(E) and injectivity | `map_manuscriptCoronaMFResidual_le` | EXACT | EXACT | literal | unconditional | - | NO | - |
| RA.06 | prop:univquot | (1) R is the kernel of a single corona representation of G₁ | `exists_manuscriptCoronaRepresentation_ker_eq_manuscriptCoronaMFResidual` | EXACT | EXACT | literal | unconditional | - | NO | - |
| RA.07 | prop:univquot | (2) G₁/R is MF | `manuscriptCoronaMFQuotient_isCDEOperatorMF` | EXACT | EXACT | literal | unconditional | - | NO | - |
| RA.08 | prop:univquot | (3) every homomorphism from G₁ to an MF group factors through G₁/R | `existsUnique_manuscriptCoronaMFQuotient_factorization_to_isCDEOperatorMF` | EXACT | EXACT | literal | unconditional | - | NO | Lean proves existence and uniqueness; the TeX asserts only existence |
| RA.09 | prop:univquot | G₁ is MF iff R = {1} | `isCDEOperatorMF_iff_manuscriptCoronaMFResidual_eq_bot` | EXACT | EXACT | literal | unconditional | - | NO | - |
| RA.10 | prop:univquot | proof of (1),(2): every nonidentity element of Q = G₁/R is detected by a corona representation of Q | `manuscriptCoronaMFQuotient_isCDEOperatorMF` | EXACT | EXACT | literal | unconditional | - | NO | - |
| RA.11 | prop:univquot | proof: enumerate detectors, pass to unitary lifts, diagonalize by selecting at stage k a coordinate with multiplicativity within 1/k and each marked element still separated, then take the block sum | `manuscriptCoronaMFQuotient_isCDEOperatorMF` | EXACT | EXACT | literal | unconditional | - | NO | the diagonalization is inside the cited proof chain, via the weak-MF universal corona |
| RA.12 | prop:univquot | block operator norms are maxima, so the sequence is an almost representation detecting every nonidentity element; its class is a faithful corona representation | `OperatorMFLocalNormalization.isNormApproximable_one` | EXACT | EXACT | literal | unconditional | - | NO | - |
| RA.13 | cor:exactradical | every corona representation factors uniquely through G₁/N when N ≤ Rad_MF(G₁); if G₁/N is MF then Rad_MF(G₁) = N | `ManuscriptExactWrappers.manuscriptExactRadicalFromCandidateQuotient` | EXACT | EXACT | literal | unconditional | - | NO | universe-polymorphic |
| RA.14 | cor:pullback | unconditionally Rad_MF(G₁) = q⁻¹(Rad_MF(G₁/N)) for N ≤ Rad_MF(G₁) | `ManuscriptExactWrappers.manuscriptRadicalReductionToQuotient` | EXACT | EXACT | literal | unconditional | - | NO | universe-polymorphic |
| RA.15 | cor:pullback | proof: forward by functoriality; conversely every corona representation of G₁ kills N and factors | `TorsionCompressionCollapse.actualCoronaMFResidual_eq_comap_quotient` | EXACT | EXACT | literal | unconditional | - | NO | - |
| RA.16 | prop:mfclosure | membership characterization of cl_MF(N) | `mem_actualCoronaMFClosure_iff` | EXACT | EXACT | literal | unconditional | - | NO | universe-polymorphic |
| RA.17 | prop:mfclosure | cl_MF is extensive, monotone, idempotent; G₁/cl_MF(N) is MF; cl_MF(N) = N iff G₁/N is MF | `manuscriptRelationClosure` | EXACT | EXACT | literal | unconditional | - | NO | all five clauses |
| RA.18 | p:radical-presentation | for G = ⟨X \| R⟩ = F/N the closure of N consists of the relations satisfied by every solution of R in every MF group, and G is MF exactly when N is closed | `mem_actualCoronaMFClosure_iff`; `LiteralUniversalHorn.manuscriptLiteralUniversalHorn` | EXACT | EXACT | literal | unconditional | - | NO | the presentation reading is the Horn proposition |
| RA.19 | p:radical-presentation | the marked element of Theorem A is an element of cl_MF(N) \ N for the forty-one relators | `LiteralUniversalHorn.manuscriptLiteralUniversalHorn` | EXACT | EXACT | literal | unconditional | - | NO | - |
| RA.20 | prop:sounditeration | every subgroup reached by the two operations lies in Rad_MF; a reached normal subgroup with MF quotient equals it; if the whole group is reached, every homomorphism to a countable MF group is trivial | `manuscriptSoundIterationClosure` | EXACT | EXACT | literal | unconditional | - | NO | universe-polymorphic; `IsSoundIterate` is the inductive predicate for the two printed operations |
| RA.21 | prop:sounditeration | proof: induct over the two operations, using Corollary 11.9 for the closure step and that the radical is an upper bound for joins | `IsSoundIterate.le_actualCoronaMFResidual` | EXACT | EXACT | literal | unconditional | - | NO | - |
| RA.22 | p:radical-sound-rules | Theorems 4.4, 4.9 and 11.22 are sound rules in this sense; Theorem 11.28 is the case where one application reaches the whole group | `ManuscriptExactWrappers.manuscriptInvolutiveCollapse`; `ManuscriptExactWrappers.manuscriptDefectSaturation` | MISMATCH | MISSING | literal | unconditional | - | NO | univ0; and no declaration exhibits these theorems as instances of `IsSoundIterate` |
| RA.23 | p:radical-sound-rules | a rule instance can hold at a later stage without holding earlier | - | MISSING | MISSING | - | unconditional | - | NO | illustrative, not formalized |
| RA.24 | cor:nofaithful | for a unital C*-algebra A embedding in a norm matrix corona, E admits no injective homomorphism into U(A) | `LiteralNonMFConsequences.literal_no_faithful_corona_subalgebra_target` | EXACT | EXACT | literal | unconditional | - | NO | universe-polymorphic in A |
| RA.25 | cor:nofaithful | proof: complement correction makes ĵ an injective homomorphism on U(A), so ĵ∘φ is a corona representation; Theorem A(2) and injectivity give φ(w) = 1 | `nonUnitalStarAlgHomUnitaryMap_injective` | EXACT | EXACT | literal | unconditional | - | NO | - |
| PM.01 | lem:permanence | (1) every subgroup of an MF group is MF | `IsOperatorMF.subgroup` | EXACT | EXACT | literal | unconditional | - | NO | - |
| PM.02 | lem:permanence | (2) every residually finite group is MF | `isOperatorMF_of_residuallyFinite` | EXACT | EXACT | literal | unconditional | - | NO | - |
| PM.03 | lem:permanence | (3) every locally finite group is MF | `isOperatorMF_of_locallyFinite` | EXACT | EXACT | literal | unconditional | - | NO | - |
| PM.04 | lem:permanence | proof of (2): a finite quotient injective on F, composed with its left regular permutation action, is an exact local model separating by at least 1 | `isNormApproximable_of_finite` | EXACT | EXACT | literal | unconditional | - | NO | - |
| PM.05 | lem:permanence | proof of (3): a finite test set lies in a finite subgroup K; the identity on K composed with its regular action is an exact local model | `isOperatorMF_of_locallyFinite` | EXACT | EXACT | literal | unconditional | - | NO | - |
| PM.06 | cor:quotclosure | MF groups are not closed under quotients: F₈ is MF and E is a non-MF quotient | `LiteralMFQuotientControls.manuscriptQuotientNonclosure` | EXACT | EXACT | literal | unconditional | - | NO | - |
| PM.07 | cor:quotclosure | proof: map the eight free generators onto the eight displayed generators; F₈ is residually finite hence MF | `LiteralMFQuotientControls.quotientMap8_surjective` | EXACT | EXACT | literal | unconditional | - | NO | - |
| ST.01 | p:stability-def | definition of point-norm matricial stability and of Rad_fd(G) | `MatricialStabilityRadical.IsPointNormMatriciallyStable`; `MatricialStabilityRadical.fdUnitaryResidual` | EXACT | EXACT | literal | unconditional | - | NO | - |
| ST.02 | prop:stabradical | Rad_MF(G) ≤ Rad_fd(G) always | `MatricialStabilityRadical.actualCoronaMFResidual_le_fdUnitaryResidual` | EXACT | EXACT | literal | unconditional | - | NO | - |
| ST.03 | prop:stabradical | equality for point-norm matricially stable G | `MatricialStabilityRadical.actualCoronaMFResidual_eq_fdUnitaryResidual` | EXACT | EXACT | literal | unconditional | - | NO | - |
| ST.04 | prop:stabradical | a stable group with Rad_fd(G) ≠ 1 is not MF | `MatricialStabilityRadical.not_isCDEOperatorMF_of_stable_of_fdResidual_ne_bot` | EXACT | EXACT | literal | unconditional | - | NO | - |
| ST.05 | prop:stabradical | proof of the first inclusion: amplify π to π^{⊕n} on ℂ^{nd}, dimensions strictly increasing, and ‖π^{⊕n}(x) − 1‖ = ‖π(x) − 1‖ | `MatricialStabilityRadical.constCoronaRep` | MISMATCH | MISMATCH | substituted | unconditional | - | NO | Lean uses the constant sequence (fun _ ↦ Y) with `opLength`, not the printed strictly increasing amplification π^{⊕n} |
| ST.06 | prop:stabradical | proof of the converse: lifts of a detecting Θ form an almost representation, stability supplies π_n with π_n(x) = 1, contradicting the uniform lower bound | `MatricialStabilityRadical.fdUnitaryResidual_le_coronaMFResidual` | EXACT | EXACT | literal | unconditional | - | NO | - |
| ST.07 | p:stability-axis | for a stable group corona representation theory is computed by finite-dimensional representation theory; combined with Theorem B this is an obstruction axis with no torsion, marked word or datum | `MatricialStabilityRadical.actualCoronaMFResidual_eq_fdUnitaryResidual`; `ManuscriptExactWrappers.manuscriptTheoremB` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CO.01 | def:invwitness | definition of an involutive compression witness (W1)–(W3) and of D_coll(L,s) | `ManuscriptExactWrappers.manuscriptInvolutiveCollapsePattern` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0; the three conditions and the normal closure are `Iff.rfl`/`rfl` |
| CO.01b | p:collapse-lamp-intro | killing the central sign of the Kazhdan–Clifford group makes all lamps commute and the moved root lamp becomes an involutive witness outright | `CommutingLampCollapse.commutingLampQuotient_collapse` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CO.02 | p:collapse-wreath | in a permutational wreath product with x₀ fixed by sLs⁻¹, every lamp involution at x₀ is a witness | `CommutingLampCollapse.commutingLampQuotient_collapse` | MISMATCH | MISMATCH | substituted | unconditional | - | NO | verified for the Clifford-lamp ambient group, not for a general permutational wreath product |
| CO.03 | thm:collapse | Theorem 11.22: D_coll(L,s) ≤ Rad_MF(H) for a Kazhdan L with a one-sided compressor s | `ManuscriptExactWrappers.manuscriptInvolutiveCollapse` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0; all six printed steps are present |
| CO.04 | thm:collapse | Step 1: exact commuting involution microstates V_n(γ) with covariance, by spectral sign of the Hermitian part and induction over an enumeration of L | `InvolutionOrbitMicrostates.exists_involutionMicrostates`; `InvolutionOrbitMicrostates.raw_covariance_vanishing` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CO.04b | thm:collapse | Step 1: block compression along the finite commutative corner structure of the previously corrected microstates preserves exact commutation | `InvolutionOrbitMicrostates.exists_involutionMicrostates` | MISMATCH | MISMATCH | substituted | unconditional | - | NO | CORRECTED against docs/COLLAPSE_STEP_AUDIT.md COL.06: the TeX names one compression along the joint corner structure; Lean compresses differently |
| CO.05 | thm:collapse | Step 2: for commuting exact involutions T = u − w satisfies T³ = 4T, so Tr \| u−w \| ² = 4·rank((u−w)²/4) and d_n is an integer-valued pseudometric | `InvolutionCollapseMetric.dV`; `InvolutionCollapseMetric.dV_triangle`; `InvolutionRankMass.rank_eq_of_projections_close` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CO.06 | thm:collapse | Step 2: projections at operator distance < 1 have equal rank, so d_n is eventually translation invariant | `InvolutionCollapseMetric.eventual_invariance` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CO.07 | thm:collapse | Step 3: (T) makes L finitely generated; k_n = Σ_{a∈S} d_n(1,a); d_n(1,γ) ≤ \| γ \| _S k_n eventually | `InvolutionCollapseProfile.wordLen`; `InvolutionCollapseProfile.eventually_dV_le_wordLen_mul_kNorm` | MISMATCH | MISMATCH | literal | unconditional | - | NO | CORRECTED against docs/COLLAPSE_STEP_AUDIT.md COL.17: Lean bounds a different word-length object than the printed word length |
| CO.08 | thm:collapse | Step 3: if k_n = 0 along a subsequence the orbit collapses and the marked commutator dies, against the separation; so k_n ≥ 1 eventually | `InvolutionCollapseProfile.eventually_one_le_kNorm_of_marked` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CO.09 | eq:generator-mass | Step 4: b_n(γ) = k_n^{-1/2}(V_n(γ) − V_n(1)), ‖b_n(γ)‖_F² ≤ 4 \| γ \| _S, and Σ_{a∈S}‖b_n(a)‖_F² = 4 | `InvolutionCollapseProfile.bVec`; `InvolutionCollapseProfile.norm_bVec_sq_le`; `InvolutionCollapseProfile.sum_normSq_bVec_eq_four` | MISMATCH | MISMATCH | literal | unconditional | - | NO | CORRECTED against docs/COLLAPSE_STEP_AUDIT.md COL.19: the Lean `bVec` carries a guard the printed b_n(γ) does not |
| CO.09b | eq:generator-mass | Step 4: ‖b_n(γ)‖²_F ≤ 4·(word length) at every large stage | `InvolutionCollapseProfile.norm_bVec_sq_le` | MISMATCH | MISMATCH | literal | unconditional | - | NO | CORRECTED against docs/COLLAPSE_STEP_AUDIT.md COL.20: Lean strengthens the intermediate estimate to remove the guard of COL.19 |
| CO.10 | thm:collapse | Step 4: the first grouping bounds rank D_n by ( \| γ \| + \| μ \| + \| a \| )k_n; the second makes ‖D_n‖ → 0; Tr \| D \| ² ≤ rank(D)‖D‖² gives vanishing normalized defect mass | `InvolutionCollapseCocycle.eventually_coboundary_defect_small` | EXACT | EXACT | literal | unconditional | - | NO | both groupings are used, as the TeX insists |
| CO.11 | thm:collapse | Step 5: Gaussians of the almost-cocycle are almost invariant, and the spectral gap bounds the limiting profile by its generator values (Delorme at the level of limiting seminorms) | `Ultralimit.centerRadius`; `InvolutionCollapseCocycle.profile_halmost` | MISMATCH | MISMATCH | literal | unconditional | - | NO | CORRECTED against docs/COLLAPSE_STEP_AUDIT.md COL.28: the Delorme/profile bound differs from the printed spectral-gap bound on two counts |
| CO.12 | thm:collapse | Step 5: a circumcenter of the displacement orbit at the level of bounded sequences produces a primitive w_n with b_n(a) ≈ w_n − U_{a,n}w_nU_{a,n}* | `InvolutionCollapseCenter.exists_approximate_coboundary` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CO.13 | thm:collapse | Step 6: by (W2) the displacement vanishes on compressed elements, so the primitive is almost fixed by them and u_n = U_{s,n}*w_nU_{s,n} is almost fixed by every a ∈ S | `InvolutionCollapseIndexCapture.index_capture` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CO.14 | thm:collapse | Step 6: transporting forward as in Theorem 3.1 (compression to the almost-fixed spectral subspace, then P ≤ VPV* at the rescaled mass) returns w_n almost fixed by every a ∈ S | `InvolutionCollapseEndpoint.stage_transport_bound`; `InvolutionCollapseIndexCapture.matMass_reverse_displacement` | MISMATCH | MISMATCH | literal | unconditional | - | NO | CORRECTED against docs/COLLAPSE_STEP_AUDIT.md COL.33: the compression to the almost-fixed spectral subspace is re-derived, not obtained from the cited transport theorem |
| CO.14b | thm:collapse | Step 6: transporting forward returns w_n up to vanishing mass, again almost fixed by every a ∈ S | `InvolutionCollapseEndpoint.stage_transport_bound` | MISMATCH | MISMATCH | literal | unconditional | - | NO | CORRECTED against docs/COLLAPSE_STEP_AUDIT.md COL.35: a quantitative one-stage substitute stands where the manuscript asserts a limit |
| CO.14c | thm:collapse | Step 6 is an instance of the transport theorem at the rank weight w_n = k_n | `InvolutionCollapseEndpoint.stage_capture`; `InvolutionCollapseEndpoint.stage_transport_bound` | MISMATCH | MISMATCH | literal | unconditional | - | NO | CORRECTED against docs/COLLAPSE_STEP_AUDIT.md R1: the rank weight is genuinely carried and no dimension-normalized substitute occurs, but neither `manuscriptKazhdanTransport` nor `scaled_transport_both` is ever invoked — Step 6 is re-derived inline, so the manuscript's deduction from a previously proved theorem is not the Lean deduction |
| CO.15 | thm:collapse | Step 6: contradiction with the generator mass; normality of corona kernels extends the conclusion to all of D_coll(L,s) | `InvolutionCollapseEndpoint.no_marked_model`; `InvolutionCollapseEndpoint.involutiveCollapseDefect_le_actualCoronaMFResidual` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CO.16 | rem:collapse-finite-stage | the limits can be replaced by explicit tolerances and the contradiction assembled at one late coordinate; that bookkeeping is not printed | `InvolutionCollapseEndpoint.numeric_transport_bound` | EXACT | EXACT | literal | unconditional | - | NO | Lean does carry explicit tolerances |
| CO.16b | rem:collapse-finite-stage | the single stage already fails: a family of at most ρ-small values cannot carry total squared mass four | `InvolutionCollapseEndpoint.anchor_contradiction` | EXACT | EXACT | literal | unconditional | - | NO | the arithmetic closing the one-coordinate assembly, against `eq:generator-mass`; header closed 2026-08-16 |
| CO.17 | rem:collapse-finite-stage | (W3) is essential: it supplies the joint spectral calculus behind the rank identity; anticommuting Clifford coordinates have no joint spectral labels | `InvolutionCollapseMetric.dV` | MISMATCH | MISSING | literal | unconditional | - | NO | (W3) is used, but the necessity claim about anticommuting coordinates is not formalized |
| CO.18 | thm:projection-collapse | Theorem 11.24: an arbitrary corona projection with commuting L-orbit, centralized by the compressed copy, commutes with Θ(L) | `ProjectionCompressionCollapse.corona_projection_collapse` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0 |
| CO.19 | thm:projection-collapse | proof: w = 1 − 2p is a self-adjoint unitary; the subgroup H' generated by Θ(H) and w is countable | `ProjectionCompressionCollapse.corona_projection_collapse` | EXACT | EXACT | literal | unconditional | - | NO | `countable_subgroupClosure` on a countable generating set |
| CO.20 | thm:projection-collapse | inside H', Θ(L) has (T), Θ(s) compresses it, w is an involutive witness; Theorem 11.22 places each [Θ(γ),w] in Rad_MF(H') | `InvolutionCollapseEndpoint.involutiveCollapseDefect_le_actualCoronaMFResidual` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CO.21 | thm:projection-collapse | the inclusion H' → U(Q) is a corona representation of H', so [Θ(γ),w] = 1 and w = 1 − 2p gives [Θ(γ),p] = 0 | `ProjectionCompressionCollapse.corona_projection_collapse` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CO.22 | p:collapse-relcomm | consequently Θ(sLs⁻¹)' ∩ Q cannot exceed Θ(L)' ∩ Q by a projection with commuting L-orbit | `ProjectionCompressionCollapse.corona_projection_collapse` | EXACT | EXACT | literal | unconditional | - | NO | restatement of the theorem |
| CO.23 | thm:torsion-collapse | Theorem 11.26: finite-order witnesses; every [γ,k] is invisible, the normal closure lies in Rad_MF(H), with equality when the quotient is MF | `TorsionSpectralCollapse.actualCoronaMFInvisible_of_torsionWitness`; `TorsionSpectralCollapse.torsionCollapseDefect_le_actualCoronaMFResidual_of_kazhdan`; `TorsionSpectralCollapse.actualCoronaMFResidual_eq_torsionCollapseDefect_of_kazhdan` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0 |
| CO.24 | thm:torsion-collapse | proof: the discrete Fourier idempotents p_j = m⁻¹ Σ ζ^{-jt}u^t are self-adjoint idempotents of the corona | `TorsionSpectralCollapse.fourierIdem`; `TorsionSpectralCollapse.star_fourierIdem`; `TorsionSpectralCollapse.fourierIdem_mul_self` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CO.25 | thm:torsion-collapse | each p_j is a polynomial in u, so the compressed copy centralizes it and the Θ(L)-conjugates commute pairwise | `TorsionSpectralCollapse.commute_fourierIdem` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CO.26 | thm:torsion-collapse | Theorem 11.24 makes every p_j commute with Θ(L); Fourier reconstruction expresses u as a ζ-weighted sum, so Θ([γ,k]) = 1 | `TorsionSpectralCollapse.actualCoronaMFInvisible_of_torsionWitness` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CO.27 | thm:commutinglamp | Theorem 11.27: W/⟨ζ⟩ is sofic and is not MF; the image of [v₁, tct⁻¹] is nontrivial and lies in its MF radical; the same holds for the general affine–Clifford ambient group | `CommutingLampQuotientSofic.literalSignFreeQuotient_isSofic_and_not_isCDEOperatorMF`; `CommutingLampCollapse.commutingLampQuotient_collapse`; `CommutingLampCollapse.literalCommutingLampQuotient_collapse`; `CommutingLampCollapse.literalCommutingLampQuotient_not_isCDEOperatorMF` | EXACT | EXACT | literal | unconditional | - | NO | the soficity clause moved into and out of a separate corollary during this audit; it is back in the theorem |
| CO.28 | thm:commutinglamp | proof: killing ζ makes any two lamps commute, so the q(L)-orbit of k commutes pairwise | `CommutingLampCollapse.commutingLampQuotient_collapse` | EXACT | EXACT | literal | unconditional | - | NO | the `hlampconj` block |
| CO.29 | thm:commutinglamp | k remains an involution and the compressed copy centralizes it because the compressed base fixes the moved site | `CommutingLampCollapse.commutingLampQuotient_collapse` | EXACT | EXACT | literal | unconditional | - | NO | the `hsite`/`hcommAmb` blocks |
| CO.30 | thm:commutinglamp | (T) passes to L, so Theorem 11.22 places every [q(v̄₁), k] in the MF radical of the quotient | `CommutingLampCollapse.commutingLampQuotient_collapse` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CO.31 | thm:commutinglamp | nontriviality survives: in the signed finite-support model the commutator has nonzero configuration coordinate while every element of ⟨ζ⟩ has zero | `CommutingLampCollapse.commutingLampQuotient_collapse` | EXACT | EXACT | literal | unconditional | - | NO | the `hne1` block |
| CO.31b | thm:commutinglamp | killing ζ abelianizes the lamp kernel: ClLamp(X)/⟨ζ⟩ is ⊕_X ℤ/2 under the same V-action, so W/⟨ζ⟩ ≅ (⊕_X ℤ/2) ⋊ V | `CommutingLampQuotientSofic.toModTwo`; `CommutingLampQuotientSofic.psiHom`; `CommutingLampQuotientSofic.Phi` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CO.31c | thm:commutinglamp | that kernel is again locally finite with finite level orbits, so the argument of Theorem E gives soficity unchanged; failure of MF is Theorem 11.27 | `CommutingLampQuotientSofic.isLocallyFiniteGroup_modTwoLamp`; `CommutingLampQuotientSofic.exists_finite_invariant_modTwo_subgroup` | EXACT | EXACT | literal | unconditional | - | NO | the Theorem E route is reused, not restated |
| CO.32 | p:collapse-route-closed | every route to an MF model of W through the commuting-lamp quotient is closed | `CommutingLampCollapse.literalCommutingLampQuotient_not_isCDEOperatorMF` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CO.32b | thm:commutinglamp | W/⟨ζ⟩ is a second finitely generated sofic non-MF group | `CommutingLampQuotientSofic.literalSignFreeQuotient_isSofic_and_not_isCDEOperatorMF` | EXACT | EXACT | literal | unconditional | - | NO | this corollary was split out of Theorem 11.27 during this audit |
| SF.01 | thm:signfree | Theorem 11.29: E/⟨w⟩ is not MF; the image of [ι(v₁),d] is nontrivial there and lies in Rad_MF(E/⟨w⟩); consequently {1,w} is a proper subgroup of Rad_MF(E) | `LiteralSignFreeQuotient.signFree_collapse`; `LiteralSignFreeQuotient.signFreeQuotient_not_isCDEOperatorMF`; `LiteralSignFreeQuotient.commutator_not_zpow_mark` | EXACT | EXACT | literal | unconditional | - | NO | added to the manuscript during this audit; all three clauses are separately badged |
| SF.02 | thm:signfree | d̄ = q(d) is an involution because c² = 1 | `LiteralSignFreeQuotient.dee_sq` | EXACT | EXACT | literal | unconditional | - | NO | - |
| SF.03 | thm:signfree | q(t)L̄q(t)⁻¹ centralizes d̄ because tι(ℬ)t⁻¹ commutes with c in E | `LiteralSignFreeQuotient.dee_commutes_compressed` | EXACT | EXACT | literal | unconditional | - | NO | - |
| SF.04 | thm:signfree | property (T) passes to L̄ and q(t) compresses it, so (W1) and (W2) hold and the content is (W3) | `LiteralSignFreeQuotient.signFree_collapse` | EXACT | EXACT | literal | unconditional | - | NO | - |
| SF.05 | thm:signfree | the rotation letters commute with d, and t carries each vᵢ to vᵢ², so ι(vᵢ²) commutes with d | `LiteralSignFreeQuotient.dee_commutes_x`; `LiteralSignFreeQuotient.dee_commutes_v1_sq` | EXACT | EXACT | literal | unconditional | - | NO | all three rotation letters and all three squared translations |
| SF.06 | thm:signfree | hence ι(g)dι(g)⁻¹ depends only on the exponent vector of the translation part modulo 2, leaving eight conjugates indexed by (ℤ/2)³ | `LiteralSignFreeQuotient.doubledBase`; `LiteralSignFreeQuotient.dee_commutes_doubledBase`; `LiteralSignFreeQuotient.rotations_le_doubledBase` | EXACT | EXACT | literal | unconditional | - | NO | - |
| SF.07 | thm:signfree | the six rotation words x, x², z, yz, yx, y²x carry the class of v₁ onto the six remaining nonzero classes, each commuting with d | `LiteralSignFreeQuotient.commutator_conj_transport`; `LiteralSignFreeQuotient.commutator_parity` | EXACT | EXACT | literal | unconditional | - | NO | - |
| SF.08 | thm:signfree | conjugating the displayed identity exhibits every nonzero parity commutator as a conjugate of w, the zero class gives [d,d] = 1, and centrality puts all eight in ⟨w⟩ | `LiteralSignFreeQuotient.commutator_via_orbit`; `LiteralSignFreeQuotient.commutator_not_mem_markSubgroup` | EXACT | EXACT | literal | unconditional | - | NO | - |
| SF.09 | thm:signfree | so d̄ is an involutive compression witness and Theorem 11.22 places [q(ι(v₁)), d̄] in Rad_MF(E/⟨w⟩) | `LiteralSignFreeQuotient.signFree_collapse` | EXACT | EXACT | literal | unconditional | - | NO | - |
| SF.10 | thm:signfree | nontriviality passes through E → W: the commutator goes to the product of the two distinct lamp basis elements while ⟨w⟩ goes into ⟨ζ⟩, whose configuration coordinate is zero | `LiteralSignFreeQuotient.commutator_not_zpow_mark` | EXACT | EXACT | literal | unconditional | - | NO | - |
| SF.11 | thm:signfree | hence the image is nontrivial and Proposition 11.6 makes E/⟨w⟩ non-MF; Corollary 11.9 identifies Rad_MF(E) with the q-preimage, so u belongs to it | `LiteralSignFreeQuotient.signFreeQuotient_not_isCDEOperatorMF`; `ManuscriptExactWrappers.manuscriptRadicalReductionToQuotient` | EXACT | EXACT | literal | unconditional | - | NO | - |
| SF.12 | p:signfree-second | the Clifford sign certifies an obstruction that survives its removal, and E/⟨w⟩ is a second finitely presented non-MF group | `LiteralSignFreeQuotient.signFreeQuotient_not_isCDEOperatorMF` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CO.33 | cor:collapsequot | unconditional radical reduction along the collapse quotient, with equality when the quotient is MF | `ManuscriptExactWrappers.manuscriptCollapseRadicalReduction` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0 |
| CO.34 | p:collapse-universal | in the second case the quotient is the universal MF quotient | `ManuscriptExactWrappers.manuscriptUniversalMFQuotient` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CO.35 | thm:saturation | (1) every homomorphism to a countable MF group kills D_coll(L,s) | `ManuscriptExactWrappers.manuscriptDefectSaturation` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0 |
| CO.36 | thm:saturation | (2) if D_coll(L,s) = H then Rad_MF(H) = H, every homomorphism to a countable MF group is trivial, and a nontrivial H is not MF | `ManuscriptExactWrappers.manuscriptDefectSaturation` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0 |
| CO.37 | thm:saturation | proof: functoriality plus subgroup permanence makes the radical of f(H) trivial | `DefectSaturation.involutiveCollapseDefect_le_ker_of_isCDEOperatorMF` | EXACT | EXACT | literal | unconditional | - | NO | - |
| CO.38 | p:saturation-remark | such a group admits no nontrivial finite-dimensional unitary representation, MF quotient, or homomorphism to a countable residually finite or amenable group | `DefectSaturation.map_eq_one_of_saturated` | MISMATCH | MISMATCH | literal | literature-input | TWW | NO | the MF-quotient and residually-finite cases follow; the amenable case needs amenable ⇒ MF, which is not formal |
| CO.39 | p:saturation-remark | whether a small-cancellation construction produces a f.p. group with saturated collapse or normal-Kazhdan defect is open | - | MISSING | MISSING | - | open | FFF | NO | stated open |
| RE.01 | p:D-preamble | every MF algebra is stably finite | - | MISSING | MISSING | - | literature-input | BK | NO | quoted; not used in the deduction, which supplies stable finiteness directly |
| RE.02 | p:D-preamble | stable finiteness is supplied by the faithful canonical trace, not inferred from the absence of MF structure | `LiteralNonMFEndpoint.manuscriptTheoremD` | EXACT | EXACT | literal | unconditional | - | NO | - |
| RE.03 | thm:D | Theorem D: C*_red(E) is unital, separable, carries a faithful tracial state, is stably finite, and is not MF | `LiteralNonMFEndpoint.manuscriptTheoremD` | EXACT | EXACT | literal | unconditional | - | NO | stable finiteness in every nonempty finite matrix amplification |
| RE.04 | p:D-base-injective | the canonical ℬ → E is injective: compose with E → W and use that ℬ → Γ̄ is an isomorphism and j is injective | `LiteralBaseCompleteness.baseAffineEquiv`; `MappingTelescope.level_injective` | EXACT | EXACT | literal | unconditional | - | NO | - |
| RE.05 | p:D-base-injective | since the infinite Kazhdan group ℬ is nonamenable, so is E; hence C*_red(E) is not nuclear | - | MISSING | MISSING | - | literature-input | BHV, Lance | NO | the TeX declares these two classical inputs explicitly |
| RE.05b | p:D-base-injective | E contains an isomorphic copy of the infinite Kazhdan base, hence is nonamenable | `NuclearityAmenability.manuscriptNotAmenableOfBaseEmbeds` | EXACT | EXACT | literal | unconditional | - | NO | the nonamenability half of RE.05, now proved; the step from nonamenable to non-nuclear is Lance and remains the literature input recorded there |
| RE.06 | lem:faithfultrace | (1) the canonical tracial state on C*_red(G₁) is faithful | `ManuscriptExactWrappers.manuscriptFaithfulTraceAndStableFiniteness` | EXACT | EXACT | literal | unconditional | - | NO | universe-polymorphic |
| RE.07 | lem:faithfultrace | (2) a unital C*-algebra with a faithful tracial state is stably finite: every isometry in M_I(A) is unitary, for every nonempty finite I | `ManuscriptExactWrappers.manuscriptFaithfulTraceAndStableFiniteness` | EXACT | EXACT | literal | unconditional | - | NO | both the general finite index set and the M_k form |
| RE.08 | lem:faithfultrace | proof (1): right translations commute with C*_red; τ(x*x) = 0 gives xδ_e = 0, hence xδ_g = 0 for all g, and the δ_g are total | `ReducedGroupCStarTrace.canonicalFaithfulTracialState` | EXACT | EXACT | literal | unconditional | - | NO | - |
| RE.09 | lem:faithfultrace | proof (2): τ_k is a faithful trace on M_k(A), and v*v = 1 makes y = 1 − vv* a projection with τ_k(y) = 0, so y = 0 | `FaithfulTracialState.matrix_mul_star_eq_one_of_star_mul_eq_one` | EXACT | EXACT | literal | unconditional | - | NO | - |
| SO.01 | thm:E | Theorem E: W is finitely generated, sofic, hence hyperlinear, and not MF | `NonMFImpact.witness_sofic_hyperlinear_nonMF` | EXACT | EXACT | literal | unconditional | - | NO | - |
| SO.02 | thm:E | the image of ᾱ has finite index (at most eight, by parity classes of the lattice), so every telescope level is commensurable with B | `LiteralBaseDoublingIndex.conjD_range_finiteIndex` | EXACT | EXACT | literal | unconditional | - | NO | supplies the `FiniteIndex` instance consumed by `isSofic_ambient` |
| SO.03 | thm:E | the stable letter conjugates B onto ᾱ(Γ̄), so all of V commensurates B; orbit–stabilizer makes every Γ̄_n-orbit in X finite | `MappingTelescopeFiniteOrbits.finite_verticalLevel_orbit` | EXACT | EXACT | literal | unconditional | - | NO | - |
| SO.04 | thm:E | a finite subset of ClLamp(X) ⋊ T has T-coordinates in one level and lamp coordinates with finite orbits, so it lies in L ⋊ Γ̄_n with L finite invariant | `SoficMarkedCompression.isSofic_lamp_telescope` | EXACT | EXACT | literal | unconditional | - | NO | via the local finite-kernel criterion |
| SO.05 | thm:E | L ⋊ Γ̄_n is sofic (finite-by-sofic) and soficity is local over finite subsets, so ClLamp(X) ⋊ T is sofic | `SoficMarkedCompression.isSofic_lamp_telescope` | EXACT | EXACT | literal | unconditional | - | NO | - |
| SO.06 | thm:E | reassociating gives W ≅ (ClLamp(X) ⋊ T) ⋊ ℤ | `SemidirectAssoc.assocEquiv` | EXACT | EXACT | literal | unconditional | - | NO | - |
| SO.07 | thm:E | a split extension of a sofic group by ℤ is sofic: truncate levels to ℤ/N, induce the kernel's approximations, and the wrap-around boundary occupies at most 2·abs(k)/N of the levels | `SoficIntegerExtension.isSofic_int_semidirectProduct`; `SoficIntegerExtension.card_badLevels_le` | EXACT | EXACT | literal | unconditional | ElekSzabo | NO | the printed 2·abs(k)/N estimate is proved internally, not quoted |
| SO.08 | thm:E | Γ̄ is sofic: its six generators lie in GL₄(ℤ) and the integral subgroup is residually finite through congruence quotients | `ExplicitIntegralLinearModel.gammaBar_isSofic`; `ExplicitIntegralLinearModel.gammaBar_residuallyFinite` | EXACT | EXACT | literal | unconditional | - | NO | - |
| SO.09 | thm:E | E → W is surjective: the image contains V, the root lamp, and hence every lamp by transitivity | `LiteralNonMFLinearWitness.witnessGroup_finitelyGenerated` | EXACT | EXACT | literal | unconditional | - | NO | - |
| SO.10 | thm:E | w ↦ ζ and functoriality of the radical make ζ ∈ Rad_MF(W); hence W is not MF | `LiteralWitnessConsequences.witnessGroup_not_isOperatorMF` | EXACT | EXACT | literal | unconditional | - | NO | - |
| ES.01 | thm:Esofic | Theorem E: E itself is sofic, with no hypothesis and no literature input | `LiteralSoficAssembly.markedGroup_isSofic` | EXACT | EXACT | literal | unconditional | - | NO | the block-Clifford window tower over the telescope, then the cyclic truncation of the ℤ step; the module is in the root import closure as of this revision, so the badge is built |
| ES.02 | thm:Esofic | E is hyperlinear, since sofic groups are | `LiteralSoficAssembly.markedGroup_isHyperlinear` | EXACT | EXACT | literal | unconditional | - | NO | - |
| ES.03 | thm:Esofic | E is finitely presented, sofic, and not MF -- one explicit group with all three | `LiteralSoficAssembly.markedGroup_finitelyPresented_sofic_nonMF` | EXACT | EXACT | literal | unconditional | - | NO | premise-free composition of ES.01 with `LiteralSoficEndpoint`, whose packaged endpoints take soficity as their single premise |
| ES.04 | thm:Esofic | the same, with hyperlinear in place of sofic | `LiteralSoficAssembly.markedGroup_finitelyPresented_hyperlinear_nonMF` | EXACT | EXACT | literal | unconditional | - | NO | - |
| ES.05 | thm:Esofic | E is sofic and not LEF, in particular not residually finite | `LiteralSoficAssembly.markedGroup_sofic_not_isLEF_unconditional` | EXACT | EXACT | literal | unconditional | - | NO | the printed reason is that an LEF group is a marked limit of finite groups and `thm:markedclosed` closes the MF locus; the Lean route is `markedGroup_not_isLEF` |
| ES.06 | thm:Esofic | the kernel of the stable-letter exponent is locally residually finite, hence LEF, hence sofic | `LiteralSoficAssembly.markedGroup_isSofic` | UNDER-SPECIFIED | UNDER-SPECIFIED | literal | unconditional | - | NO | the printed sentence is a route, not a determinate step: the formal proof runs the block-Clifford window tower rather than a literal locally-residually-finite argument, so there is nothing here to bind step for step |
| SO.11 | p:E-extension | W fits in 1 → ClLamp(X) → W → V → 1 with MF kernel and quotient but non-MF total | `LiteralWitnessConsequences.literalWitness_locallyFiniteKernel_nonMF` | EXACT | EXACT | literal | unconditional | - | NO | - |
| SO.12 | p:E-extension | the lamp kernel is locally finite, LEF, sofic and MF | `CliffordLamp.isLocallyFiniteGroup_cliffordLamp`; `CliffordLamp.isLEF_cliffordLamp`; `CliffordLamp.isSofic_cliffordLamp`; `CliffordLamp.isOperatorMF_cliffordLamp` | EXACT | EXACT | literal | unconditional | - | NO | - |
| SO.13 | p:E-extension | V is the subgroup of GL₄(ℚ) generated by Γ̄ and D, with telescope levels D^{-n}Γ̄D^n and determinant giving the ℤ-coordinate; it is residually finite via odd-modulus congruence reductions, hence MF | `WitnessVertical.vertical_isOperatorMF` | EXACT | EXACT | literal | unconditional | Malcev | NO | Mal'cev is cited only for comparison; the reduction is proved internally |
| SO.14 | p:E-zext | W → ℤ has kernel ClLamp(X) ⋊ T, which is LEF hence MF; so W is an extension of an LEF group by ℤ and is not MF | `LiteralLEFExtension.literalWitness_LEFKernel_integerExtension_nonMF` | EXACT | EXACT | literal | unconditional | - | NO | - |
| SO.14b | p:E-zext | soficity is preserved by an extension with amenable quotient | `SoficByAmenablePermanence.manuscriptSoficOfSoficKerOfAmenableQuotient` | EXACT | EXACT | literal | unconditional | - | NO | the Elek--Szabo permanence the sentence cites, now in-repo rather than a citation |
| SO.15 | p:E-zext | soficity is preserved by every extension with amenable quotient | - | MISSING | MISSING | - | literature-input | ElekSzabo | NO | only the ℤ case is formalized (SO.07) |
| SO.16 | p:E-exact | C*_red(W) is exact, has a faithful tracial state, is stably finite and is not MF | `LiteralWitnessConsequences.literalWitness_reducedGroupCStar_stablyFinite_nonMF` | MISMATCH | MISSING | literal | literature-input | GHW, KWPermanence, KWExact | NO | everything except exactness is formal; the TeX says the library has no definition of exact C*-algebra |
| SO.17 | p:E-simple | there is a countable simple sofic group equal to its own MF radical | - | MISSING | MISSING | - | literature-input | ElekSzaboHyper | NO | the embedding of a countable sofic group into a simple sofic one is quoted |
| SO.18 | p:E-simple | proof: embed W, use functoriality, and note that a normal radical containing a nontrivial element of a simple group is everything | `map_actualCoronaMFResidual_le` | MISMATCH | MISSING | literal | literature-input | ElekSzaboHyper | NO | functoriality is formal; the simple sofic envelope is not |
| ML.01 | p:markedlimit-intro | at every fixed number of marked generators, MF is closed under limits of marked groups and its failure always has a finite certificate | `MarkedGroupSpace.isClosed_operatorMFLocus` | EXACT | EXACT | literal | unconditional | - | NO | - |
| ML.02 | thm:markedclosed | (1) the marked groups with MF quotient form a closed set | `MarkedGroupSpace.isClosed_operatorMFLocus` | EXACT | EXACT | literal | unconditional | - | NO | - |
| ML.03 | thm:markedclosed | (2) the non-MF marked groups form an open set | `MarkedGroupSpace.isOpen_compl_operatorMFLocus` | EXACT | EXACT | literal | unconditional | - | NO | - |
| ML.04 | thm:markedclosed | (3) every non-MF k-marked group admits a finite-radius certificate | `MarkedGroupSpace.exists_wordBall_cylinder_subset_compl_operatorMFLocus` | EXACT | EXACT | literal | unconditional | - | NO | - |
| ML.05 | thm:markedclosed | proof: a failure of MF is a failure of normalized local approximation, witnessed on one finite subset | `MarkedGroupSpace.operatorMFLocus_eq_normApproximableOneLocus` | EXACT | EXACT | literal | unconditional | - | NO | - |
| ML.06 | thm:markedclosed | proof: expressing the finitely many multiplications and inequalities as relation constraints gives a basic clopen neighbourhood that fails MF; a reduced-word ball gives the radius form | `MarkedGroupSpace.exists_cylinder_subset_compl_operatorMFLocus`; `MarkedGroupSpace.exists_subset_wordBall` | EXACT | EXACT | literal | unconditional | - | NO | - |
| HO.01 | p:horn-intro | Theorem A reads as one finite quasi-identity valid in all MF groups | `LiteralUniversalHorn.manuscriptLiteralUniversalHorn` | EXACT | EXACT | literal | unconditional | - | NO | - |
| HO.02 | prop:horn | every MF group satisfies the displayed universal Horn sentence, while the canonical tuple of E satisfies R and has w ≠ 1 | `LiteralUniversalHorn.manuscriptLiteralUniversalHorn` | EXACT | EXACT | literal | unconditional | - | NO | universe-polymorphic in the target group |
| HO.03 | prop:horn | proof: a tuple satisfying the relators induces E → G sending the marked word to w(x₁,…,x₈); functoriality of the radical kills it | `LiteralUniversalHorn.isOperatorMF_satisfies_literalQuasiIdentity` | EXACT | EXACT | literal | unconditional | - | NO | - |
| HO.04 | cor:cylinder | the marked groups satisfying R with w ≠ 1 form a nonempty clopen set of non-MF groups | `LiteralMarkedCylinder.literal_nonempty_clopen_nonMF_cylinder` | EXACT | EXACT | literal | unconditional | - | NO | - |
| HO.05 | cor:cylinder | proof: both conditions constrain finitely many values, the set contains E, and Proposition 11.36 excludes every MF point | `LiteralMarkedCylinder.literalCylinder_isClopen`; `LiteralMarkedCylinder.literalCylinder_nonempty`; `LiteralMarkedCylinder.literalCylinder_subset_nonMF` | EXACT | EXACT | literal | unconditional | - | NO | - |
| UN.01 | p:undec-markov | MF is a Markov property: the trivial group is MF and the f.p. group E embeds in no MF group | `MarkovMFConsequences.operatorMF_subgroup_hereditary`; `MarkovMFConsequences.exists_finitelyPresented_nonOperatorMF` | EXACT | EXACT | literal | unconditional | - | NO | - |
| UN.02 | cor:undecidable | given a computable reduction from the halting problem, no algorithm decides MF from a finite presentation | `MarkovMFConsequences.presentationCodes_recognition_undecidable_of_haltingReduction` | EXACT | EXACT | literal | unconditional | - | NO | the printed corollary quantifies the reduction and nothing else; undecidability of the halting problem is proved in the development, so no literature premise remains |
| UN.03 | cor:undecidable | given the same reduction, the set of presentation codes of non-MF groups is not recursively enumerable | `MarkovMFConsequences.presentationCodes_negative_side_not_re_of_haltingReduction` | EXACT | EXACT | literal | unconditional | - | NO | same shape as UN.02; the non-enumerable complement of the halting problem is proved rather than cited |
| UN.04 | p:undec-adianrabin | the Adian–Rabin construction supplies a computable map from word-problem instances to presentations, trivial when w = 1 and containing E when w ≠ 1 | - | MISSING | MISSING | - | literature-input | Rabin58 | NO | the TeX names Novikov–Boone and Adian–Rabin as the inputs the corollary quantifies |
| UN.05 | p:undec-adianrabin | the computability-theoretic pullback: from any computable reduction, undecidability and failure of r.e. on the negative side follow formally | `MarkovMFConsequences.recognition_undecidable`; `MarkovMFConsequences.negative_side_not_re` | EXACT | EXACT | literal | unconditional | - | NO | the pullback itself is unconditional |
| UN.05b | p:undec-adianrabin | the same pullback in the manuscript's general form: a reduction from any undecidable source problem makes MF recognition undecidable | `MarkovMFConsequences.operatorMF_recognition_undecidable` | EXACT | EXACT | literal | unconditional | - | NO | the general form is still badged in the prose beside the halting-problem specialization the corollary now prints |
| UN.06 | p:mult-products | E × ℤ^k for k ≥ 0 are f.p., pairwise nonisomorphic, and non-MF | `ProductMultiplicity.manuscriptInfiniteMultiplicity` | MISMATCH | MISMATCH | literal | unconditional | - | NO | the TeX separates by torsion-free rank of the abelianization; Lean counts homomorphisms into ℤ/2, a deliberate difference the TeX records |
| UN.07 | p:mult-continuum | pairing E with a continuum of pairwise nonisomorphic f.g. groups yields 2^ℵ₀ pairwise nonisomorphic f.g. non-MF groups | `ContinuumMultiplicity.manuscriptContinuumMultiplicity` | MISSING | MISSING | - | literature-input | Neumann37 | NO | Neumann's family is a quantified hypothesis, as the TeX states |
| UN.07b | p:mult-continuum | the input family itself: a continuum of pairwise nonisomorphic finitely generated groups, constructed rather than quoted | `NeumannContinuum.manuscriptContinuumMultiplicityUnconditional` | EXACT | EXACT | literal | unconditional | - | NO | removes the Neumann literature input from UN.07; the family is not Neumann's (a lamplighter over free-group coset spaces, not a subdirect product of alternating groups) and is finitely generated, not two-generator, which is all the deduction uses -- the TeX now says so |
| UN.08 | p:mult-continuum | the counting step: each N embeds in X as a f.g. subgroup, a countable group has countably many f.g. subgroups, and a map with countable fibres from a continuum-sized family has continuum-sized image | `ContinuumMultiplicity.exists_continuum_pairwise_nonisomorphic` | EXACT | MISMATCH | literal | conditional-data | - | NO | the manuscript's own step on top of the hypothesis is formal |
| LI.01 | p:limits-opnorm | HS-controlled multiplication does not make the adjoint operators operator-norm close, and both transport proofs need exactly that control | `KazhdanCompressorCorner.displacement_vanishing` | MISMATCH | MISSING | literal | unconditional | - | NO | the necessity claim is not formalized; only the positive use of operator-norm control is |
| LI.01b | p:limits-adjointgap | the failure is exact and dimension-free: against ‖Ad U − Ad V‖ ≤ 2‖U − V‖ there are unitaries of arbitrarily small normalized HS distance whose adjoints stay 2 apart in operator norm | `HilbertSchmidtAdjointGap.exists_hsClose_adjointFar`; `HilbertSchmidtAdjointGap.two_le_l2_opNorm_conjDouble_sub`; `HilbertSchmidtAdjointGap.hsNormSq_one_sub_signDiagonal` | EXACT | EXACT | literal | unconditional | - | NO | added during this audit; the sign-diagonal witness realizes the constant 2 |
| LI.02 | p:limits-dilution | padding with an identity block preserves every operator-norm quantity while collapsing normalized HS distances below any bound | `NormModel.exists_hs_collapse`; `l2_opNorm_cornerPad` | EXACT | EXACT | literal | unconditional | - | NO | - |
| LI.03 | p:limits-dilution | hence HS invisibility alone can never prove a group non-MF; an obstruction must carry its own scale | `NormModel.exists_hs_collapse` | EXACT | EXACT | literal | unconditional | - | NO | - |
| LI.04 | p:limits-dilution | macroscopic relative rank is not required: padding leaves the Reynolds corner untouched while d_n grows, so r_n/d_n may tend to zero | `FiniteNormalAverageCorner.exists_corner_with_finite_sum_vanishing` | MISMATCH | MISSING | literal | unconditional | - | NO | the corner is intrinsically renormalized in Lean, but no declaration states this independence claim |
| LI.05 | p:limits-alekseev | this is a limitation of the method, not a tracial nonapproximation theorem for E; Alekseev–Thom's Open Problem 6.2 is separate | - | MISSING | MISSING | - | literature-input | AlekseevThom | NO | commentary |
| LI.06 | p:limits-trace | finite dimensionality cannot be traded for stable finiteness plus faithful traces: constant coordinates A_n = C*_red(E) refute any such generalization | `LiteralNonMFEndpoint.manuscriptTheoremD` | MISMATCH | MISSING | literal | unconditional | - | NO | the refutation argument (left regular embedding into the constant corona and the surviving defect) is not formalized |
| LI.06b | p:limits-nogo | constant coordinates A_n = C*_red(E) refute the faithfully-traced generalization: the left regular representation embeds E injectively, c centralizes the base, and the commutator of tct⁻¹ with the base is the nontrivial defect | `FaithfullyTracedCoordinates.manuscriptFaithfullyTracedCoordinateNoGo`; `FaithfullyTracedCoordinates.ConstantReduced.reducedLeftRegular_injective`; `FaithfullyTracedCoordinates.literal_compressionDefect_ne_one` | EXACT | EXACT | literal | unconditional | - | NO | added during this audit; replaces the informal version audited at LI.06 |
| LI.06c | p:limits-nogo | the refuted statement is the transport theorem of Section 3 with matrix coordinates replaced by finite faithfully traced C*-coordinates and the normalized HS norm by the trace 2-norm, every other hypothesis copied verbatim | `FaithfullyTracedCoordinates.FaithfullyTracedCoordinateTransport`; `FaithfullyTracedCoordinates.traceTwoNorm` | EXACT | EXACT | literal | unconditional | - | NO | the refuted proposition is spelled out as a Lean definition, then negated |
| LI.07 | p:questions-torsion | every finite subgroup of a torsion-free group is trivial | `finiteSubgroup_eq_bot_of_isMulTorsionFree` | EXACT | EXACT | literal | unconditional | - | NO | universe-polymorphic |
| LI.08 | p:questions-torsion | by Theorem 4.9 a normal (T) subgroup of the defect obstructs without torsion; what remains is group-theoretic | `ManuscriptExactWrappers.manuscriptNormalKazhdanObstruction` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0 |
| LI.09 | p:q1 | Question 1: what is Rad_MF(E)?  It properly contains {1,w} by Theorem 11.29 | `LiteralSignFreeQuotient.signFree_collapse` | EXACT | EXACT | literal | open | - | NO | the question was rewritten during this audit; the containment is now a theorem |
| LI.10 | p:q1 | applying Corollary 11.30 to E/⟨w⟩ with the witness of that proof reduces the computation to the quotient by the resulting collapse defect D | `ManuscriptExactWrappers.manuscriptCollapseRadicalReduction` | MISMATCH | EXACT | literal | unconditional | - | NO | univ0; the reduction is stated generally, not instantiated at E/⟨w⟩ |
| LI.11 | p:q1 | and Corollary 11.8 identifies the radical with the preimage of D as soon as that quotient is MF | `ManuscriptExactWrappers.manuscriptExactRadicalFromCandidateQuotient` | EXACT | EXACT | literal | unconditional | - | NO | - |
| LI.12 | p:q1 | whether that quotient is MF is open; a detecting model must survive both collapses and by Theorem B factors through no finite quotient and no exact finite-dimensional representation | `ManuscriptExactWrappers.manuscriptTheoremB` | EXACT | EXACT | literal | open | - | NO | - |
| LI.13 | p:q2 | Question 2: given routing data, there is a two-generated, f.p., torsion-free (T) group equal to its own MF radical | `FullMFRadicalEndpoint.exists_twoGenerated_finitelyPresented_torsionFree_kazhdan_fullMFRadical` | MISSING | MISSING | - | conditional-data | - | NO | hypothesis `Nonempty (DefectRoutingData D)`; the TeX labels it conditional |
| LI.14 | p:q2 | and every nontrivial quotient of such a group also fails to be MF | `FullMFRadicalEndpoint.exists_group_with_every_nontrivial_quotient_not_isCDEOperatorMF` | MISSING | MISSING | - | conditional-data | - | NO | same hypothesis |
| LI.15 | p:q2 | constructing the routing data uses Hull–Osin small-cancellation theory and remains open | - | MISSING | MISSING | - | open | FFF | NO | - |
| LI.16 | p:q3 | Question 3: whether E is sofic or hyperlinear is not decided by the results above | - | MISSING | MISSING | - | open | - | NO | - |
| LI.17 | p:q4 | Question 4: a faithful corona embedding need not make any coordinate trace faithful, so MF does not immediately supply a hyperlinear model | `NormModel.exists_hs_collapse` | EXACT | EXACT | literal | open | - | NO | the trace-blindness half is formal; the question is open |
| AE.01 | p:appA-localmodel | definition of an operator-norm local model for (G, F, δ, ε) | `NormModel` | EXACT | EXACT | literal | unconditional | - | NO | multiplicativity ≤ ε on F and separation ≥ δ on F, exactly as printed |
| AE.02 | app:equivalences | Lemma 2.3 identifies the unitary-sequence quotient with the unitary group of the C*-quotient | `normMatrixCoronaUnitaryEquiv` | EXACT | EXACT | literal | unconditional | - | NO | - |
| AE.03 | app:equivalences | replacing an arbitrary finite coordinate set by a standard one of the same cardinality conjugates by a permutation unitary | `actualCoronaNaturalizeEquiv` | EXACT | EXACT | literal | unconditional | - | NO | - |
| AE.04 | app:equivalences | dimension normalization: pad by earlier identity blocks to get strictly increasing D_n, preserving products, defects and pairwise distances | `isOperatorMFIncreasing_iff` | EXACT | EXACT | literal | unconditional | - | NO | - |
| AE.05 | app:equivalences | for injective ρ and g ≠ h in F, some δ_{g,h} > 0 is attained at arbitrarily large coordinates | `OperatorMFLocalNormalization.frequently_pair_separated` | EXACT | EXACT | literal | unconditional | - | NO | - |
| AE.06 | app:equivalences | choose N with 8 < N δ²; some tensor power of exponent p ≤ N separates the pair by more than 1 | `OperatorNormAmplification.exists_tensorPower_pair_far` | EXACT | EXACT | literal | unconditional | - | NO | the printed constant 8 appears verbatim in `exists_pairStage` |
| AE.07 | app:equivalences | choose a coordinate with the separation and every defect ≤ ε/N; the telescoping identity bounds each new defect by pε/N ≤ ε | `OperatorMFLocalNormalization.PairStage`; `OperatorMFLocalNormalization.PairStage.block_multiplicative` | EXACT | EXACT | literal | unconditional | - | NO | - |
| AE.08 | app:equivalences | take the block sum of the finitely many pair-specific models; block operator norms are maxima | `OperatorMFLocalNormalization.isNormApproximable_one` | EXACT | EXACT | literal | unconditional | - | NO | - |
| AE.09 | app:equivalences | conversely, local models with separation 1 for all F and ε make the group weakly MF | `OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one` | EXACT | EXACT | literal | unconditional | - | NO | - |
| AE.10 | app:equivalences | weak MF makes the norm-MF radical trivial, and the block-sum diagonalization of Prop 11.6(2) assembles a single faithful corona representation | `isCDEOperatorMF_iff_manuscriptCoronaMFResidual_eq_bot`; `manuscriptCoronaMFQuotient_isCDEOperatorMF` | EXACT | EXACT | literal | unconditional | - | NO | the printed routing through the universal quotient is what Lean does |
| FS.01 | app:finite-stage | property (T) provides a finite symmetric generating S ∋ 1 and κ ∈ (0,1] | `KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FS.02 | app:finite-stage | the adjoint model is that of the printed proof: conjugation on L²(M_{d_n}, tr_{d_n}), an operator-norm asymptotic representation | `OpAlmostRepresentation.adjoint`; `conjDouble` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FS.03 | app:finite-stage | H_n = Hermitian part of the S-average; θ = ½((1 − κ²/(4 \| S \| )) + 1) < 1; P_n = spectral projection above θ | `KazhdanCornerMatrices.hermitianAverage`; `KazhdanCompressorCorner.cornerProjection`; `KazhdanAsymptoticCommutant.transport` | EXACT | EXACT | literal | unconditional | - | NO | `transport` sets `theta := ((1 - kappa^2/(4*S.card)) + 1)/2`, exactly the printed midpoint |
| FS.04 | app:finite-stage | (i) displacement: ‖(Ad U_n(ι(γ)) − 1)P_n‖ → 0 for every γ | `KazhdanCompressorCorner.displacement_vanishing` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FS.05 | app:finite-stage | the robust spectral gap: for 1 − κ²/(4 \| S \| ) < a and b < 1, eventually no eigenvalue of H_n lies in [a,b] | `WeakMFVectorGNS.hermitianAverage_eventually_no_intermediate_eigenvalues` | EXACT | EXACT | literal | unconditional | - | NO | proved, not granted; the TeX only asks that it be granted |
| FS.06 | app:finite-stage | consequently a unit η ∈ ran P_n has ⟨(1 − H_n)η,η⟩ ≤ δ, each generator moves η by ≤ √(2 \| S \| δ), and a word of length ℓ by ℓ√(2 \| S \| δ) plus accumulated defects | `KazhdanCompressorCorner.displacement_vanishing` | EXACT | EXACT | literal | unconditional | - | NO | the word-length propagation is inside `topSpectralDisplacement_vanishing_of_generates` |
| FS.07 | app:finite-stage | (ii) concentration: ‖(1 − P_n)η‖₂ ≤ (1 − θ)⁻¹‖(1 − H_n)η‖₂, applied to ξ_n | `KazhdanAsymptoticCommutant.capture_vanishing` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FS.08 | app:finite-stage | T_n = Ad U_n(s), Q_n = T_nP_nT_n*, a projection of the same rank as P_n | `KazhdanCompressorCorner.movedProjection`; `KazhdanCompressorCorner.movedProjection_rank` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FS.09 | app:finite-stage | the conjugation relation enters once: s⁻¹ pulls almost-fixedness under ι(Γ) ⊇ sι(Γ)s⁻¹ back to almost-fixedness under each ι(s') | `KazhdanCompressorCorner.conj_defect_vanishing`; `KazhdanCompressorCorner.one_sub_map_mul_rotated_vanishing` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FS.10 | app:finite-stage | hence ran P_n is almost contained in its conjugate: ‖(1 − Q_n)P_n‖ → 0 | `KazhdanCompressorCorner.one_sub_corner_mul_moved_vanishing` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FS.11 | app:finite-stage | the equal-rank reversal: for projections of equal finite rank, ‖(1−q)p‖ ≤ ε < 1 implies ‖(1−p)q‖ ≤ ε/√(1−ε²) | `KazhdanCornerMatrices.norm_one_sub_mul_flip` | EXACT | EXACT | literal | unconditional | - | NO | the printed inequality, verbatim |
| FS.12 | app:finite-stage | so ‖(1 − P_n)Q_n‖ → 0: a one-sided compression cannot enlarge the subspace | `KazhdanCompressorCorner.one_sub_moved_mul_corner_vanishing` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FS.13 | app:finite-stage | combining: fix γ and ε, let M bound ‖x_n‖ and q = min(1, ε/(40(M²+1))); the three estimates hold at tolerance q | `KazhdanAsymptoticCommutant.transport_of_leakage` | EXACT | EXACT | literal | unconditional | - | NO | the same q and the same 40(M²+1) as printed |
| FS.14 | app:finite-stage | decompose T_nξ_n along P_n and Q_n into three terms | `MarkedCompressionVectorChain.transported_displacement_le` | EXACT | EXACT | literal | unconditional | - | NO | the `hdecomp` block |
| FS.15 | app:finite-stage | ‖(1 − Q_n)T_nξ_n‖₂ = ‖(1 − P_n)ξ_n‖₂ ≤ q^{1/2} by unitary invariance | `MarkedCompressionVectorChain.vecMass_one_sub_conjugate` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FS.16 | app:finite-stage | the middle term is ≤ qM and the displacement moves the first by ≤ qM | `MarkedCompressionVectorChain.transported_displacement_le` | EXACT | EXACT | literal | unconditional | - | NO | - |
| FS.17 | app:finite-stage | applying A_n − 1 gives ‖(A_n−1)T_nξ_n‖₂² ≤ (qM + 2qM + 2q^{1/2})² ≤ 18q²M² + 16q ≤ ε | `KazhdanAsymptoticCommutant.transport_of_leakage` | EXACT | EXACT | literal | unconditional | - | NO | the Lean bound is `(2q² + 16q²)·mass + 16q·card`, which is the same 18q²M² + 16q after normalization |
| FS.18 | app:finite-stage | T_nξ_n is the vector of U_n(s)x_nU_n(s)*, proving the convergence with an explicit rate in κ, \| S \| , M and the defects | `KazhdanAsymptoticCommutant.transport` | EXACT | EXACT | literal | unconditional | - | NO | - |
| MC.01 | p:appC-construction | the universe-relative maximal group C*-algebra: the closed *-subalgebra generated by the diagonal copy of H in the bounded product of all its nontrivial unitary representations on 𝔘-small unital C*-algebras | `MaximalGroupCStar` | EXACT | EXACT | literal | unconditional | - | NO | - |
| MC.02 | prop:maximal-cstar | h ↦ u_h is injective, and every ρ : H → U(B) extends uniquely to a unital *-homomorphism | `manuscriptUniverseRelativeMaximalGroupCStar` | EXACT | EXACT | literal | unconditional | - | NO | universe-polymorphic in H at the stated universe |
| MC.03 | p:appC-universal | for a nontrivial target, projection to its coordinate gives the extension; density gives uniqueness; the left-regular coordinate proves injectivity | `maximalGroupCStar_existsUnique_lift`; `maximalGroupCStarUnitaryHom_injective` | EXACT | EXACT | literal | unconditional | - | NO | - |
| MC.04 | prop:proper-isometry | a projection p and unitary u with upu* absorbing p on both sides and upu* ≠ p give a non-unitary isometry | `ProperProjectionCompression.isometry_not_isUnit` | EXACT | EXACT | literal | unconditional | - | NO | the structure fields are exactly the printed hypotheses |
| MC.05 | prop:proper-isometry | consequently A is not stably finite | `ProperProjectionCompression.not_isStablyFiniteRing` | EXACT | EXACT | literal | unconditional | - | NO | - |
| MC.06 | prop:proper-isometry | and carries no faithful tracial state | `ProperProjectionCompression.no_faithfulTracialState` | EXACT | EXACT | literal | unconditional | - | NO | - |
| MC.06b | p:appC-separate | the maximal and reduced algebras separate already at the level of finiteness, and the algebraic mechanism is machine-checked in full | `ProperProjectionCompression.isometry_not_isUnit`; `ProperProjectionCompression.not_isStablyFiniteRing` | EXACT | EXACT | literal | unconditional | - | NO | - |
| MC.07 | rem:maxinfinite | for a group with strict Kazhdan compression the Kazhdan projection exists in the maximal algebra and conjugation by u_t dominates it | `MaximalCStarProperCompression.StrictKazhdanCompression.proj`; `MaximalCStarProperCompression.StrictKazhdanCompression.proj_mul_conjugate` | MISMATCH | MISMATCH | literal | conditional-data | - | NO | stated over a `StrictKazhdanCompression` datum; the TeX badge that named only `QuasiRegularWitness.baseVector_apply_base`, a trivial fragment, is now joined by the paragraph-level certificate of MC.08b |
| MC.08 | rem:maxinfinite | the domination is strict: at the quasi-regular coordinate ℓ²(G/tΓt⁻¹) the point mass at the base coset is fixed by the compressed subgroup and moved by everything outside it | `QuasiRegularWitness.exists_baseVector_witness`; `QuasiRegularWitness.baseVector_apply_base` | EXACT | EXACT | literal | unconditional | - | NO | the badge certifies only the evaluation; the separation is `exists_baseVector_witness` |
| MC.08b | rem:maxinfinite | the whole remark at once: projection, strict domination, failure of Dedekind and stable finiteness, no faithful trace, neither RFD nor MF, and the contrast with the reduced algebra | `MaximalCStarParagraphEndpoint.manuscriptMaximalCStarStrictCompressionRemark` | EXACT | EXACT | literal | unconditional | - | NO | added to the TeX 2026-08-16 in answer to MC.07's note: the paragraph now carries a certificate for its load-bearing conclusions, not only for the quasi-regular evaluation.  Conjuncts follow the printed sentence order |
| MC.09 | rem:maxinfinite | hence the maximal algebra of such a group is not stably finite, carries no faithful trace, and is neither RFD nor MF — with the base of E as the running example | `ChosenMaximalCStarInfinite.chosen_maximalCStar_not_isStablyFiniteRing`; `ChosenMaximalCStarInfinite.chosen_maximalCStar_no_faithfulTracialState` | MISMATCH | MISMATCH | substituted | unconditional | - | NO | instantiated for the *Chosen* presentation, not for the literal eight-generator E of Definition 7.1; and no RFD clause is stated |
<!-- END-LEDGER-STEPS -->

## What would close this ledger

In dependency order, cheapest first.

1. **Universe scope (30 rows).**  Restate the `{H : Type}` obstruction theorems
   universe-polymorphically, or add one transfer lemma "a countable group is
   isomorphic to a group in `Type 0`, and each of these predicates is
   isomorphism-invariant" and route the printed statements through it.  Nothing
   mathematical is at stake; 30 `MISMATCH` statements become `EXACT`.
2. **Small printed steps with no declaration (about 15 rows).**  The trace bound
   `|tr_r x| ≤ ‖x‖`; the explicit polar-correction estimate of the lifting lemma; the
   invariant-size principle instantiated at cardinality of subgroups of a finite group;
   the `A₄ < S₄` commutant example; the six-relator form of `E_BS`; the identification
   of the transport theorem with the scaled form at `w_n = d_n`; the dilution-invariance
   claim about relative corner rank.
3. **The printed ultraproduct proof of the transport theorem (30 rows, `KT.00`–`KT.29`;
   16 `MISSING`, 10 `MISMATCH`).**  Either formalize the Hilbert-space and norm
   ultraproducts, faithfulness of the action, `C*`-finiteness, and the Kazhdan
   projection — the printed road — or record that the manuscript's Section 3 proof is
   documentation for an argument the development does not contain and that the
   finite-stage appendix is the formalized one.  This is the single largest block of
   `MISSING` rows and the only one that touches the main theorem's printed reasoning.
4. **Literature used in deductions.**  Exactness of `C*_red(W)`; amenable ⇒ MF; the
   simple sofic envelope; Adian–Rabin; Neumann's continuum family; nonamenability of
   infinite Kazhdan groups; nonnuclearity of `C*_red` of a nonamenable group; the
   amenable-quotient case of Elek–Szabó beyond `ℤ`.  Each needs a Lean proof, or the
   corresponding manuscript claim must be understood as unformalized.
5. **The conditional endpoints.**  Discharge `Nonempty (DefectRoutingData D)`, and
   formalize Neumann's family.
6. **Remark C.4.**  Instantiate `StrictKazhdanCompression` at the literal `E` rather than
   at the Chosen presentation, and add the RFD clause; then the remark's badge can point
   at a declaration that carries its content instead of at
   `QuasiRegularWitness.baseVector_apply_base`.

## Running the gate

```
python3 scripts/check_non_mf_proof_ledger.py             # against the working tree
python3 scripts/check_non_mf_proof_ledger.py --self-test
python3 scripts/check_non_mf_proof_ledger.py --repin-digests   # deliberate re-anchor
```

Failures come in two buckets, because on a shared checkout they mean different things.

* **broken** — a `\label` is gone, a cited declaration no longer exists, or a row
  violates an invariant.  Something is actually wrong; fix it.
* **drifted** — a printed statement was reworded, or a prose probe no longer occurs
  exactly once.  Expected while peers edit the manuscript.  Re-read the rows on the
  named anchor, decide whether the *claim* changed or only its wording, and then
  re-pin: `--repin-digests` rewrites `env` digests and logs every one it moves.
  Prose probes are never auto-repaired — a relocated paragraph might be a changed
  claim, so it keeps failing until a human looks.

Re-pinning without re-reading defeats the ledger.  The digest is not a checksum for
its own sake; it is the trigger that forces a claim to be looked at again.

**No line numbers, by design.**  A line-number column would be stale within minutes
on this checkout and would invite readers to trust it.  The anchor *is* the locator:
`grep -n 'thm:signfree' non_mf_groups_exist.tex` for a label, or `grep -nF` with the
probe text for a prose anchor, gives the current position in one step.

