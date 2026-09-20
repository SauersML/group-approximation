# Liu's internality argument inside the Cairn program

Integrated and updated on 2026-09-20. The nonhyperlinear root now has closed written-proof derivations. This is the reading map and trust ledger for the canonical subgraph, not a Lean build certificate or an external human referee report.

## Attribution

The central analytic results are **Jihao Liu's**, in
[*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf)
(2026-09-20): Proposition 3.1, Theorems 3.2, 4.3, 5.1 and 6.7, and the
auxiliary lemmas identified below. The per-model normalization theorem is Liu
7.4; **Andreas Thom** has priority for the conditional universal-internality-to-
normalization argument and double construction. The group pair and lamp
construction are due to **Gábor Kun and Andreas Thom**, building on the earlier
OpenAI compression mechanism, as Liu's paper explains.

The Leavitt and other Cairn consequences below are applications of
Liu's analytic theorem through previously recorded Cairn arguments. They are
not presented as theorems Liu states in his paper, nor as independent discoveries
of his analytic results. Independently checking or restating a proof does not
transfer its authorship. Each consuming canonical node carries this attribution.

## Bottom line

The paper addresses a bottleneck that Cairn had explicitly isolated: extracting
finite-dimensional algebra structure from Kazhdan commutants in tracial matrix
ultraproducts. The group-level lamp route was already present. Several analytic
pieces were also present, including low-energy cuts, soft overlapping selection,
and transporting expansion tests back into their tested corner.

The additional mechanism is a coupled construction with a vanishing
global error budget: physical equivariant rounding; monotone-resolvent seed
assembly and range-leakage control; unequal-rank matching; and exhaustion through
uniform conditional expectations. The complete combined construction was not
located in the earlier sources inspected. This is neither an exhaustive priority
claim nor evidence that Liu accessed the repository.

The graph separates mathematical implications from acceptance of their analytic inputs. The central claim
[`kazhdan-commutants-are-internal`](../kazhdan-commutants-are-internal.md)
is now **ESTABLISHED by a checked written chain**, and the existing nonhyperlinear root derives from it. The four exact analytic leaves have full proof reconstructions, Theorem 5.1 assembly has an independent cross-review, and matching/exhaustion have full proof routes. No route simply declares the whole paper proved. Standard finite-von-Neumann-algebra imports remain identified; no fresh Lean check or external human review is claimed.

The general compression conclusion is obtained through **Thom's** checked conditional theorem. Liu's stronger one-model theorem, assuming only internality of the subgroup commutant, remains separately OPEN and is not needed for the completed routes. This prevents acceptance of an unreviewed stronger statement merely because a consequence is proved.

The [integrated consequences figure](../../output/figures/cairn-liu-integrated-consequences.svg)
is also available as a [PNG](../../output/figures/cairn-liu-integrated-consequences.png).
It condenses canonical routes and labels their extra inputs. The proof ledger distinguishes written acceptance, retained literature imports, and genuinely open statements.

## The analytic chain

All matrix traces are normalized; the ultrafilter and original dimensions are
fixed. A quotient gap means the conjugation average has a positive gap off its
fixed space in the quotient, not that its coordinate lifts are genuine
representations.

| Interface | What is actually supplied | Review boundary |
|---|---|---|
| [Coordinate expectation lift](../quotient-gap-expectations-have-coordinate-lifts.md) | One model-dependent averaging schedule works on every bounded sequence; equality of expectations is a uniform infinity-to-2 norm statement | A full written witness/diagonal proof is supplied and separately checked; not a universal schedule across all models |
| [Relative repair](../quotient-gap-gives-uniform-relative-projection-repair.md) | One large corner and relative error sequence work for every eligible projection, however small its rank | Liu 3.2; full written reconstruction accepted |
| [In-place rounding](../low-energy-povms-round-equivariantly-in-place.md) | Orthogonal partition in the original dimension; output energy vanishes even at fixed purity deficit | Liu 4.3; full written reconstruction with Houdayer–Vaes and Ioana imports |
| [Resolvent assembly](../resolvent-assembly-controls-covariance-and-leakage.md) | Summed covariance and actual range-leakage estimates without a factor counting the outcomes | Liu 5.2-5.3; full written reconstruction accepted |
| [Defect pruning](../defective-block-expansion-prunes-to-doubled-gaps.md) | Summable defects yield scalar gaps after pruning and doubling nearby generators | Liu 5.4; full written reconstruction accepted |
| [Large expanding blocks](../quotient-gap-gives-large-scalar-expanding-blocks.md) | For each fixed discarded-trace tolerance, a positive gap on retained physical blocks | Assembly independently cross-reviewed; all four inputs accepted |
| [Matching](../scalar-expanding-kazhdan-blocks-give-internality.md) | Unequal approximate blocks are aligned into coherent multiplicity algebras, including off-diagonal intertwiners | Liu 6.4-6.5; full written proof of the supplied-block implication |
| [Exhaustion](../internal-corners-exhaust-kazhdan-commutants.md) | Nearly full internal corners plus one uniform expectation lift give full internality | Liu 6.6; full written proof; no nested corners or uniform gap required |

The principal AND-route is
[`kazhdan-internality-from-blocks-and-exhaustion`](../kazhdan-internality-from-blocks-and-exhaustion.md).
These are shared interfaces, not a second independent collection of isolated
Liu-summary nodes. The stronger existing
`hs-one-level-expander-block-decomposition` is deliberately NOT declared a
consequence: it has different original-generator and gap quantifiers.

## Why the new error budget matters

The September 8
[corner-transport artifact](quantum-corner-expansion-transport-2026-09-08.md)
already returns a test q to range(pq), preserves its rank bound, and charges its
escape from p as leakage. It explicitly identifies the unresolved ratio of
seed boundary to expansion threshold. Making both small at the same rate does
not make their ratio small.

Liu's selection includes a leakage penalty from the outset. Positive resolvent
increments telescope; a determinant potential controls overlap; physical
orthogonalization retains vanishing total energy. The constructed partial
isometries return all small physical tests to their original selection windows,
while the sum of their range leakage tends to zero. At fixed expansion threshold
the sum of transferred defects therefore tends to zero, and pruning becomes
affordable. This is a more specific advance than the idea of returning tests.

The original
[flexible-cut artifact](low-energy-povm-flexible-cuts-2026-09-08.md)
also matches several early ingredients closely. The
[soft-projection-cone artifact](soft-projection-cone-residual-energy-2026-09-08.md)
already considers overlapping positive sums, but leaves expansion-compatible
selection open. Neither is a proof of the complete internality conclusion.

## Completed downstream routes, with different requirements

### Compression and the Kun-Thom wreath

Universal internality through
[Thom's conditional no-drift theorem](../all-trace-normalization-via-thom-no-drift.md)
gives
[normalization for every tracial model](../kazhdan-compression-pairs-normalize-all-tracial-models.md).
This strengthens the existing `kt-centralizer-normalization-hs` interface and
feeds its recorded lamp proof. A root lamp commutes with the stabilizer; after
transport, normalization says a stabilizer element still commutes with it, while
the group action moves it to a distinct lamp. Thus every model identifies two
distinct lamps.

Thom has priority for the implication from universal centralizer internality to
normalization and the conditional nonhyperlinear construction. Liu credits that
priority. Liu's one-model normalization hypothesis and Thom's universal-input
formulation are not identical; the normalization audit explains both.

Strength matters downstream:

- All-trace normalization gives the existing **uniform finite-window compression
  inequality**. It rules out the arbitrary-trace CE normalization countermodel.
- The **single specified wreath's nonhyperlinearity** transfers to its double,
  centralizer HNN group, free binary coset wreath and relative-embeddability
  problem through the recorded equivalence, with the same parameters.
- The double's negative conclusion, together with its unique-trace theorem,
  rules out **MF of its reduced C-star algebra**. It does not rule out the
  existing abstract-group weak-MF model.
- A single-wreath theorem alone does NOT rule out every nonnormalizing actor
  model: such a model can instead produce a wreath over an intermediate
  stabilizer. The graph uses the stronger source for that refutation.

### Native heat and the binary Leavitt unit group

The original alternate route does not need Liu's normalization theorem. Internality for
every canonical Kazhdan model supplies finite-algebra rounding of its admissible
heat maps, uniformly on the operator unit ball of each coordinate sequence.
The existing Leavitt two-use argument then applies:

1. Global heat rounding and canonical component selection produce a model whose
   full external commutant is scalar.
2. Native-subgroup heat rounding and the compressor's central-height obstruction
   produce a nonzero trace-zero element in the center of that same commutant.

This is a contradiction. The
[Leavitt audit](liu-leavitt-consequences-audit-2026-09-20.md)
checks the sequential quantifiers, ICC trace concentration, squared-time
relation budget, reverse witness, central-height estimate and native generation
identity. The algebraic property-(T), simplicity and SOS inputs remain named
dependencies, not conclusions of Liu's paper.

**A shorter internality-only proof is now wired.** The [direct bounded-Poincare route](../leavitt-nonhyperlinear-from-internal-commutants.md) transfers the quotient inequality to uniform coordinate slack, then selects one physical-weight component with small gap, relation and trace defects. This obtains the scalar full commutant directly. Applying internality to the native subgroup gives the forward and reverse expectation defects directly, so the existing finite central-height contradiction applies. It removes heat, SOS certificates, time schedules, and the separate Proposition 3.1 interface from the downstream argument. [Independent cross-review](liu-leavitt-direct-internality-cross-review-2026-09-20.md) checked those replacements.

**A shorter group-side proof uses normalization.** The [native compressor route](../leavitt-nonhyperlinear-from-compressor-normalization.md) verifies H=<L,u,k_+,k_-> with three actual compressors. Normalization kills x_13(e), a nonidentity elementary matrix. It needs no scalar-commutant selection, character classification, simplicity, finite presentation, or central-height lemma. With simplicity added, every tracial-matrix-ultraproduct homomorphism of the F_2 unit group is trivial.

The [every-field extension](../binary-leavitt-units-over-any-field-are-not-hyperlinear.md) descends the required elementary factorizations to a finitely generated subring and uses k_+ to kill x_24(a). It reaches characteristic zero and uncountable fields through a countable finitely generated witness; it does not assert property (T), simplicity or finite presentation for each full unit group.

This route does NOT establish
`bistochastic-near-idempotents-round-dimension-free`: arbitrary channels need
not arise from fixed Kazhdan group generators and their SOS certificates. The
existing broad channel-rounding route remains a distinct sufficient route.

## Consequences and non-consequences

With the accepted shared analytic premise and the displayed structural inputs:

### Full-defect rings: the strongest algebraic extension

The [full-defect theorem](../full-defect-rings-have-full-hyperlinear-radical.md) says that for a countable nonzero unital associative ring R,

```
ts=1 and R(1-st)R=R
    ==> every homomorphism EL_n(R) -> a hyperlinear group is trivial,
        for every n>=2.
```

Fullness means a finite sum of two-sided multiples of the defect equals 1. It is essential: one-way invertibility alone is not the theorem. This is total collapse of every hyperlinear image, not merely absence of an injective model. The [complete algebraic audit](full-defect-ring-hyperlinear-radical-audit-2026-09-20.md) checks the universal Cohn ring, actual elementary factorizations of the compressors, ambient generation, killing and normal generation of the defect, and the independent rank-two transfer. The analytic input is Liu's internality followed by Thom's normalization; the old operator-norm obstruction alone does not imply it.

The construction first kills every image of EL_4 of the universal two-copy Cohn ring. Fullness supplies a map of that ring into R. A matrix-to-corner embedding transfers a killed normal generator into EL_2(R); two-coordinate copies then cover every higher elementary rank. No property (T) of EL_2(R) is assumed. An [independent algebraic cross-review](full-defect-hyperlinear-independent-crossreview-2026-09-20.md) rederives the compressor and rank-two calculations, including the conjugation-back step. The [rank-descent figure](../../output/figures/cairn-full-defect-rank-descent.png) isolates these steps.

For the actual binary F_2 Leavitt unit group, its identification with EL_4(R) gives [triviality of every tracial matrix-ultraproduct image](../binary-leavitt-tracial-ultraproduct-images-are-trivial.md). For arbitrary full-defect rings, the unit group is nonhyperlinear because it contains the obstruction; total collapse of the entire unit group is NOT claimed. The [countable-core route](../leavitt-all-fields-from-countable-full-defect-core.md) also gives nonhyperlinearity of binary Leavitt units over every field, including uncountable fields, without imposing Kazhdan or finite-presentation hypotheses on those larger unit groups.

### Exact radicals and stronger specified examples

The [exact radical theorem](../kun-thom-wreath-hyperlinear-radical-is-fibre-parity.md) applies to the whole binary Kun–Thom family. If N is the normal closure of the polynomial subgroup in the Laurent actor, then the hyperlinear radical, sofic radical and finite residual all equal the finite configurations with even parity on each fibre of G/Gamma -> G/N. The surviving quotient is residually finite. Thus the result describes every forced collapse, not only Liu's marked pair of lamps. [Proof and parameter audit](kun-thom-exact-hyperlinear-radical-2026-09-20.md).

Three profiles refer to different groups and must not be conflated:

| Specified witness | Combined conclusion | Additional input beyond Liu–Thom |
|---|---|---|
| Binary F_2 Leavitt unit group | Infinite simple, finitely presented, Kazhdan, integrally acyclic, nonhyperlinear; all tracial images trivial | Existing simplicity/property-(T)/rank identification; Huynh Viet Khanh Theorems 6.1 and 4.4 for finite presentation and acyclicity |
| Rank-six polynomial/Laurent double D_6 | Finitely presented, surjunctive, nonhyperlinear | Existing fold-surjunctivity theorem, Steinberg finite presentation, full stable rank-six K_2 kernel calculation |
| Ollivier–Wise cover doubled over the lifted Leavitt subgroup | Finitely presented, torsion-free, nonhyperlinear, integral cohomological dimension at most 3 | Ollivier–Wise cover, Leavitt finite presentation, Bass–Serre dimension argument |

The corresponding [Leavitt profile](../binary-leavitt-is-fp-simple-kazhdan-nonhyperlinear.md), [surjunctive double proof](fp-surjunctive-nonhyperlinear-double-audit-2026-09-20.md), and [torsion-free double proof](torsion-free-nonhyperlinear-rips-double-2026-09-20.md) keep these inputs explicit. The latter does not assert dimension exactly 3. Neither double profile establishes torsion-freeness or surjunctivity of the simple Leavitt group. Khanh's preprint inputs remain separate literature dependencies, not theorems proved by Liu.

The existing [four-generator, eighteen-relator presentation](../thompson-steinberg-presentation-of-leavitt-unit-group.md) gives a compact description of the Leavitt witness, with its written completeness review and dependencies retained. The three-generator/sixteen-relator and two-generator/fifteen-relator reductions are still unreviewed; no status promotion is made here. A compact presentation is not an explicit numerical Hilbert–Schmidt gap.

The new [recognition route](../hyperlinear-undecidable-from-leavitt-negative-seed.md) feeds the finitely presented Leavitt negative seed into the existing hereditary-approximation Rice theorem, proving undecidability of hyperlinearity on finite presentations. The stronger finite-presentation Pi^0_2-completeness target still needs the compiler's hyperlinear positive branch. Supplying a negative seed does not supply that branch.

### Parallel consequence and problem-development wave

The next wave audits the expanded comparison rather than treating it as
an already-proved list. Its completed written deductions are:

| Connection | Exact output | Extra premise or remaining boundary |
|---|---|---|
| [MF versus hyperlinear](mf-nonhyperlinear-double-separation-2026-09-20.md) | The same rank-six double is finitely presented, surjunctive, MF, and nonhyperlinear | Shulman's symmetric C-star amalgamation theorem plus the faithful RF-group-double bridge; no assertion that the canonical trace is an MF trace |
| [Linear-constraint games](liu-to-linear-games-and-marked-gap-2026-09-20.md) | A finite binary LCS has perfect commuting play and quantum-approximable value strictly below one | Paddock--Slofstra; the positive gap is existential, not numerical |
| [Concrete game input](../leavitt-central-sign-seed-for-lcs.md) | Six-generator, 25-relator group with nontrivial central involution invisible in every tracial matrix model | Reviewed four-generator Leavitt presentation; actual game equations and a rational gap remain open |
| [Surjunctivity and ring finiteness](liu-surjunctivity-permanence-audit-2026-09-20.md) | Liu's wreath and the rank-six double have stably finite group algebras over every field | Phung's ordinary-surjunctivity theorem; no Kaplansky or Gottschalk counterexample |
| [Intermediate stabilizers](../kt-intermediate-wreaths-missing-normal-core-not-hl.md) | Every stabilizer containing Gamma but missing its normal closure gives a nonhyperlinear binary coset wreath | Applies normalization to Gamma, not to the larger stabilizer; refutes the former intermediate-overgroup search target |

There is also a fixed word invisible in **every** MF model of the
nonhyperlinear double. This is stronger than padding one bad model:
universal MF-to-hyperlinear model selection and the two universal rate
profiles are refuted, while their conditional amplification lemmas
remain usable for special families. Exact finite-image vertex gluings
already kill a concrete Laurent difference, explaining why finite
quotient gluing cannot recover the double's canonical trace.

The [new-frontiers audit](liu-new-frontiers-2026-09-20.md) separates the
remaining tasks: the actual compiler's relative coset models, a genuine
rank-metric replacement for analytic internality, and new geometric
obstructions for hyperbolic or one-relator groups. No such existence
problem is marked solved. Cross-review also catches a seed-dependence
issue in older recognition notes: abstract equality of positive bridge
groups does not identify the effective Higman outputs. The strengthened
positive-branch hypothesis must retain the seed quantifier.

All nonhyperlinear uses credit Jihao Liu's internality and Andreas
Thom's conditional mechanism, with Kun--Thom's pair and each further
source retained. Cross-review of the central HNN seed checks base
injectivity, genuine centrality, the 25-relator count and the
dimension-free estimate `kappa_new(delta) <= 2 kappa_source(delta)+delta`.
This is written mathematics and graph wiring, not a new Lean result.

### Other connections and limits

- The existing nonhyperlinear root is reached through the wreath and independently
  through the Leavitt argument.
- The Leavitt negative statement selects the existing stable Steinberg branch.
  The relevant equivalence is about the actual Leavitt quotient, not an arbitrary
  central cover.
- Characteristic-two boundary simple Kazhdan groups inherit the negative result
  through the recorded embedding/equivalence. Do not extend that assertion to
  odd characteristic without its own argument.
- The existing finite-presentation partial-table theorem yields a finitely
  presented nonhyperlinear witness from any nonhyperlinear group. Separately,
  the existing simple-envelope theorem yields a two-generator simple witness.
  Those two statements alone do NOT yield one witness having both properties.
- For the binary Leavitt group itself, finite presentation uses the separate
  Khanh input `leavitt-unit-group-finitely-presented`. Simplicity and property (T)
  also use their structural inputs. The Leavitt route therefore offers the
  stronger combined description only with those dependencies retained.
- Nonhyperlinearity ascends to overgroups. It does not automatically pass to
  arbitrary subgroups or quotients. In particular nothing here decides
  Thompson F or V, arbitrary tensor-host finite presentation, or the universal
  Boone-Higman problem.
- Nonsoficity versus hyperlinearity, operator norm versus normalized HS, and
  rank-metric obstructions remain distinct. The global existence of hyperlinear
  nonsofic groups is not ruled out by this chain.

## Audits, source provenance and current acceptance boundary

- [Sections 3-5: physical block construction](liu-block-construction-audit-2026-09-20.md).
- [Sections 6-8: internality, normalization, Thom comparison](liu-internality-normalization-audit-2026-09-20.md).
- [Leavitt and host consequences](liu-leavitt-consequences-audit-2026-09-20.md).

Those three initial audits have now been supplemented by [complete analytic leaf reconstructions](liu-analytic-leaves-proof-acceptance-2026-09-20.md), [independent Theorem 5.1 assembly review](liu-theorem-five-assembly-cross-review-2026-09-20.md), [Section 6 acceptance and the Thom bypass](liu-section-six-acceptance-and-thom-bypass-2026-09-20.md), and [independent direct Leavitt review](liu-leavitt-direct-internality-cross-review-2026-09-20.md). These supply actual written proof routes, rather than converting “no gap found” into acceptance by metadata alone. They remain textual mathematical work with credited imports, not a Lean build or external human referee verdict.

The branch merge exposed unrelated schema errors and a fail-open kernel hazard: a malformed route with a missing premise list could accidentally count as a proof with no premises. The kernel now invalidates malformed routes before propagation, including when loading caches. Eighteen regression tests passed on MSI. The [schema audit](cairn-schema-hygiene-audit-2026-09-20.md) records conservative repairs: proposed dependencies remain unaccepted prose, and four malformed documents were preserved intact as notes rather than supplied invented proofs. The unrelated class-transposition target is correctly OPEN, not silently preserved as a false positive.

### Current validation checkpoint

The [MSI validation record](liu-proof-acceptance-validation-2026-09-20.json) checks pinned commit `3fb72da3f6`: 34,194 nodes, zero schema/artifact errors, and zero duplicate findings among 102 touched canonical nodes. The root, internality, normalization, full-defect theorem and displayed group consequences derive ESTABLISHED without counterfactual assumptions. The stronger one-model normalization claim and compiler positive branch remain OPEN. All 61 schema-hygiene-affected claims preserve their status under the fail-closed kernel, and all four archived documents are byte-identical. The tracked FRONTIER was refreshed. Standard parser, linter, compiler and duplicate checks ran on streamed Git blobs with pinned-tree artifact validation; this was not a full CLI/app build or Lean verification.

### Historical validation checkpoint

The [machine-readable check](liu-cairn-integration-validation-2026-09-20.json)
records 37 new canonical claim/route nodes, no new schema errors against the
merged-main baseline, and no duplicate-node findings. The 70 baseline schema
errors remained unchanged at that earlier checkpoint. Counterfactual compilation confirmed that internality
alone activates the Leavitt route, while adding the conditional normalization
theorem activates the wreath family and its matched refutations. Merely assuming
the single-wreath result does not activate universal normalization. These are
dependency checks, not proof certification; no counterfactual assumption was
written into the actual mathematical status.

The reduced-C-star obstruction is used through the positive node's source-owned
`refuted_by` edge. Cairn's dependency-only root traversal does not count that
edge, so its detached label is not evidence that the obstruction is unused.
No false implication from reduced non-MF alone to nonhyperlinearity was added
merely to alter its layout or reachability score.
