# The trace problem: literature, priority, and formalization audit

The selected result gives a negative answer to Schafhauser–Tikuisis–White
Problem XXII: a separable unital C*-algebra has an additional trace on its
uniform tracial completion. It also gives a factorial tracially complete
pair whose designated traces do not exhaust its tracial state space. The
submission consists of the two declarations selected by
[`Palomar/comparator-stw-xxii.json`](../../Palomar/comparator-stw-xxii.json).
Its claim is a new counterexample application of established methods,
with an explicit Lean proof. It should not claim that the underlying
homogeneous-bundle or Borsuk–Ulam obstruction is new.

The earliest public asking located is **Aaron Tikuisis's May 25, 2020
Canadian Operator Symposium talk**, in its Questions section at
[**37:40–38:58**](https://www.youtube.com/watch?v=qrtLAOC3ZIU&t=2260s). The supplied transcript explicitly asks whether a
factorial tracially complete pair can have X different from T(M), then
asks about completion and trivial-bundle cases. The Fields Institute
record independently supplies the date and speaker. This establishes
Tikuisis as a public presenter of the question, not its sole originator.[^7][^19]

The earliest explicit paper formulation verified here is Question 1.1, printed
page 9 of the first version of *Tracially complete C*-algebras*, posted
**October 31, 2023, at 16:30:19 UTC**. Credit belongs collectively to
**José R. Carrión, Jorge Castillejos, Samuel Evington, James Gabe,
Christopher Schafhauser, Aaron Tikuisis, and Stuart White**, using the
names in the bibliographic record. That is an earliest verified paper
statement, not a determination of who first suggested the question in
private. The completion formulation appears in the following discussion
on the same page. STW's numbered Problem XXII is present in its first
arXiv version, posted **June 12, 2025**.[^1][^2]

No earlier solution of this exact question was located among the primary
sources examined through September 14, 2026 UTC. This finding supports
submission as an original counterexample, with the antecedents below
credited. It cannot establish absolute priority or exclude unpublished
work. The proof's validity and its historical originality are separate
questions: kernel verification settles neither bibliographic priority nor
the adequacy of the mathematical statement as a rendition of the question.

## Question history

Several related questions involve extra traces, but concern different
algebras or different designated sets. Their chronology cannot be merged
into a single date for the present problem.

| Date | Primary evidence | What the evidence establishes |
|---|---|---|
| 1970 | Pedersen–Petersen, Lemma 3.5, p. 202 | A projective homogeneous-block obstruction using Borsuk–Ulam; an ancestor of the method, not the completion question.[^3] |
| June 2012 | Bice–Farah's introduction | Wilhelm Winter asked at the BIRS workshop whether all traces on a countable norm ultraproduct come from ultraproducts of traces. This is a different question.[^4] |
| April 12, 2013 | Ozawa's first arXiv posting | The foundational uniform-completion paper; introducing a construction does not establish first authorship of a later question.[^5] |
| June 29, 2013 | Bice–Farah's first arXiv posting | Public account of Winter's question and a stronger pathological norm-ultrapower example.[^4] |
| September 2, 2013 | Robert's first arXiv posting | A close vector-bundle and corner-compression predecessor for commutator obstructions.[^6] |
| May 25, 2020 | Fields Institute's Tikuisis talk record | Tikuisis explicitly asks the trace question at 37:40–38:58 in the supplied transcript; the event page supplies date and speaker.[^7][^19] |
| March 3, 2023 | Vaccaro's first arXiv posting | A then-forthcoming seven-author draft is credited; a different question about preservation of factoriality is stated and answered negatively.[^8] |
| October 31, 2023 | CCEGSTW v1, Question 1.1, p. 9 | Earliest explicit paper statement verified of the factorial trace problem, with the completion instance immediately discussed.[^1] |
| June 30, 2024 | Evington's first arXiv posting | Positive solution for Z-stable source algebras; subsequent journal publication in 2025.[^9] |
| January 2, 2025 | Farah–Vaccaro's first arXiv posting | Positive solution for factorial trivial W*-bundles with base dimension at most one.[^10] |
| June 12, 2025 | STW v1, Problem XXII | The question appears under the selected number; the v2 citation used for statement review is dated May 8, 2026.[^2] |
| April 27, 2026 | Evington–Tikuisis v1 | A further proof of the type II₁ factorial CPoU positive result.[^11] |

The supplied 2020 transcript resolves the main historical gap left by the
event abstract. At 37:40–38:10 the speaker asks whether retaining the
designated set X is necessary, or whether X must equal all traces on M.
At 38:10–38:58 he discusses completions of separable nuclear algebras and
trivial W*-bundles. At 35:23–35:56 he identifies the seven-author
collaboration. The transcript's repeated “we” does not assign sole
origination to the presenter.[^19]

The transcript has obvious automated transcription errors in mathematical
terms and names. This report paraphrases its mathematical content rather
than presenting silently corrected wording as a verbatim quotation. The
event took place on May 25, 2020; the supplied video-page record dates
its public upload to June 4, 2020. These are respectively the documented
asking date and the recording's upload date. Its description includes an
unrelated “Quantum Graphs and Quantum Graph C*-Algebras” title. That appears
to be a copy-paste error: the video title, named speaker, event, abstract,
and transcript all identify the tracial-completion talk. The unrelated
description title should not be propagated into the citation. White's
accessible 2022 slides are later framework evidence and do not improve
the earliest located asking.[^12]

Evington's 2018 thesis supplies substantial earlier W*-bundle background.
The available thesis did not supply an earlier explicit version of this
question. Its existence, or a talk with a related title, would not justify
attributing the question to one individual. Likewise, Vaccaro's reference
to a forthcoming draft establishes circulation of the collaborative
framework, not the date on which Question 1.1 was first written.[^8][^13]

The appropriate registry wording is therefore: **“A negative answer to
STW Problem XXII and CCEGSTW Question 1.1; an earlier public asking is
recorded in Aaron Tikuisis's May 25, 2020 talk (37:40–38:58).”** It would be unsupported to
write “first asked by White in 2025,” “first asked by Ozawa in 2013,” or
“Winter's 2012 completion problem.”

## Closest mathematical antecedents

### Pedersen–Petersen and Bice–Farah

Pedersen and Petersen construct degree-two homogeneous algebras over
complex projective spaces. Their Lemma 3.5 uses Borsuk–Ulam to force a
lower bound on the number of terms implementing equivalence of two
projections. The actual argument is visible on page 202 of the journal
scan. This is substantive credit for the architecture of the obstruction,
beyond a generic citation to classical topology.[^3]

Bice and Farah revisit those blocks and strengthen the obstruction to
approximation by short sums of self-commutators, using simultaneous
zeros of off-diagonal coordinates. Their Section 2 leads to a trace on
a norm ultrapower that is not even locally obtained from the anticipated
traces. Their paper is especially close to the selected proof's strategy
and was missing from the initial submission metadata despite appearing
in an older repository audit. It is now credited as a mathematical
antecedent.[^4]

The difference relevant to the submitted result can be checked directly.
For a matrix of fixed size two,

\[
 \|a\|\leq \sqrt{2}\,\operatorname{tr}_2(a^*a)^{1/2}.
\]

Taking the supremum over fibres gives the same uniform estimate for the
fixed-rank section algebras. Consequently, a bounded element cannot retain
norm one while its uniform tracial two-norm tends to zero in that model.
This is an analysis of the examples, rather than a claim from the cited
paper. It explains why its extra norm-ultrapower trace does not by itself
supply the discontinuous completion trace selected here. Growing matrix
ranks remove the uniform estimate and permit the new tail construction.

### Robert

Robert's Proposition 6.2 and Example 6.3 deserve explicit credit for the
vector-bundle and distinguished-corner form of the obstruction. A
nonexistence statement for sections forces a point where compression
annihilates the relevant off-diagonal terms. At that point a corner trace
obstructs approximation by finitely many commutators. This is a close
predecessor of the mechanism in the selected Lean development.[^6]

The submission does not import a Lean implementation of Robert's theorem,
and its selected theorem is not stated in that paper. That distinction
is not a reason to omit the mathematical credit. The defensible claim is
an application of this family of ideas to the uniform-completion trace
problem, including the growing-rank scaling, completion identification,
and discontinuity witness. No claim is made that such an application
would require inventing a wholly new obstruction.

### Ozawa and later ultraproduct results

Ozawa introduced the relevant uniform completion and developed the
W*-bundle viewpoint. His discussion around Theorem 8 also records
Pedersen–Petersen examples with extra product or ultraproduct traces.
He deserves foundational credit independently of whether he first posed
the precise question; the latter attribution was not established.[^5]

Vaccaro provides an essential comparison case. His Theorem 1.4 constructs
factorial W*-bundles whose tracial ultraproduct is not factorial. The
conclusion therefore does not give a pair satisfying the factorial
hypothesis in CCEGSTW Question 1.1. Dropping that distinction would make
an earlier negative theorem appear to solve the present problem when its
output violates a hypothesis of that problem.[^8]

Antoine–Perera–Robert–Thiel give broad criteria for density of limit traces
and quasitraces in ultrapowers, including Cuntz-semigroup formulations.
This is relevant background for distinguishing ultrapower questions from
completion questions; it is not a direct formal dependency of the selected
proof.[^14] The earlier Castillejos–Evington–Tikuisis–White paper on uniform
tracial sequence algebras also separates norm-product and tracial-product
trace behavior explicitly.[^15]

### Topology and formal source reuse

Borsuk's 1933 theorem supplies the classical common-zero input.[^16] The
actual Lean theorem is built on the vendored **HamSandwich** development,
pinned at commit `76202dbbb6610ffcebbccfbf7a56f833a4c2a376`. That is a real
formal dependency, not just a citation to a mathematical idea. Its
namespace-isolated Lean 4.28-to-4.32 port and Apache-2.0 provenance are
recorded in [`UPSTREAM.md`](../../GroupApproximation/ThirdParty/HamSandwich/UPSTREAM.md).[^17]

The source metadata consequently uses `related_formalizations` with
`relationship: builds-on` for HamSandwich. Pedersen–Petersen, Bice–Farah,
Robert, Ozawa, and the completion theory receive mathematical-source
entries explaining their roles. These two forms of credit should not be
collapsed: reusing a proof method and reusing existing formal source code
are different contributions.

## Relation to the positive results

The negative theorem has no Z-stability, CPoU, type II₁, or low-dimensional
trivial-bundle hypothesis. Earlier positive results impose substantive
conditions; they are not contradicted by the chosen existential statements.

| Source | Relevant positive scope | Consequence for submission wording |
|---|---|---|
| Evington, Theorem A | Uniform completion of a Z-stable base with compact nonempty trace space | Do not present the result as disproving the Z-stable case.[^9] |
| Evington, Theorem B | Type II₁ factorial tracially complete pairs with CPoU | Include the type II₁ hypothesis when citing this formulation.[^9] |
| Farah–Vaccaro | Factorial **trivial** W*-bundles with base covering dimension at most one | Keep “trivial”; a broader talk abstract or survey shorthand is insufficient.[^10] |
| Evington–Tikuisis, Theorem C / 4.1 | Type II₁ factorial tracially complete pairs with CPoU | Credit the newer proof and preserve its hypotheses.[^11] |
| Vaccaro, Theorem 1.3 | Tracial ultraproducts of factorial W*-bundles with uniformly bounded base dimensions | The present construction uses unbounded dimensions.[^8] |

These distinctions matter more than the title of a surrounding survey.
Although STW's collection concerns nuclear C*-algebras, a submission must
report what its selected declarations actually assert. Here the selected
base is separable and unital. The registry statements do not assert
nuclearity, type I, a Bauer trace simplex, simplicity, or a type II₁
counterexample. Broader repository endpoints must not silently enlarge
that selected scope.

Toms's 2026 *Schubert Calculus and uniform property Gamma* supplies further
context on topological obstructions and regularity. Its abstract addresses
comparison and uniform property Gamma, rather than an additional trace on
a uniform completion. It was not evidence of a prior answer to XXII.[^18]

## Actual selected proof

This account is based on the local Lean source, especially
[`STW22AntipodalBlockData.lean`](../../GroupApproximation/Analysis/STW22AntipodalBlockData.lean),
[`STW22UnconditionalCore.lean`](../../GroupApproximation/Analysis/STW22UnconditionalCore.lean),
and the [Palomar bridge](../../GroupApproximation/PalomarBridges/XXII.lean).
It separates what the selected proof actually uses from a different earlier
informal account in the repository.

For positive integer s and d = 4s², take continuous matrix functions on
Sᵈ with covariance f(−x) = u f(x) u, where
u = diag(1,−1,…,−1) has size s+1. Geometrically these are endomorphism
sections of the trivial line plus s copies of the complexified real
tautological line over RPᵈ. The base algebra is the unitized c₀-sum of
these blocks, with s increasing along the sequence.

The witness in each block is

\[
 h_s=\operatorname{diag}(1,-1/s,\ldots,-1/s),\qquad
 \operatorname{tr}_{s+1}(h_s)=0,\qquad
 \operatorname{tr}_{s+1}(h_s^2)=1/s.
\]

Thus its norm remains one while its uniform tracial two-norm is 1/√s.
For a finite packet of m ≤ s elements, the off-diagonal rows and columns
from the distinguished coordinate give an odd map with 2ms complex
coordinates. Its real dimension is 4ms ≤ d. Borsuk–Ulam supplies a common
zero. The corresponding coordinate state detects h_s and annihilates
the self-commutators in that packet.

Choosing arbitrarily late coordinates also makes finitely many c₀
constraints small. Compactness of the state space then produces a tracial
state on the bounded-product/c₀ corona which evaluates h to one. The
completion is identified with scalars plus the uniform-two-null ideal
inside the bounded product. Pulling back the corona trace gives a trace
on that completion.

Tail truncations h^(N) still have value one under this trace, while their
uniform two-norms tend to zero. This proves discontinuity. The designated
canonical extensions are continuous, so the trace is additional.
Completeness, the closed-face property, trace restriction, density, and
separability supply the two exact selected statements.

The older informal account uses complex projective spaces, a Chern-class
obstruction, another normalization of the witness, and a character. Those
features should not describe the literal selected Lean route: the selected
route uses real-projective antipodal blocks and a **tracial state** obtained
by finite constraints and compactness. In particular, it does not require
a character or a Cuntz–Pedersen/Jordan-decomposition separation step just
because some imported files or namespaces mention that machinery.

## Statement fidelity and metadata corrections

The Challenge is intentionally independent of the solution construction.
Its `TracialState` is a unital positive complex-linear functional satisfying
the trace identity. Positivity supplies norm continuity; omitting a
separately bundled continuity proof does not enlarge the class of traces.
The topology is pointwise weak-star convergence. Sequential continuity
at zero expresses uniform-two continuity in this seminorm setting.

Its completion presentation consists of a unital star-homomorphism
α : A → M, a tracially complete pair (M,X), unique restriction of X onto
all base traces, and uniform-two density of α(A). CCEGSTW Corollary 3.29(i)
identifies completion from a dense C*-subalgebra.[^1] Applying it here
requires the usual facts that the image is a C*-algebra, base traces factor
through α, and bounded image elements have bounded lifts. The Solution's
concrete witness is the bounded-Cauchy quotient itself. No additional
injectivity hypothesis is necessary for the presented completion notion.

Factoriality is an explicit assumption of the **general** trace question.
It follows for the completion pair formed using **all** base traces; it
is not an extra printed assumption in XXII. Four old module comments
were corrected accordingly without changing any Lean declarations or
proof terms.

The revised package makes the following corrections concrete:

| Issue | Correction |
|---|---|
| Missing close predecessors | Added Pedersen–Petersen, Bice–Farah, Robert, and Ozawa with their mathematical roles. |
| Earlier related counterexample easy to conflate | Added Vaccaro, explaining why a nonfactorial ultraproduct does not settle the factorial trace question. |
| Vague originality claim | Limited it to the counterexample application and explicitly credited the inherited obstruction. |
| Question dated only by the current survey version | Recorded Tikuisis’s 2020 public asking, the 2023 first verified paper formulation with all seven authors, and the 2025 first numbered XXII. |
| Positive-theorem hypotheses omitted in shorthand | Included type II₁ for the CPoU theorem and triviality for Farah–Vaccaro. |
| Informal and formal proofs conflated | Recorded the actual antipodal/corona-trace route and its normalization. |
| Formal dependency understated | Kept the exact HamSandwich source pin, license, and builds-on relationship. |
| Selected scope could be confused with broader endpoints | Explicitly listed properties not asserted by the two selected declarations. |
| Production credit no longer described revised prose | Distinguished Astra's argument, Claude's original exposition, and Codex's submission/literature work; retained human authorship and responsibility with Sauers. |
| Registry readiness confused with acceptance | Kept self-assessed review status and explicit not-submitted status. |

Dates were taken from submission histories and publisher records rather
than search-engine crawl dates or regenerated PDF footers. In particular,
Bice–Farah's arXiv paper has a 2013 submission history even though the
rendered copy carries a later typesetting date. Pedersen–Petersen is cited
as volume 27 (1970), matching the journal's record, rather than treating
a parenthetical 1971 in a later bibliography as a separate original work.

## Verification and remaining limits

The two selected proofs are unconditional and their permitted axioms are
`propext`, `Classical.choice`, and `Quot.sound`. The Challenge contains two
intentional placeholders for the registry protocol; the Solution contains
proofs whose closures must exclude `sorryAx`. Source checks, elaborated
statement comparison, axiom closure, Comparator, Lean kernel replay, and
NanoDa replay are separately recorded in the
[submission readiness record](https://github.com/SauersML/group-approximation/blob/main/research/artifacts/palomar-stw-xxii-submission-readiness-2026-09-13.md).
That record identifies the immutable candidate and exact verification runs.

The literature audit does not claim a human expert's endorsement, an
exhaustive search of unpublished mathematics, or editorial acceptance.
The 2020 transcript establishes an earlier public asking than the 2023
paper. It does not establish that no earlier private or public asking
occurred, or that the speaker originated the question alone. No messages were sent to authors to seek private priority
information. No Palomar intake or submission was initiated.

## Sources

[^1]: José R. Carrión, Jorge Castillejos, Samuel Evington, James Gabe, Christopher Schafhauser, Aaron Tikuisis, and Stuart White. [*Tracially complete C*-algebras*, v1](https://arxiv.org/pdf/2310.20594v1), October 31, 2023, Question 1.1, p. 9; [submission history](https://arxiv.org/abs/2310.20594); [v6](https://arxiv.org/html/2310.20594v6), August 7, 2026, definitions and Corollary 3.29(i) used for fidelity review.
[^2]: Christopher Schafhauser, Aaron Tikuisis, and Stuart White. [*Nuclear C*-algebras: 99 problems*, v1](https://arxiv.org/pdf/2506.10902v1), June 12, 2025, Problem XXII; [v2, Section 7](https://arxiv.org/html/2506.10902v2#S7), May 8, 2026, p. 24; [version history](https://arxiv.org/abs/2506.10902).
[^3]: Gert K. Pedersen and Nils H. Petersen. [*Ideals in a C*-Algebra*](https://doi.org/10.7146/math.scand.a-10998), *Mathematica Scandinavica* 27 (1970), 193–204. [Journal scan](https://journals.msp.org/mscand/article/download/2324/2323), pp. 201–203, especially Lemma 3.5 on p. 202.
[^4]: Tristan Bice and Ilijas Farah. [*Traces, Ultrapowers and the Pedersen-Petersen C*-Algebras*](https://arxiv.org/abs/1307.0111), first posted June 29, 2013; *Houston Journal of Mathematics* 41 (2015), 1175–1190. [Text](https://arxiv.org/pdf/1307.0111), introduction and Section 2, Theorem 2.1 and Corollary 2.2.
[^5]: Narutaka Ozawa. [*Dixmier approximation and symmetric amenability for C*-algebras*](https://arxiv.org/abs/1304.3523), first posted April 12, 2013; [text](https://arxiv.org/pdf/1304.3523), Sections 3–5, particularly the discussion before Theorem 8 and the completion/W*-bundle construction.
[^6]: Leonel Robert. [*Nuclear dimension and sums of commutators*](https://arxiv.org/abs/1309.0498), first posted September 2, 2013; *Indiana University Mathematics Journal* 64 (2015), 559–576. [Text](https://arxiv.org/pdf/1309.0498), Proposition 6.2 and Example 6.3.
[^7]: Fields Institute. [Aaron Tikuisis, *Uniformly tracially complete C*-algebras*](https://www.fields.utoronto.ca/talks/PLENARY-Uniformly-tracially-complete-C-algebras), 48th Canadian Operator Symposium, online, May 25, 2020, 15:10–16:00. [Author's talks index](https://mysite.science.uottawa.ca/atikuisis/talks.html), indexed listing; underlying slides unavailable for verification.
[^8]: Andrea Vaccaro. [*Ultraproducts of factorial W*-bundles*](https://arxiv.org/abs/2303.01942), first posted March 3, 2023; [journal text](https://www.uni-muenster.de/FB10/mjm/vol_16/mjm_vol_16_09.pdf), *Münster Journal of Mathematics* 16 (2023), 301–322, Question 1.2 and Theorems 1.3–1.4.
[^9]: Samuel Evington. [*Traces on the uniform tracial completion of Z-stable C*-algebras*](https://doi.org/10.1112/jlms.70207), *Journal of the London Mathematical Society* (2025), Theorems A and B. [Preprint and version history](https://arxiv.org/abs/2407.00727), first posted June 30, 2024. The journal's Theorem B numbering is used here.
[^10]: Ilijas Farah and Andrea Vaccaro. [*Continuous Selection of Unitaries in II₁ Factors*, v3](https://arxiv.org/abs/2501.01272v3), September 15, 2025; first posted January 2, 2025. Abstract and trace theorem specify factorial trivial W*-bundles and covering dimension at most one.
[^11]: Samuel Evington and Aaron Tikuisis. [*The real and stable rank of tracially complete C*-algebras*, v2](https://arxiv.org/abs/2604.24206v2), May 8, 2026; first posted April 27, 2026. [Text](https://arxiv.org/pdf/2604.24206v2), Theorem C and Theorem 4.1.
[^12]: Stuart White. [OADG 2022 slides](https://web.math.ku.dk/~rordam/OADG-2022/Slides/White.pdf), 2022. Classification and tracially complete framework; no explicit earlier trace question verified in these slides.
[^13]: Samuel Evington. [*W*-Bundles*, doctoral thesis](https://theses.gla.ac.uk/8650/1/2018EvingtonPhD.pdf), University of Glasgow, 2018. Earlier framework background; no earlier explicit trace-problem formulation established from this source.
[^14]: Ramon Antoine, Francesc Perera, Leonel Robert, and Hannes Thiel. [*Traces on ultrapowers of C*-algebras*](https://arxiv.org/abs/2303.01929), first posted March 3, 2023. [Text](https://arxiv.org/pdf/2303.01929), Theorem A and Section 2.
[^15]: Jorge Castillejos, Samuel Evington, Aaron Tikuisis, and Stuart White. [*Classifying maps into uniform tracial sequence algebras*](https://ora.ox.ac.uk/objects/uuid%3A070c0c5f-c489-4845-b4d2-bfe596c78710/files/skk91fk879), author manuscript, discussion preceding Proposition 2.5; [journal copy](https://d-nb.info/1244290335/34), p. 274.
[^16]: Karol Borsuk. [*Drei Sätze über die n-dimensionale euklidische Sphäre*](https://doi.org/10.4064/fm-20-1-177-190), *Fundamenta Mathematicae* 20 (1933), 177–190.
[^17]: akopjan/HamSandwich. [Source at commit 76202dbbb6610ffcebbccfbf7a56f833a4c2a376](https://github.com/akopjan/HamSandwich/tree/76202dbbb6610ffcebbccfbf7a56f833a4c2a376), July 6, 2026. Local port details in [`UPSTREAM.md`](../../GroupApproximation/ThirdParty/HamSandwich/UPSTREAM.md).
[^18]: Andrew S. Toms. [*Schubert Calculus and uniform property Gamma*](https://arxiv.org/abs/2606.12188), June 2026. Abstract used to distinguish regularity/comparison results from the selected trace assertion.

[^19]: Aaron Tikuisis, [*Uniformly tracially complete C*-algebras*, official Fields Institute recording](https://www.youtube.com/watch?v=qrtLAOC3ZIU&t=2260s), Questions section 37:40–38:58; collaboration credit 35:23–35:56. Access note: the timestamped transcript and video URL were supplied on September 13, 2026 America/Chicago; the transcript was read directly and YouTube's oEmbed record independently confirmed the title and Fields Institute channel. No independent audio transcription is claimed. The supplied video-page metadata dates its upload to June 4, 2020. The event identification and May 25, 2020 talk date are supported by the Fields event record; the preceding Matthew Kennedy talk mentioned in the transcript also matches its program. The description's unrelated Quantum Graphs title is inconsistent with the actual video title and content.
