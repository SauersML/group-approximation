# Archaeology of `non_mf_groups_exist.tex`

This document reconstructs how the non-MF manuscript arose, what its first
claims were, which earlier results made them possible, and how the paper and
Lean dependency chains differ. It is based on the repository notes, source
files, commit messages and diffs, manuscript credit audits, and the recursive
Lean import graph.

All times below are commit author times in `America/Chicago`. Short hashes are
used because the history contains many concurrent commits within the same
minute. The archaeology should be read as a history of the recorded
repository, not as a claim that every transient idea was correct when first
written.

## Executive answer

The manuscript was not the planned endpoint. The active program on
2026-08-08 was Question 3.4, whether every hyperlinear group is sofic. The
research tried to start with nonsofic compression/lamp groups and manufacture
Hilbert--Schmidt models from operator-norm models. That program repeatedly ran
into a rank-visibility problem: operator norm can see a defect living on a
vanishing fraction of the matrix dimension, while normalized
Hilbert--Schmidt norm cannot.

The decisive reversal was this:

```text
attempted route
    weak-MF Clifford cover
        -> cut to the negative central sector
        -> renormalize its trace
        -> obtain a hyperlinear nonsofic image

what the analysis actually proved
    any negative Clifford sector in a norm-matrix corona
        -> adjoint/conjugation representation
        -> Kazhdan fixed-space inclusion
        -> stable-finite equality
        -> two distinct Clifford lamps must agree in L2
        -> contradiction
        -> every norm-corona representation kills the Clifford sign
```

The first recorded group-level non-MF theorem is therefore a failed-route
result. It appeared in `NOTEPAD.md` at commit `112e04a6` on
2026-08-09 13:11:27 under the heading “The Clifford sign is invisible in
every norm-matrix model.” It was promoted into the durable no-go note
`docs/FALSE_CLIFFORD_NORM_MF_STERILITY.md` at `d1eb160f` on
2026-08-12 17:51:05.

The first explicit **finitely presented** non-MF claim appeared 81 minutes
later, at `a1fa3786` on 2026-08-12 19:12:06, in
`docs/EXPLICIT_FINITELY_PRESENTED_NON_MF_GROUP.md` and `docs/AGENDA.md`.
The extraction replaced the entire infinite Clifford lamp group by:

- one involution `c` centralizing the Kazhdan subgroup;
- its transported copy `d = tct^{-1}`;
- one marked commutator `w = [d, ada^{-1}]`; and
- relations making `w` a central involution.

The infinite Clifford group was retained only as an external witness that
the finite presentation does not accidentally kill `w`. The first full TeX
draft followed at `bf2325ce`, 2026-08-12 19:40:48.

In short: the paper happened because a proposed route **through** weak MF
proved a universal obstruction **to** weak MF, and because the obstruction
could be localized to a single marked word.

## What “dependency” means here

There are four different graphs, and conflating them gives a misleading
history.

1. **Discovery dependencies** are ideas and failed routes that caused the
   theorem to be noticed.
2. **Paper proof dependencies** are the mathematical statements actually
   used by `non_mf_groups_exist.tex`.
3. **Lean theorem dependencies** are declarations used to prove the formal
   endpoint. The formal finitely presented group is not the paper's literal
   eight-generator group.
4. **Lean import dependencies** are files loaded transitively. This is a
   strict over-approximation of theorem dependency: a file can import a large
   module while using only one declaration from it.

This document records all four and labels them explicitly.

## The discovery spine

### 1. Infrastructure before the MF question, August 1--7

The repository began as a nonsoficity and group-approximation project. Several
bricks later reused by the non-MF proof were already present for different
reasons.

| Time | Commit | Where | What was available |
| --- | --- | --- | --- |
| Aug 1 15:17 | `9db64a7e` | then `NonsoficGroupsExist/Kazhdan.lean` and `CompressionSetup.lean` | The abstract Kazhdan-compression setup. |
| Aug 3 14:26 | `9adb6a45` | the future `Leavitt/UniversalRankFour.lean` | The explicit rank-four Leavitt ambient group used by the formal witness. |
| Aug 4 09:28--10:12 | `e676c411`, `ce951ac3`, `85fad483`, `9d132492` | `PropertyT/A2Magic*.lean` | The six-vertex `A_2` incidence, local energy estimates, Laplacian, and strict energy gap. |
| Aug 4 17:15--23:28 | `dcbf079d`, `62c86c00`, `e036989f` | `PropertyT/FreeRootCharacterValuation.lean`, `FreeElementaryPropertyT.lean`, future `Leavitt/UniversalPropertyT.lean` | The internal property-(T) proof for free elementary groups and its universal-Leavitt specialization. |
| Aug 5 00:04--00:46 | `a4a6cb53`, `f3a53ef4` | `Leavitt/UniversalLeavitt*.lean`, `PropertyT/FiniteTypeCharacteristicTwoPropertyT.lean` | The universal binary Leavitt algebra and property (T) for rank three over finite-type characteristic-two algebras. |
| Aug 5 14:15 | `2c769be9` | `Kazhdan/ShalomFinitePresentation.lean` | The internal Shalom finitely presented Kazhdan-cover construction later used by the formal non-MF witness. |
| Aug 7 16:36 | `70a4ba36` | `Criterion/ExactCompression.lean` | In an exact finite action, a one-sided conjugate inclusion becomes equality by cardinality. |
| Aug 7 17:39 | `7b7aa052` | `Criterion/CommutantRigidity.lean` | The finite-dimensional adjoint version: the commutant cannot grow under compression because finite dimension replaces finite cardinality. This is the direct ancestor of manuscript Theorem B. |

The August 7 commit message already states the trichotomy that later became
central: exact finite sets use cardinality; exact finite-dimensional
representations use dimension; the tracial infinite-dimensional setting can
fail because a `II_1` factor is not co-Hopfian. The non-MF proof would add the
third successful finite setting: Murray--von Neumann finiteness in an
operator-norm matrix corona.

### 2. The operator-norm detour, August 8

`docs/AGENDA.md` records that the new campaign began on 2026-08-08 as a
program for the hyperlinear-versus-sofic question.

At `c58df131` (11:42:48), `Sofic/NormTraceGap.lean` isolated the fundamental
interface:

- operator-norm multiplicative error controls normalized
  Hilbert--Schmidt error dimension-independently;
- operator-norm separation does **not** imply tracial separation;
- identity-block padding preserves operator norm while making every
  normalized Hilbert--Schmidt distance vanish.

This closed the naive implication “weak MF implies hyperlinear.” It also made
rank renormalization the central design problem.

At `e30bfd1e` (12:17:47), `Sofic/FreeLampReduction.lean` formalized the
group-theoretic free-lamp reduction around a one-sided Kazhdan compressor and
one centralizing element. The note and commit explicitly targeted a
hyperlinear nonsofic group, not a non-MF group.

An early note then overclaimed weak MF for a symmetric double. Commit
`8879c935` (Aug 9 08:30) records the correction: Shulman's C*-algebraic
amalgam theorem did not automatically preserve the abstract group normal
form. A later, different profinite-regular argument established the needed
weak-MF double at `1540713f` and reconciled the status at `418f2a9d`. This
episode matters because it shows why the eventual non-MF theorem cannot be
read as a routine corollary of MF permanence.

The proof shape itself was already emerging on August 8:

- `f857d2e3` (16:50) added an “MF Mautner decomposition” to `NOTEPAD.md`.
  It used the Kazhdan projection and finiteness of a norm matrix corona to
  force an invariant Kazhdan corner. It still lacked a rank-insensitive
  group element detecting that corner.
- `d3ca88a4` (19:18) identified strict compression with an infinite
  Kazhdan projection in a left--right envelope.
- `b2d1ecc8` (Aug 9 12:47) exposed the related universal projection in the
  full group C*-algebra. This was only a C*-algebra obstruction, not yet a
  group-level kernel theorem.

### 3. The Clifford sign supplies the detector, August 9

The search next introduced Clifford/CAR lamps because their central sign
provides a finite-order spectral sector. The negative sector can be cut out
and regarded as a new matrix sequence, eliminating the vanishing-density
problem that had blocked all earlier norm-to-trace conversions.

At `cd899946` (02:53), the formal library acquired the constructive Kazhdan
projection, weak-MF ultraproduct interface, vector GNS layer, and the first
Kazhdan corner modules. These were built for the broader weak-MF/hyperlinear
investigation.

At `112e04a6` (13:11), the argument reversed direction. `NOTEPAD.md` proved:

> Every homomorphism of the complete or sparse Clifford semidirect product
> into a norm quotient of matrix algebras kills the central Clifford sign.

The four load-bearing moves were already the ones in the final paper:

1. cut to the `z = -1` corner;
2. conjugate on normalized Hilbert--Schmidt matrix space;
3. use the Kazhdan projection and the one-sided compressor;
4. use stable finiteness to turn the projection inclusion into equality.

The note correctly separated this from the Hilbert--Schmidt setting: an HS
almost representation does not give an operator-norm representation of the
adjoint maps in a stably finite norm corona.

Also on August 9, `c2e5cd5d` (10:30) formalized the proper binary Leavitt
shift. This later supplied the formal witness with an internally proved
injective, non-surjective endomorphism. It was not needed for the paper's
literal base `Z^3 semidirect SL_3(Z)`.

### 4. From a failed Clifford route to one marked word, August 12

The theorem remained part of the hyperlinear-versus-sofic no-go analysis for
three days. At `d1eb160f` (17:51), it was moved into
`docs/FALSE_CLIFFORD_NORM_MF_STERILITY.md`; the file name reflects its role at
that time: it killed a proposed route to a different goal.

At `a1fa3786` (19:12), the key finite-presentation extraction appeared.
Instead of finitely presenting the infinite lamp group, the construction
adjoined one lamp `c` and imposed central order two only on the one word whose
survival mattered. The coset Clifford group became a quotient target used
solely to prove `w != 1`.

This extraction is the conceptual bridge from the August 9 theorem to the
paper:

```text
infinite Clifford group                     finite marked presentation
-----------------------                     --------------------------
central sign z                              marked word w
root Majorana c_Gamma                       one generator c
moved Majorana c_(t Gamma)                  d = tct^-1
second site c_(a t Gamma)                   ada^-1
[two distinct Majoranas] = z                [d, ada^-1] = w
all Clifford relations                      only c^2, w^2, centralizer,
                                             and centrality of w
```

At `5158bff8` (19:30), the note sharpened the observation to one Clifford
edge. At `bf2325ce` (19:40), `non_mf_groups_exist.tex` was added with the
corner cut, conjugation corona, Kazhdan order argument, stable-finiteness
pinning, finite-dimensional theorem, cyclic-base calibration, and an
explicit linear/Clifford witness.

## First appearances of the headline claims

| Claim | First recorded location | Commit and time | Later status |
| --- | --- | --- | --- |
| Operator-norm approximation alone carries no trace information | `Sofic/NormTraceGap.lean` and `NOTEPAD.md` | `c58df131`, Aug 8 11:42 | Kernel-checked; explains the limitation of the final theorem. |
| Stable-finite Kazhdan pinning for a norm-corona representation | `NOTEPAD.md`, “MF Mautner decomposition” | `f857d2e3`, Aug 8 16:50 | Became the analytic heart of Theorem A. |
| Every norm-corona representation kills a Clifford sign | `NOTEPAD.md`, “The Clifford sign is invisible...” | `112e04a6`, Aug 9 13:11 | First group-level non-MF theorem in the recorded history. |
| Durable non-MF Clifford no-go | `docs/FALSE_CLIFFORD_NORM_MF_STERILITY.md` | `d1eb160f`, Aug 12 17:51 | Later points to the standalone manuscript. |
| Explicit finitely presented non-MF group | `docs/EXPLICIT_FINITELY_PRESENTED_NON_MF_GROUP.md`, `docs/AGENDA.md` | `a1fa3786`, Aug 12 19:12 | First marked finite-presentation extraction. |
| One Clifford edge suffices | same note | `5158bff8`, Aug 12 19:30 | Explains why the finite presentation needs only one marked word. |
| Full manuscript Theorems A--C | `non_mf_groups_exist.tex` | `bf2325ce`, Aug 12 19:40 | Referee and attribution revisions followed. |
| Finite-normal obstruction criterion and Theorem D | manuscript introduction and later proof sections | `1a038269` through `4219f4f6`, Aug 12 21:11--21:15 | Paper-proved generalization of the central-involution case. |
| MF radical, permanence failures, scaling family, multiplicity, uniformity | manuscript consequences | `c3501887`, Aug 12 21:17 | Paper-only consequences at that point. |

## Formalization chronology

The formalization was a parallel construction, not a transcription of the
literal eight-generator paper group.

| Time | Commit | Formal brick |
| --- | --- | --- |
| 19:50 | `7e633404` | `NormMFResidualDetector`, `OpAlmostRepresentation`, and involution-corner primitives. |
| 19:51 | `e3e6740c` | The formalization blueprint and lane map. |
| 20:00 | `4a00268a` | Theorem B, the finite-dimensional marked-commutator kill, machine-checked over every field. |
| 20:01 | `868e17cf` | `ExplicitNonMFBase`: the internal Leavitt Kazhdan group, proper shift, and omitted element. |
| 20:06 | `094b7f32` | Existing Kazhdan corner machinery generalized from separated weak-MF models to arbitrary operator-norm almost representations. |
| 20:10 | `525d58e8` | Analytic data generalized from an embedded subgroup/endomorphism to image inclusion; injectivity is not needed. |
| 20:10 | `9f64ddba` | The independent finite marked presentation scaffold. |
| 20:13 | `b7a7502d` | Mapping telescope for an injective endomorphism. |
| 20:17--20:18 | `4181c9cb`, `5873fdb1` | Extraction of sequential marked almost representations from arbitrary norm ultraproducts. |
| 20:19 | `0bc1212e` | Presented Clifford lamp group, nontrivial sign, and permutation action. |
| 20:21--20:23 | `9ed3a245`, `0f192514` | Equal-rank projection flip, the finite-dimensional shadow of stable finiteness. |
| 20:24--20:27 | `f1a8f537`, `0c7c4493`, `a2e0a48f`, `ce295db8` | MF-residual functoriality, sequential reduction, adjoint almost representation, and explicit witness assembly. |
| 20:35--20:39 | `764de0e0`, `1af31c75`, `a526bc5b` | Finished finite presentation, dimension-free vector chain, and packaged endpoint. |
| 20:47 | `9562257f` | Negative involution corner generalized to marked models. |
| 20:58 | `6e27dbb8` | Sequential kill theorem and public endpoints assembled. |
| 21:22 | `77369f38` | Focused axiom audit for the explicit non-MF theorem. |
| 21:47--21:54 | `368332e7`, `c1a402a5`, `ddd09cca` | Final stabilization, coercion repair, and completion of the sequential proof. |
| 21:56 | `85585534` | Explicit endpoint integration repaired. |

The public endpoint proves that an independently constructed finitely
presented group exists whose nontrivial marked element is invisible to every
operator-norm matrix ultraproduct. The manuscript's concrete
`Z^3 semidirect SL_3(Z)` presentation is proved in TeX, not identified with
the formal witness.

## Manuscript evolution after the first draft

The first draft was not the present paper. The history records several
substantive upgrades and corrections:

- `525d58e8` removed injectivity and endomorphism structure from the analytic
  criterion, retaining only one-sided inclusion of the image.
- `8d962426` clarified the two incompatible uses of “MF” in the literature
  and sharpened the cyclic comparison.
- `bc557c4d` and `30d6f486` performed a referee-style revision.
- `1a038269`, `10763ab5`, `0f6325e6`, and `4219f4f6` replaced the
  central-involution-only proof by the finite-normal obstruction criterion.
- `c3501887` added the consequences section.
- `e958cf46` hardened the literal presentation and separated presentation
  identities from injectivity claims.
- `c79d55dd`, `c2ff4c04`, and `6783c574` narrowed priority claims, added
  lineage, and disclosed tool use.
- `936c7be9` corrected the claim about stable-finite non-MF C*-algebras:
  MIP*=RE already implies abstract examples; the new result is the explicit
  reduced group C*-algebra realization.
- `72114a9e` added credit for finite-normal approximation machinery.

The audit also caught a concrete transcription error in the displayed
`SL_3(Z)` presentation: the `x` and `y` matrices had been swapped relative
to Conder--Robertson--Williams. The relator set was symmetric under that swap,
so the downstream theorem was unaffected, but the paper and action formulas
were corrected after direct source reading. The same audit rejected a
fetched-summary claim about Thom 2010 after the primary paper did not support
it. These are important examples of why the final paper cannot be
reconstructed safely from commit subjects alone.

