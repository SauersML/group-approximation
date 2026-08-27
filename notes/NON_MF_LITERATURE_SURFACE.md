# The residual literature surface of `non_mf_groups_exist.tex`

Phase 4 audit. What stands between the manuscript and **zero unformalized
literature inputs**, measured rather than estimated.

Anchors are line numbers in the working copy at the time of writing plus a
grep string; the `.tex` is under concurrent edit, so trust the grep string.

---

## 0. Method, and the exact queries

**Claims with declared external inputs.** `notes/NON_MF_NUMBERED_CLAIMS.json`
holds 56 claims (17 `theorem`, 12 `corollary`, 10 `proposition`, 7 `lemma`,
5 `definition`, 4 `mainthm`, 1 `construction`).

```python
json.load(open('notes/NON_MF_NUMBERED_CLAIMS.json'))['claims']
# -> [x['id'] for x in claims if x['external_inputs']]   == ['cor:undecidable']
# -> [x['id'] for x in claims if x['coverage_gap']]      == ['cor:undecidable']
# -> [x['id'] for x in claims if x['extra_assumptions']] == []
# -> Counter(x['status'] for x in claims) == {'exact': 55, 'literature-input': 1}
```

**Confirmed** at the revision this was taken.

> **Re-run 2026-08-17 — every number in the block above has moved, and the
> conclusion it supported is gone.** Against the current
> `notes/NON_MF_NUMBERED_CLAIMS.json`:
>
> ```python
> # -> [x['id'] for x in claims if x['external_inputs']]   == []
> # -> [x['id'] for x in claims if x['coverage_gap']]      == []
> # -> [x['id'] for x in claims if x['extra_assumptions']] == []
> # -> Counter(x['status'] for x in claims) == {'exact': 54}
> ```
>
> **No** numbered claim declares an external input any more. `cor:undecidable`
> was the one, and it is now proved on both clauses — see § 3.6, rewritten
> below.  The environment count is 54, not 56.  The section's *argument*
> survives the correction intact and is worth restating for that reason: the
> numbered-claim surface was never where the literature debts lived, and an
> empty `external_inputs` list is no more a certificate now than a
> one-element list was then.

That fact is true and it is also the least informative true fact about this
manuscript's literature surface, because **the numbered-claim surface is not
where the literature debts live.** Five of the seven live debts sit in
unnumbered `\paragraph{}` blocks, one sits in a `\begin{proof}` of an
unnumbered claim, and one is not a citation at all. None of them is reachable
from the JSON, and none of them is reachable from any gate: `check_non_mf_refs.py`
validates `\leanverified` badges against Lean declarations and never reads a
`\cite`; the zero-input and unconditional gates read Lean, not TeX. **No tool in
this repository inspects the bibliography surface.**

**Environment membership** was determined by bracket-matching, not by eye:
a stack of `\begin{env}`/`\end{env}` over
`theorem|mainthm|proposition|lemma|corollary|definition|remark|proof|construction|abstract`,
truncated at `\begin{thebibliography}` (line 3805), with commented-out `\cite`s
excluded (there are none). Script: the parser in this audit's scratch
directory; results reproduced in §1.

**Measured citation counts** (65 `\cite` commands, 77 key mentions, 45 distinct
keys, and all 45 bibitems are cited — no orphan entries):

| key | n | key | n | key | n |
|---|---|---|---|---|---|
| `Shulman` | 5 | `TWW` | 2 | `Th` | 1 |
| `CDE` | 4 | `GKEMP` | 2 | `LuO` | 1 |
| `BK` | 3 | `FGH` | 2 | `Kun16` | 1 |
| `BDL` | 3 | `DGLT` | 2 | `KT19` | 1 |
| `FFF` | 3 | `OAI` | 2 | `Fritz` | 1 |
| `SlofstraCorrelations` | 3 | `KT` | 2 | `GR` | 1 |
| `ElekSzabo` | 3 | `MdlS` | 2 | `Gl19` | 1 |
| `Rabin58` | 3 | `AlekseevThom` | 2 | `BekkaAmenable` | 1 |
| `Schafhauser` | 2 | `SlofstraProfile` | 2 | `BekkaValette` | 1 |
| | | `SlofstraVidick` | 2 | `Dadarlat` | 1 |
| | | `BHV` | 2 | `Loring` | 1 |
| | | `Neumann37` | 2 | `Lance` | 1 |
| | | `HT` | 1 | `Ozawa` | 1 |
| | | `MIPRE` | 1 | `NetzerThom` | 1 |
| | | `CRW` | 1 | `CLV` | 1 |
| | | `NST` | 1 | `Malcev` | 1 |
| | | `GHW` | 1 | `KWPermanence` | 1 |
| | | `KWExact` | 1 | `ElekSzaboHyper` | 1 |

The brief's working list differs from the measurement (`FFF` 3 not 4;
`Shulman` 5 not 2; `Ozawa` 1 not 2; `BK` and `BDL` 3 not 2). **`Kropholler`
does not appear in this manuscript at all** — not in the body, not in the
bibliography. It belongs to the other manuscript. `FFF` is cited 3 times and
Fournier-Facio is *named in prose* at 5 sites (L159, L854, L3278, L3680, L3704),
which is presumably the "five mentions" of the earlier pass: two of the five
are personal-communication attributions carrying no `\cite`.

---

## 1. Where the citations sit

Only **four** `\cite` commands are inside a numbered environment:

| line | keys | environment |
|---|---|---|
| 856 | `FFF` | `remark[rem:ff-realization]` |
| 1479–1482 | `CRW`, `CLV`, `BHV` | `remark[rem:classical-base]` |
| 2540–2541 | `SlofstraCorrelations`, `NST` | `definition[def:radical]` |
| 3549 | `Rabin58` | `corollary[cor:undecidable]` |

Five more are inside a `\begin{proof}`. Bracket-matching the proof to what it
proves:

| line | keys | proof opened at | proves |
|---|---|---|---|
| 1371, 1373 | `Ozawa`, `NetzerThom` | 1342 | `proposition[prop:literal-base-T]` |
| 3368 | `ElekSzabo` | 3336 | `\begin{proof}[Proof of Theorem~\ref{thm:E}]` |
| 3404 | `Malcev` | 3394 | **unnumbered** — `\paragraph{Failure of extension permanence.}` |
| 3442 | `ElekSzaboHyper` | 3440 | **unnumbered** — `\paragraph{A simple sofic envelope.}` |

The remaining 56 are body prose. That is where the debts are.

---

## 2. Classification of every body citation

**attribution** — prior work, priority, context; carries no mathematical weight.
**formalized** — the fact is cited *and* proved in-repo.
**DEBT** — a real unformalized load-bearing input.

### 2.1 Section 1 (`Introduction`, `Relation to prior work`) — all attribution

| line | key(s) | role |
|---|---|---|
| 133, 134, 140, 148 | `Shulman`, `Schafhauser`, `GKEMP` | attribution — naming the MF conjecture and its state of the art |
| 137 | `CDE` | attribution at the citation; the fact (LEF ⇒ MF) is separately **formalized**, `LocallyFiniteMF.isOperatorMF_of_isLEF` |
| 138 | `TWW` | attribution — survey sentence "by quasidiagonality, all amenable groups". Not used; see §3.1 for the two sites that *are* |
| 143, 145, 147 | `BK`, `CDE`, `HT`, `MIPRE`, `FGH` | attribution — history of the Blackadar–Kirchberg question |
| 152–160 | `Th`, `DGLT`, `LuO`, `BDL`, `OAI`, `FFF`, `KT` | attribution — the Schatten-`p` programme and the nonsofic results |
| 176, 184 | `CDE`, `Shulman`, `BDL`, `BK` | attribution — provenance of the MF definition adopted |
| 220, 222 | `GKEMP`, `MdlS` | attribution — stronger conventions not adopted here |
| 334–336 | `OAI`, `KT`, `Kun16`, `KT19`, `AlekseevThom` | attribution — closest analogues |
| 345–352 | `SlofstraProfile`, `SlofstraCorrelations`, `SlofstraVidick`, `Fritz` | attribution — priority for Clifford/shift/HNN, invisible quotients, negative-eigenspace compression |
| 364–375 | `DGLT`, `GR`, `Gl19`, `BekkaAmenable`, `BekkaValette`, `Dadarlat`, `CDE` | attribution — technique provenance |
| 424 | `Loring` | attribution — "the following lifting facts are standard; see Loring". The lifting facts themselves are `lem:lift`, badged and proved |

### 2.2 Numbered environments

| line | key(s) | class | note |
|---|---|---|---|
| 856 | `FFF` | attribution | `rem:ff-realization` is explicitly a report of a personal communication and an open suggestion; the remark asserts nothing the manuscript uses |
| 876 | `BHV` | **formalized** | property (T) of the affine group; the same sentence says "Section~\ref{sec:group} also proves this from the presentation used below" — `LiteralBaseP13PropertyTBridge.manuscriptBaseHasKazhdanPropertyT` |
| 1479–1482 | `CRW`, `CLV`, `BHV` | **formalized** | `rem:classical-base`; the remark itself says "the proofs here are independent of these sources, and so is the identification", and carries `LiteralBaseCompleteness.baseAffineEquiv` |
| 1371, 1373 | `Ozawa`, `NetzerThom` | attribution | inside `prop:literal-base-T`'s proof, but as "Certificates of this kind go back to …" — a provenance sentence appended after the SOS certificate has already been exhibited and machine-checked |
| 2540–2541 | `SlofstraCorrelations`, `NST` | attribution | `def:radical`'s closing sentence is "This is the operator-norm analogue of …". The definition is `manuscriptMFRadical` |
| 3549 | `Rabin58` | **DEBT** | see §3.6 |

### 2.3 Body prose, non-attribution

| line | key(s) | class | note |
|---|---|---|---|
| 1013, 1017, 1020 | `BK`, `FGH`, `MdlS` | attribution | "Every MF algebra is stably finite [BK]" is immediately superseded — "Here stable finiteness comes from the faithful canonical trace, independently of the MF question" (`lem:faithfultrace`, badged) |
| 1039 | `Lance` | **DEBT** | see §3.5 |
| 1070 | `ElekSzabo` | **formalized (badge owed)** | see §3.7 |
| 2249 | `BDL` | attribution | terminological — "In the terminology of [BDL, Def. 1.2], … *Deligne type*" |
| **2473** | `TWW` | **DEBT** | see §3.1 |
| **3275** | *(none — uncited)* | **DEBT** | see §3.2 |
| 3368, 3417 | `ElekSzabo` | **formalized (badge owed)** | see §3.7 |
| 3404 | `Malcev` | attribution | hedged as "compare Mal'cev's theorem"; the congruence-separation argument is given in full in the same sentence, and the paragraph carries `literalWitness_locallyFiniteKernel_nonMF` |
| **3425–3427** | `GHW`, `KWPermanence`, `KWExact` | **DEBT ×3** | see §3.4 |
| **3442** | `ElekSzaboHyper` | **DEBT** | see §3.3 |
| 3544, 3553 | `Rabin58` | **DEBT** (same as 3549) | see §3.6 |
| **3587, 3597** | `Neumann37` | **DEBT, closable by amendment** | see §3.8 |
| 3644 | `AlekseevThom` | attribution | quoting an open problem to say it is *not* what is proved here |
| 3681 | `FFF` | attribution | priority for the torsion-free nonsofic example, in a Questions section |
| **2386–2387** | *(none — uncited)* | **DEBT, already discharged in Lean** | see §3.9 |

---

## 3. The load-bearing unformalized items

Seven live debts, in descending order of what collapses.

### 3.1 `TWW` — the sharpness paragraph  *(inventory row 13)* — **CLOSED 2026-08-17**

**Status: executed.** The recommendation at the foot of this subsection has been
carried out. The sentence below is no longer in the manuscript, the paragraph now
routes through the exhibited monomial models instead of through amenability, and
it carries the badge this subsection asked for. `TWW` survives in the manuscript
only as the intro attribution sentence (grep `amenable groups are MF`), which is
credit, not a step in an argument. **The corpus has no live `TWW` inference.**
The rest of the subsection is kept as the record of what was owed and why the
replacement is sound; the paragraph-level facts in it that have since changed are
corrected in place below.

**Sentence, as it stood** (grep `hence MF by`; deleted 2026-08-17):

> The realized quotient is a subgroup of this amenable group and is therefore
> amenable, hence MF by \cite{TWW}.

**Environment:** body prose, `\paragraph{Sharpness of the Kazhdan hypothesis.}`,
after `\end{proof}` of `thm:cyclic`. It carried **no badge**, so no gate saw it;
it does now.

**What is owed:** amenable ⇒ MF, i.e. Tikuisis–White–Winter quasidiagonality.
Lean state: `Sofic/CliffordBSAmenable.lean:84` carries it as an assumed
structure, `AmenableImpliesMF`, consumed by two unbadged theorems.

**What it costs to formalize as printed:** out of reach. Quasidiagonality is
not expressible at the pinned Mathlib — there are no C\*-tensor products and no
nuclearity (`Analysis/NuclearityAmenability.lean` calls this a foundations gap;
`Analysis/CStarExactness.lean` says exactness "is not expressible in this
library"). TWW itself is a Annals-scale theorem on top of that.

**What it costs to formalize the paragraph's actual conclusion:** nothing more —
it is written, compiled and certified. `GroupApproximation/Sofic/CliffordBSAmenableMF.lean`
proves it without TWW. **Corrected 2026-08-17:** this paragraph used to read
"1,579 lines, untracked, wired into `GroupApproximation.lean:759`, reported to
have 21 compile errors", and that description outlived the facts by a day. The
module is 1,635 lines, tracked and clean, imported at `GroupApproximation.lean:948`,
and **present on `origin/verified` together with its root-import line** — and
promotion to `verified` requires the exact successful `Build and audit` job of a
push run, so it compiles and passes the kernel audit. The assessment below was
written before that was known and holds independently of it:

* The paragraph's conclusion is `w_BS ∉ Rad_MF(E_BS)` — an intersection of
  kernels. One corona representation that does not kill the mark suffices; no
  injectivity, hence no MF statement about any group, is required. The file
  says so in its docstring and its endpoint theorems match.
* The model: coordinates `Fin 2 × ZMod M` with `M = 2m+3` odd; `γ₀ =
  diag((-1)^s ζ^k)`, whose spectrum is exactly the `2M`-th roots of unity each
  once (since `M` is odd, `{2k} ∪ {2k+M}` exhausts `ℤ/2M`); `t` the permutation
  `(s,k) ↦ (s, 2k + b_s)`, a permutation because doubling is invertible mod an
  odd modulus.
* The defect is real and vanishes. `defectPhase m = ζ^{m+1}` and
  `(m+1)·2π/M = π − π/M`, so `defectPhase = −e^{−iπ/M}` (`defectPhase_eq`) and
  `‖defectPhase + 1‖ = 2 sin(π/2M) ≤ 2π/M` (`norm_defectPhase_add_one_le`,
  a loose but valid bound), giving `eventually_defect_lt` along the cofinite
  filter — exactly the filter the corona quotients by.
* The mark is exactly `−1`. With `D = 2^{−1/2}(X+Z)` and `ZDZ = 2^{−1/2}(Z−X)`,
  both self-adjoint unitaries, `D·(ZDZ) = XZ` and `(ZDZ)·D = −XZ`, so the
  commutator is `(XZ)² = −1`. Being a scalar, it satisfies the four relators
  making the mark a central involution *exactly*. Six of seven relators hold
  exactly; only the doubling relator carries the `O(1/m)` defect.
* The presented group is the manuscript's own object: `coronaRep` is built by
  `PresentedGroup.toGroup` over `CyclicBaseLEFObstruction.relators`, the seven
  printed relators, and `mark` is the repo's `markedWord`. No new group is
  introduced.
* The impossibility side is respected rather than ignored: `CyclicBaseLEFObstruction`
  proves no *exact* finite model can work and `Analysis/AmenableQuasidiagonal`
  proves *permutation* models are exact-or-useless, which is why the models are
  monomial and the whole approximation lives in the phases. `realizedQuotient_elementary_routes_closed`
  states the four failures in one theorem.
* No `sorry`, no `axiom`, no `native_decide` in the file.

The one thing to be clear about: the file discharges the paragraph's
*conclusion*, not its *printed sentence*. `isOperatorMF_subgroup_CliffordBS`
stays conditional, and the file's own docstring says so.

**Recommendation: PROVE — the proof exists; fix the compile errors and rewrite
the sentence. DONE 2026-08-17.** There were no compile errors left to fix: the
module had entered the closure and reached `verified` while this subsection still
described it as broken, which is why the item read as open for a day longer than
it was. The paragraph was rewritten and badged; the text that landed differs from
the draft below in routing the reader back to the Clifford attachment already
built in the preceding proof, rather than describing the models afresh, and in
not restating the `O(1/M)` defect bound, which is an artifact of the formalization
rather than of the argument. Draft as proposed:

> The realized Clifford quotient in Theorem~\ref{thm:C} is amenable, and its
> marked word is the nontrivial Clifford sign. More is true, and does not need
> amenability: an explicit sequence of finite monomial matrix models satisfies
> six of the seven printed relators exactly and the doubling relator with
> defect `O(1/M)`, while the marked word is the scalar `−1` in every model.
> Its class in the norm matrix corona is therefore nontrivial, so
> `w_BS ∉ Rad_MF(E_BS)` and property (T) cannot be omitted from the
> central-sign criterion.
> `\leanverified{Sofic/CliffordBSAmenableMF}{GroupApproximation.CliffordBSAmenableMF.manuscriptSharpnessOfKazhdanHypothesis}`

**If dropped instead:** the sharpness paragraph goes, and with it the
manuscript's only evidence that the Kazhdan hypothesis in `thm:sign-criterion`
is not decorative. `thm:C` survives (it is badged and independent); what is
lost is the sentence "property~\textup{(T)} cannot be omitted".

### 3.2 `TWW` again — uncited, at the saturation discussion  *(not in the inventory)*

**Sentence** (L3275, grep `homomorphism to any countable`):

> A group as in (2) admits no nontrivial finite-dimensional unitary
> representation, no nontrivial MF quotient, and no nontrivial homomorphism to
> any countable residually finite or **amenable** group.

**Environment:** body prose, immediately after `\end{proof}` of `thm:saturation`.
Unbadged. **Carries no `\cite` at all**, which is why it appears in no citation
audit and in no row of `NON_MF_CONDITIONAL_INVENTORY.md`.

**What is owed:** the "amenable" clause needs *countable amenable ⇒ MF* in full
generality — the general theorem, not one group's corona. Nothing in the repo
touches it; `CliffordBSAmenableMF`'s docstring flags this site explicitly and
disclaims covering it.

The "residually finite" clause is fine: `OperatorMFPositiveControls.isOperatorMF_of_residuallyFinite`
plus `manuscriptDefectSaturation`.

**Recommendation: DROP the word.** Delete `or amenable`. Cost: one word. Loss:
the sentence keeps its finite-dimensional, MF-quotient and residually-finite
clauses, all three formalized, and loses a fourth that was never used
downstream. Formalizing instead means TWW, which is out of reach at the pin
(§3.1).

### 3.3 `ElekSzaboHyper` — the simple sofic envelope

**Sentence** (L3442, inside the `\begin{proof}` at L3440 of the unnumbered claim
at L3432–3438):

> By Elek--Szab\'o, every countable sofic group embeds in a countable simple
> sofic group \cite[Theorem~1]{ElekSzaboHyper}.

**Environment:** proof of an **unnumbered** `\paragraph{A simple sofic envelope.}`
claim. **No badge anywhere in the paragraph.** Not in the JSON (unnumbered),
not in the inventory.

**Lean state, and it is good:** `Sofic/SimpleSoficEnvelope.lean` (193 lines;
*this said "untracked" and that was wrong by 2026-08-17 — it is tracked, inside
the root import closure, and on `verified`*) proves steps 2–4 of the printed four-step argument for the
manuscript's actual witness `W` and mark `ζ`, plus the "Equivalently" as a
genuine biconditional — and assumes nothing: it proves the implication *from a
concrete envelope*. `Sofic/SoficEnvelopeExistence.lean` (535 lines as of 2026-08-17, not 503;
likewise tracked, in the closure, and on `verified`)
does moves 1 and 3 of the classical proof in full and reduces the entire
remaining debt to one statement:

> for every `δ > 0` there is a `K` such that whenever `σ` is a permutation of a
> finite set `Ω` with `|supp σ| ≥ δ|Ω|`, every even permutation of `Ω` is a
> product of at most `K` conjugates of `σ` and `σ⁻¹`.

Bounded normal generation of finite symmetric groups, with `K` independent of
`Ω`. That is the only thing between the repo and the citation.

**Cost:** one self-contained finite-combinatorics theorem, no analysis, no
foundations gap. Real work (this is the combinatorial heart of Elek–Szabó) but
bounded and clearly scoped — the only genuinely *closable* hard citation in the
manuscript.

**Recommendation: PROVE.** Rank it after §3.1 and §3.8, before §3.6.
**If dropped:** the paragraph goes and the manuscript loses its "countable
simple sofic group with full MF radical" example. Nothing else depends on it.
An intermediate is available and honest: restate the paragraph conditionally —
"if `S` is a countable simple sofic group containing `W`, then
`Rad_MF(S) = S`" — and badge it with `SimpleSoficEnvelope`, which proves exactly
that. That converts a black box into a printed hypothesis at zero mathematical
cost.

### 3.4 `GHW` + `KWPermanence` + `KWExact` — the exact stably finite algebra

**Sentences** (L3423–3427, grep `Exact groups are closed under extensions`):

> the locally finite lamp kernel is amenable and hence exact, while the linear
> group `V ≤ GL₄(ℚ)` is exact \cite{GHW}. Exact groups are closed under
> extensions \cite{KWPermanence}, so `W` is exact; for discrete groups this is
> equivalent to exactness of the reduced group algebra \cite{KWExact}.

**Environment:** body prose, unnumbered `\paragraph{An exact stably finite
non-MF algebra.}`. **No badge.** Three literature inputs in one four-sentence
deduction — the densest debt in the manuscript.

**Lean state:** `Analysis/ExactnessPermanence.lean` tabulates these as links
E.2/E.3/E.4 and reports all three **missing**; E.2 (Guentner–Higson–Weinberger,
linear groups are exact) is called "research-scale"; E.4 (group-exact ⇔
C\*-exact) is "not statable today". Only E.1's group half is proved: property A
for the manuscript's own lamp kernel (`hasPropertyA_cliffordLamp`, twice, once
via local finiteness and once via Day). `Analysis/CStarExactness.lean`
deliberately defines `IsNuclearlyEmbeddable` rather than `IsExact` and states
that Kirchberg's equivalence is not formalized and that nothing in the
repository proves or assumes `Cred(W)` is nuclearly embeddable.

**Cost:** three separate literature theorems, one of them research-scale, on top
of a foundations gap (no C\*-tensor products at the pin). Not closable in this
manuscript's lifetime.

**Recommendation: DROP the paragraph.** Loss, stated concretely: the claim
"`Cred(W)` is exact, has a faithful tracial state, is stably finite, and is not
MF" — i.e. the *exact* separable stably finite non-MF C\*-algebra. The trace
and stable finiteness survive (`lem:faithfultrace`), and the non-MF half
survives (`thm:E` route), so the salvageable residue is one sentence:

> The same witness gives a separable stably finite non-MF example: `Cred(W)`
> carries a faithful trace and is stably finite by
> Lemma~\ref{lem:faithfultrace}, and an MF embedding would restrict to a
> faithful norm-corona model of the canonical group unitaries, contradicting
> that `W` is not MF.

That sentence has zero literature inputs. The word *exact* is what has to go,
and with it the three citations.

### 3.5 `Lance` — nonnuclearity of `Cred(E)`

**Sentence** (L1035–1039, grep `is not nuclear`):

> the canonical map `B → E` is injective, so `E` contains an infinite Kazhdan
> group and is nonamenable, whence `Cred(E)` is not nuclear \cite{Lance}.

**Environment:** body prose, after `thm:D`'s proof. Unbadged. `thm:D` itself is
`exact` in the JSON and does not mention nuclearity, so the printed theorem is
unaffected.

**Lean state:** the *first* half is proved —
`Analysis/NuclearityAmenability.lean:211 base_not_isAmenable` and `:231
not_isAmenable_of_base_embeds`. The second half is not proved and is not
assumed; the module docstring calls Lance's theorem "UNSTATABLE, a foundations
gap", nuclearity being absent from the pinned Mathlib, and flags the paragraph
as non-load-bearing.

**Recommendation: DROP the nonnuclearity clause, keep the amenability clause.**
Replacement:

> The canonical map `B → E` is injective, so `E` contains an infinite Kazhdan
> group and is nonamenable.
> `\leanverified{Analysis/NuclearityAmenability}{GroupApproximation.NuclearityAmenability.not_isAmenable_of_base_embeds}`
> The nuclear form of the Blackadar–Kirchberg problem — whether every stably
> finite separable nuclear C\*-algebra is quasidiagonal — is not addressed
> here and remains open.

Loss: the assertion that `Cred(E)` is *not* nuclear. Nothing downstream uses
it; its only function was to explain why the nuclear form of the BK problem is
untouched, which the replacement says directly.

### 3.6 `Rabin58` — undecidability  *(inventory row 1)*

> **SUPERSEDED 2026-08-17. This debt is closed, and the section below is kept
> only as the record of what it looked like open.** Every factual claim in it
> about the tree or the manuscript has since become false, checked one at a
> time:
>
> * The quoted sentence — "By the effective form of the Adian--Rabin
>   construction \cite{Rabin58}, the set of finite presentations of non-MF
>   groups is not even recursively enumerable" — **occurs zero times** in
>   `non_mf_groups_exist.tex`. So do the three cited line numbers.
>   `\cite{Rabin58}` now has exactly one body site, framing prose before the
>   corollary, where it is priority attribution and not a step.
> * "Every undecidability theorem is conditional" is false.
>   `Computability.not_computablePred_wordProblemPred` proves the word problem
>   on presentation codes undecidable with no hypothesis, and
>   `Computability.operatorMF_recognition_not_computable` carries it to MF
>   recognition. The negative side went the same way:
>   `WordProblemRE.rePred_wordProblemPred` makes the word problem recursively
>   enumerable, and `WordProblemRE.operatorMF_negative_side_not_re` concludes
>   that no enumeration lists the codes of non-MF groups. All four take no
>   argument and all four are badged at the corollary.
> * The subheading's "the JSON's one declared input" is false; see § 0.
> * The **6000–11000 line** estimate, and "it includes Novikov--Boone", are
>   both moot rather than wrong: the route taken was Aanderaa--Cohen modular
>   machines, and the closing work was coordinates — writing the halting word
>   as raw data in the code's own numbering, proving the
>   configuration-to-word map primitive recursive, and matching triviality
>   with halting.
> * **The recommendation below is retracted.** "KEEP, restated as conditional"
>   and the `\leanconditional` proposal describe a corollary that no longer
>   exists. `\leanconditional` is still used zero times in the manuscript, and
>   now for the better reason.
>
> The estimate is the part worth keeping in view. A section that priced this
> debt in five figures of Lean and named it the manuscript's least tractable
> citation was reporting the cost of the route it could see, not the cost of
> the problem.

**Sentences** (L3544 body, L3549 inside `cor:undecidable`, L3553 body). The
in-environment one:

> By the effective form of the Adian--Rabin construction \cite{Rabin58}, the set
> of finite presentations of non-MF groups is not even recursively enumerable.

**Environment:** `corollary[cor:undecidable]`, plus framing prose on both sides.
This is the **only** debt the manuscript's own machinery already knows about,
and the surrounding prose already says the construction "is quoted here and used
nowhere else."

**Lean state:** `Computability/MarkovMFConsequences.lean:55` carries
`structure AdianRabinReduction` (transform + computability + correctness) and
every undecidability theorem is conditional on it plus an assumed
`¬ComputablePred sourceProperty`. Its *hypotheses* are proved unconditionally:
`AdianRabinMarkovProperty.lean:444 operatorMF_isMarkovProperty` (Markov, with
positive witness `PUnit` and forbidden witness `MarkedGroup`), plus Post's
theorem at `:482`. `RabinConstruction.lean` proves the collapse half; the
embedding half is absent, not assumed.

**Cost:** the module's own D1–D6 ledger puts it at **6000–11000 lines**, and it
is explicit that there is no partial retraction — the sentence names the single
input the whole corollary rests on, and the effective/`not r.e.` refinement is
worth about 5% of the total. It includes Novikov–Boone.

**Recommendation: KEEP, restated as conditional.** This is the one place where
dropping costs more than the debt: deleting `cor:undecidable` removes the entire
undecidability subsection, which is the manuscript's headline application of
`thm:A` being hereditary. The honest move is remediation item 1 of the
conditional inventory — use `\leanconditional` (it exists, is checked by
`check_non_mf_refs.py`, and is used **zero** times in the manuscript) over
`MarkovMFConsequences.operatorMF_negative_side_not_re`, so that the one
acknowledged black box is also the one machine-visible black box.

### 3.7 `ElekSzabo` — soficity by amenable extension  ***DEBT NOW CLOSED IN LEAN, BADGE OWED***

Three sites: L1070 (intro summary of `thm:E`), L3368 (inside
`\begin{proof}[Proof of Theorem~\ref{thm:E}]`), L3417 (`\paragraph{Extensions by
$\Z$.}`).

Site L3368 is attribution as printed — the proof does the `ZMod N` truncation
argument itself and only then says "This is the `ℤ`-extension case of the
Elek–Szabó amenable-extension theorem", and the concrete case is proved by the
tracked `Sofic/SoficIntegerExtension.lean`. Sites L1070 and L3417 are genuine
invocations of the general theorem.

**All three are now covered.** `Sofic/SoficByAmenablePermanence.lean` (828
lines, untracked, wired in at `GroupApproximation.lean:737`) proves
*sofic-by-amenable is sofic* outright — no splitting, arbitrary amenable
quotient, no countability premise — by the Elek–Szabó cocycle-plus-Følner
argument, with the Følner sets produced from the repository's own
invariant-mean definition via its own Tarski–Hall theorem. Its docstring:
"There is no literature input anywhere in this file." The four packaging
corollaries include `isSofic_of_isSofic_of_int_quotient`, which is exactly the
non-split shape L3417 uses.

**Recommendation: badge it.** Add `\leanverified{Sofic/SoficByAmenablePermanence}{GroupApproximation.SoficByAmenablePermanence.isSofic_of_isSofic_ker_of_isAmenable}`
at L3417 and keep `\cite{ElekSzabo}` as attribution. Zero mathematical cost;
this converts three citations from debt to attribution.

### 3.8 `Neumann37` — the continuum family  *(inventory row 2)*

**Sentences** (L3587, L3597):

> pairing `E` with the continuum of pairwise nonisomorphic **two-generator**
> groups of B.~H.~Neumann \cite{Neumann37} yields `2^{ℵ₀}` pairwise
> nonisomorphic finitely generated non-MF groups … Neumann's family is quoted,
> not reproved \cite{Neumann37}.

**Environment:** body prose, badged `ContinuumMultiplicity.manuscriptContinuumMultiplicity`
— which takes the family as a **hypothesis binder** (`hfam`, `hcard`). That is
row 2 and it is correctly diagnosed.

**But the repo has since discharged it, with one caveat.**
`Monsters/NeumannContinuum.lean:186 neumann_continuum_of_finitely_generated_groups`
proves, unconditionally, that there is a continuum of pairwise nonisomorphic
**finitely generated** groups — via a lamplighter `A₅ ≀_{F₂/H} F₂`, not
Neumann's subdirect products of alternating groups — and feeds
`ContinuumMultiplicity.manuscriptContinuumMultiplicityUnconditional`. The
caveat is exactly one word: the repo's family is finitely generated, the printed
sentence says *two-generator*.

**Recommendation: PROVE by amendment.** Delete "two-generator", repoint the
badge at `manuscriptContinuumMultiplicityUnconditional`, and demote
`\cite{Neumann37}` to priority attribution ("Neumann first produced such a
family, with two generators"). Cost: one sentence edit. Loss: the adjective
*two-generator*, which the module docstring confirms "is not used anywhere in
the manuscript's deduction". This is the cheapest full closure available.

### 3.9 The Zariski chain condition — uncited, and also already closed

**Sentence** (L2386–2387, grep `The chain condition for Zariski-closed`):

> The chain condition for Zariski-closed subgroups of `GL(V)` is classical and
> is quoted here.

**Environment:** `remark[rem:chaincondition]`, adjacent to
`\leanverified{Criterion/ClosedEnvelopeCompression}{…manuscriptEnvelopeCompressionBlind}`.
**Carries no `\cite`** — a literature input announced in prose with no
bibliography entry, invisible to any citation-based audit. This is inventory
row 5.

**Lean state:** discharged. `Algebra/ZariskiDescendingChain.lean:131` proves
`instance wellFoundedLT_isZClosedSubgroup` from the Hilbert basis theorem,
`:137 zariski_dcc_closedSubgroups` states the DCC, and `:282
manuscriptZariskiEnvelopeCompressionBlind` is the manuscript's displayed
identity **with no instance binder left**, with `:309
manuscriptZariskiClosureOfRepresentation` giving the representation form. The
module docstring: "Every step is proved from Mathlib; no hypothesis stands in
for mathematics."

**Recommendation: delete the quoting sentence and repoint the badge** at
`ZariskiDescendingChain.manuscriptZariskiClosureOfRepresentation`. Cost: two
lines of TeX.

---

## 4. What contradicts the inventory and the brief

1. **"Exactly one claim carries `external_inputs`" is true and misleading.**
   The JSON covers 56 numbered environments *(54 as of 2026-08-17, and the
   `external_inputs` list is now empty — § 0)*. Five of the seven live literature
   debts (§3.1, §3.2, §3.3, §3.4, §3.5) live in unnumbered `\paragraph{}`
   blocks that the JSON cannot represent, and a sixth (§3.9) is not a citation.
   A manuscript with zero unformalized literature inputs cannot be certified by
   reading `NON_MF_NUMBERED_CLAIMS.json`.

2. **There is a second TWW site, and the inventory does not have it.** Row 13's
   anchor is only `\paragraph{Sharpness of the Kazhdan hypothesis.}`. L3275
   ("no nontrivial homomorphism to any countable residually finite or amenable
   group") needs the *general* theorem, is uncited, and is unbadged. It is
   strictly harder than row 13 and strictly cheaper to fix (§3.2).

3. **Row 5 is discharged.** `ClosedEnvelopeCompression.lean`'s docstring ("the
   external input … stays external") is stale; `ZariskiDescendingChain.lean`
   removes it. The manuscript sentence quoting it as classical should go.
   *(2026-08-17: both halves are done. The docstring now states the two things
   the badge carries and quotes nothing as external, and the manuscript
   sentence occurs zero times.)*

4. **Row 2 is discharged up to one adjective.** `ContinuumFamilyCriterion.lean`'s
   docstring ("not proved anywhere in this development. This file does not prove
   it either") is stale for the same reason — `NeumannContinuum.lean` imports
   that file and discharges its obligation.
   *(2026-08-17: the docstring was refreshed and now says "**It is no longer
   quoted**", naming the discharging declaration. The adjective is still in the
   manuscript — wave 0 item 3 below is the one wave-0 item still outstanding.)*

5. **`ElekSzabo` is no longer a debt at all** (§3.7), which no inventory row
   records because it was never a badged claim.

6. **Two unbadged unnumbered paragraphs carry four citations between them and
   no Lean at all**: `\paragraph{An exact stably finite non-MF algebra.}` and
   `\paragraph{A simple sofic envelope.}`. They are outside the JSON, outside
   the inventory, and outside every gate.

7. **The brief's citation frequencies were off**, and `Kropholler` is not in
   this manuscript (body or bibliography) — see §0. All 45 bibitems are cited;
   there are no orphan entries.

---

## 5. Prove-or-drop, in one table

| # | Input | Sites | Verdict | Cost | Concrete loss if dropped |
|---|---|---|---|---|---|
| 3.7 | `ElekSzabo` | L1070, L3368, L3417 | **PROVE — done** | badge edits only | — |
| 3.9 | Zariski DCC (uncited) | L2386 | **PROVE — done** | 2 lines TeX | — |
| 3.8 | `Neumann37` | L3587, L3597 | **PROVE by amendment** | 1 sentence TeX | the adjective *two-generator* |
| 3.1 | `TWW` (sharpness) | grep `hence MF by` | **PROVE — DONE 2026-08-17** | no compile errors remained; module was already on `verified`.  1 paragraph rewritten and badged | "property (T) cannot be omitted from the central-sign criterion" |
| 3.2 | `TWW` (general) | grep `or amenable` | **DROP — DONE** | 1 word | the clause "or amenable" in one sentence, already gone from the tex |
| 3.3 | `ElekSzaboHyper` | L3442 | **PROVE**, else restate conditionally | one bounded-normal-generation theorem for finite symmetric groups | the simple sofic group with full MF radical |
| 3.5 | `Lance` | L1039 | **DROP** | 1 clause | "`Cred(E)` is not nuclear" |
| 3.4 | `GHW`+`KWPermanence`+`KWExact` | L3425–3427 | **DROP** | 1 paragraph rewritten to 1 sentence | the word *exact* in "exact stably finite non-MF algebra" |
| 3.6 | `Rabin58` | one body site (attribution only) | ~~KEEP, mark conditional~~ **PROVED 2026-08-17** | — | — |

---

## 6. Ordered plan to zero unformalized literature inputs

**Wave 0 — free, no Lean (half a day).** Everything here is already proved.

*Status 2026-08-17: items 1, 2, 4 and 5 are done — verified against the tex and
the two docstrings, not inferred. Item 3 is the only one outstanding, and
`\cite{Neumann37}` with its "two-generator" adjective is still in the
manuscript.*

1. Badge L3417 with `SoficByAmenablePermanence.isSofic_of_isSofic_ker_of_isAmenable`;
   keep `\cite{ElekSzabo}` as attribution. (§3.7)
2. Delete L2386–2387 and repoint `rem:chaincondition`'s third badge at
   `ZariskiDescendingChain.manuscriptZariskiClosureOfRepresentation`. (§3.9)
3. Delete "two-generator" at L3587, repoint the badge at
   `manuscriptContinuumMultiplicityUnconditional`, demote `\cite{Neumann37}` to
   priority attribution. (§3.8)
4. Delete "or amenable" at L3275. (§3.2)
5. Refresh the stale docstrings in `ContinuumFamilyCriterion.lean:8-11` and
   `ClosedEnvelopeCompression.lean:12`, which now assert the opposite of the
   truth.

   *After wave 0: four debts remain (§3.1, §3.3, §3.4, §3.5, §3.6 — five
   sentences, six citations).*

**Wave 1 — drops (one day).** Each removes a debt outright.

6. Rewrite `\paragraph{An exact stably finite non-MF algebra.}` to the
   literature-free residue in §3.4; the three citations go with it.
7. Rewrite the nonnuclearity clause at L1035–1039 per §3.5, badging
   `not_isAmenable_of_base_embeds`.

**Wave 2 — the one that needs Lean debugging (days, not weeks).**

8. ~~Fix the 21 compile errors in `Sofic/CliffordBSAmenableMF.lean` and land it.~~
   **DONE 2026-08-17, and there was nothing to fix** — the module reached the root
   import closure and then `origin/verified` while this list still described it as
   broken. Check `git cat-file -e origin/verified:<path>` before believing any
   claim here that a module is uncompiled.
9. ~~Rewrite `\paragraph{Sharpness of the Kazhdan hypothesis.}` per §3.1 and badge
   `manuscriptSharpnessOfKazhdanHypothesis`.~~ **DONE 2026-08-17.** Leave
   `CliffordBSAmenable.isOperatorMF_subgroup_CliffordBS` in place, unbadged and
   unreferenced — it is a clean conditional and nothing cites it; likewise the six
   `tww` binders in `Sofic/CliffordBSPrintedRoute.lean`, which are the
   formalization of the *printed* route and are deliberately kept as such.

**Wave 3 — the last closable citation (a real but bounded project).**

10. Prove bounded normal generation of finite symmetric groups (§3.3), feed it
    to `SoficEnvelopeExistence`, compose moves 1 and 3, badge
    `\paragraph{A simple sofic envelope.}`.
11. If wave 3 is not attempted, do the honest intermediate instead: restate the
    paragraph as an implication from a concrete envelope and badge
    `SimpleSoficEnvelope`. That is *also* zero unformalized inputs — the
    hypothesis becomes printed rather than quoted.

**Terminal state.** ~~After waves 0–3, the manuscript's only unformalized
literature input is Adian–Rabin at `cor:undecidable`, printed as conditional,
marked `\leanconditional`, and visible to `check_non_mf_refs.py`.~~

*Revised 2026-08-17.* The terminal state this paragraph describes was overtaken
from the other end: Adian–Rabin was proved rather than marked, so the residue
after waves 0–3 is **zero** declared inputs, not one. `\leanconditional`
remains unused and there is no longer a candidate for it. What the paragraph
got right is the shape of the argument — that a manifest reporting no external
inputs certifies nothing by itself — and § 0 now makes that point against an
empty list instead of a singleton.

**Gate work owed regardless.** No gate reads `\cite`. A ten-line addition to
`check_non_mf_refs.py` — flag any `\cite` outside `\subsection*{Relation to
prior work}`, the introduction, and an explicit attribution allowlist, unless
the enclosing block also carries a `\leanverified` or `\leanconditional` badge —
would have found every item in §3 automatically, including the two uncited ones
if the same pass also greps for `classical`, `quoted here`, `standard`, and
`by [A-Z]`. Without it, this audit has to be redone by hand after every edit.
