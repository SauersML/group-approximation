# sk-fp-sofic-a: finitely presented simple Kazhdan sofic groups: status, a firewall, and what the note should say

Lane `sk-fp-sofic-a`, 2026-09-13. Line numbers refer to `sk/manuscript-disk-1646.tex` (md5 7b3dc4ec…).

## 1. The question and its status

**Question.** Is there a finitely presented infinite simple group with property (T) that is sofic, or
hyperlinear?

It is the natural next question after the note. The note's groups `G_X` are LEF, and a finitely
presented LEF group is residually finite, so no `G_X` is finitely presented.

**Status: OPEN** (bounded check, stated).
- The graph records it as `hyperlinear-fp-infinite-simple-kazhdan-group` (OPEN). The weaker question
  without (T), `hyperlinear-fp-infinite-simple-group` (OPEN), cites Salo arXiv:2103.15505 for the
  open soficity of Thompson's `V` and records arXiv abstract searches that returned no example.
- `research/artifacts/ex-open-status-2026-09-12.md`, row 3, has the same verdict.
- Three web searches by this lane on 2026-09-13 found no claim of a finitely presented infinite simple
  sofic or hyperlinear group:
  - "finitely presented infinite simple group sofic open problem";
  - "finitely presented simple group property (T) hyperlinear OR sofic arXiv 2026";
  - "Kac-Moody lattice sofic Caprace Rémy simple Kazhdan soficity".
- Among the hits, Fournier-Facio arXiv:2608.02025 and Ersoy arXiv:2604.19174 concern nonsofic
  groups. Becker--Lubotzky arXiv:1809.00632 is on stability and (T). arXiv:2512.09180 ("Stability,
  approximable quotients, and higher property (T)") was not opened.
- This is not a complete literature verification.

**Candidates recorded on main, as recorded and not re-verified here.**

| Candidate | fp, simple, (T) | Soficity |
|---|---|---|
| Kac--Moody lattices `S_q`, type (2,4,6), `q >= 4` | `km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4` (citation assembly PASS, ex-review part 13 §13.4) | gate `km-246-lattice-is-sofic`, OPEN |
| Titz Mite--Witzel kernels | recorded in `hyperlinear-fp-infinite-simple-kazhdan-group` | open both ways |
| binary Leavitt unit group | recorded | nonsofic (`fp-simple-nonsofic-group`); hyperlinear OPEN |
| ring route `EL_n(LC(Ω, F_q) ⋊ Z^2)/Z`, `Ω` a quantum rigid free minimal SFT | ring fp OPEN for Labbé's shift; group fp gate `rigid-sft-elementary-group-mod-centre-is-fp` OPEN | only `F_q`-linear soficity (`free-minimal-subshift-elementary-groups-are-simple-kazhdan`) |

## 2. What this lane adds: a firewall for linear models

Node `gap-sofic-approximations-are-local-embeddings` (ESTABLISHED, unreviewed), route
`gap-sofic-approximations-are-local-embeddings-proof`.

**Theorem.** A countable group is LEF iff it has a sofic approximation inside permutation groups
`H_N` whose nontrivial elements all have fixed-point ratio at most `1 - δ`, for one fixed `δ > 0`.

**Gap families.**
- Affine maps of a finite group acting on it (so `GL_m(F_q)` and `AGL_m(F_q)` on `F_q^m`, and
  automorphisms of finite groups): gap `1/2`. A fixed-point set is a coset of a subgroup.
- `PGL_m(F_q)` on `P^(m-1)(F_q)`: gap `1/2`, by counting lines in eigenspaces.

**Consequences.**
- A finitely presented infinite simple group has no sofic approximation through linear, affine or
  projective linear maps of finite vector spaces.
- In every sofic approximation of such a group, for all large `N` some relator defect is a
  nontrivial permutation with fixed-point ratio tending to `1`.
- So the soficity gate (c) of `sofic-fp-simple-kazhdan-group-from-fp-simple-ring` cannot be met by
  `F_q`-linear or projective models: rank models do not upgrade to soficity along the natural
  actions. The heuristic recorded there ("rank defect `r` becomes Hamming defect `1 - q^(-O(r))`") is
  now a theorem in exact form.
- For the note: the models of `G_X` in `GL_(3N)(F_2)` acting on vectors are automatically local
  embeddings. LEF is the entire content that such models carry.

No novelty is claimed. This is the standard minimum-distance observation plus "finitely presented
LEF ⇒ residually finite" (Vershik--Gordon 1997).

## 3. Manuscript proposals (RULES §6)

### Option B (recommended if the note stays minimal): one remark in the introduction

(a) Current text, l.63-65:
```latex
Thom had already constructed a finitely generated Kazhdan LEF group
that is not residually finite~\cite[Theorem~1.4]{Thom}; his example
is not simple.
```
Replacement (appends three lines to the same paragraph):
```latex
Thom had already constructed a finitely generated Kazhdan LEF group
that is not residually finite~\cite[Theorem~1.4]{Thom}; his example
is not simple.
A finitely presented LEF group is residually finite, so $G_X$ is not
finitely presented. We do not know whether some finitely presented
infinite simple Kazhdan group is sofic.
```
(b) The proof is the sentence itself. The standard reason: a local embedding of a ball that contains
all relators extends to a homomorphism onto a finite group that is injective on the ball.
(c) +3 lines.
(d) Trade-off: it answers the first question a reader asks about `G_X` (is it finitely presented?) and
names the next question, with no new machinery and no citation.
(e) Status: standard fact. The open status rests on the bounded check in §1.

### Option A (if the note gains a closing question): a short final section

(a) Insert before l.264 (`\subsection*{Origin and authorship}`), and add `\newtheorem*{question}{Question}`
after l.9:
```latex
\section{Finite presentations}

The groups $G_X$ are not finitely presented. Let $G=\langle S\mid R\rangle$
be finitely presented and LEF, and let $B$ be a ball in $G$ that contains
all relators. A local embedding of $B$ into a finite group extends to a
homomorphism of $G$ that is injective on $B$, so $G$ is residually finite.
Every homomorphism from an infinite simple group to a finite group is trivial.

The same obstruction applies to every sofic approximation by linear maps.
Two distinct affine maps of a finite vector space differ on at least half of
its vectors. So a sofic approximation by affine maps satisfies each relation
exactly on large models, and it is a local embedding. A finitely presented
example needs permutation models of another kind.

\begin{question}
Is there a finitely presented infinite simple group with property~\textup{(T)}
that is sofic or hyperlinear?
\end{question}

The Kac--Moody lattices studied by Caprace and R\'emy include finitely
presented infinite simple Kazhdan groups~\cite{CapraceRemy}. We do not know
whether any of them is sofic.
```
Bibliography entry, placed alphabetically after `\bibitem{BCFS}` (DOI verified through Crossref on
2026-09-13):
```latex
\bibitem{CapraceRemy}
P.-E. Caprace and B.~R\'emy,
\emph{Simplicity and superrigidity of twin building lattices},
Invent. Math. \textbf{176} (2009), 169--221.
\doi{10.1007/s00222-008-0162-6}.
```
(b) Complete as written. The affine claim: the fixed points of `y ↦ Ay + b` are empty or a coset of
`ker(A - 1)`, which has index at least 2 unless the map is the identity. A relation's defect is an
affine map fixing a proportion of vectors tending to 1, so it is the identity.
(c) About +28 lines (22 in the section, 1 in the preamble, 5 in the bibliography).
(d) Trade-off: the reader learns the exact boundary of the method and the natural next question with
a two-line proof and one citation, at a cost of about 28 lines. The middle paragraph can be dropped
(-6 lines) with no loss to the rest.
(e) Status:
- the fp remark is standard;
- the affine paragraph is `gap-sofic-approximations-are-local-embeddings` (unreviewed, queued with
  sk-verify-3);
- the Caprace--Rémy sentence relies on the graph's source-read citation
  `km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4` and on their Invent. Math. paper, which
  this lane did not read at source. sk-citations may want to confirm the exact theorem number.

## 4. Sharpest next target

For a finitely presented infinite simple Kazhdan group `S`, sofic models must generate permutation
groups containing nontrivial elements with fixed-point ratio tending to `1`. Fixed-point-ratio
classifications of primitive groups (Liebeck--Saxl, Guralnick--Magaard, Burness) suggest the
following open claim, not landed here: the primitive constituents of such models are eventually
alternating or symmetric groups in their actions on `k`-subsets, or product actions built from them.
It would direct constructions toward combinatorial models and away from groups of Lie type.

The concrete cruxes already owned by other lanes are Labbé's quantum rigidity (gate (a)) and the
Steinberg kernel (gate (b)). No new family of lanes is recommended.
