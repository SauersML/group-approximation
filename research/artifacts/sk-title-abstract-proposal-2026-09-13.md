# sk-title-abstract proposal: title, abstract, opening paragraph and theorem statement

Lane `sk-title-abstract`, 2026-09-13.
- **Base text:** revision 1 (`sk/drafts/rev1.tex`, md5 33acb2a4…), with main's decision log `sk/drafts/rev2-decisions.md`.
- **Line numbers:** "rev1 l." refers to rev1; "disk l." refers to the frozen disk copy, identical to main's bf961c128b.
- **Status:** no Cairn nodes. Every variant uses only reviewed mathematics, except where a gate is named.

## 0. The sentence a reader should remember
"The elementary group $\EL_3$ of the crossed product of an infinite minimal subshift by $\Z$, over $\F_2$, is an
infinite simple Kazhdan group and a limit of finite simple groups."

The object is concrete, the family is explicit, and "limit of finite groups" is the standard name for LEF among
finitely generated groups. Everything else follows from it: sofic, hyperlinear, Brown's form.

## 1. Lineage, as printed (from `sk-citations-sources-2026-09-13-part2.md` §1–3, verbatim quotes checked there)
- **Brown**, arXiv:math/0111286, §11, Question 7: "Can an infinite, simple, discrete group with Kazdan's property T
  be embed into the unitary group of an R^ω-embeddable McDuff factor?"
- **Ozawa**, arXiv:math/0306067 v1 (3 Jun 2003), after Thm 7.4; journal IJM 15 (2004), p. 527: "It is unknown
  whether there exists a simple property (T) group Γ which is hyperlinear."
- **Pestov**, arXiv:0804.3968 v8, BSL 14 (2008): "Open question 9.1 (Cf. Ozawa [64]). Let G be an infinite simple
  group with Kazhdan's property (T). Can it be hyperlinear (sofic)?" v1 numbers it 8.1.
- **Rules followed in every variant:**
  - never "first asked";
  - Ozawa "stated" the hyperlinear form, since his text records it as unknown and does not pose a question;
  - Pestov "adds the sofic form";
  - Brown's form is glossed as he printed it.
- **Factual consistency flag, not a lineage change.** The text says "2003" (the preprint), and the bibitem is the 2004 journal article with p. 527. Proposal L1 below makes both visible.

## 2. Three variants

Common to all three:
- the opening paragraph O1 (§3) and the Ozawa bibitem fix L1 (§4);
- `\hypersetup{pdftitle=...}` changes to match the chosen title.

### Variant A: conservative (fits rev1 exactly; no gate)
**Title:**
```latex
\title{Infinite simple Kazhdan groups that are sofic}
```
**Reasons:**
- The plural matches the family (one group for each minimal subshift) and removes the four-modifier stack
  "An infinite simple Kazhdan sofic group".
- "sofic" is the searchable property.
- LEF, which is stronger, goes in the abstract.

**Abstract** (replaces rev1 l.26–34):
```latex
\begin{abstract}
For every infinite minimal subshift $X$, the group
$G_X=\EL_3(\LC(X,\F_2)\rtimes\Z)$ is an infinite, finitely generated,
simple group with property~\textup{(T)} that is locally embeddable into
finite groups. So $G_X$ is sofic and hyperlinear. This answers the
question of Brown and Ozawa whether an infinite simple Kazhdan group can
be hyperlinear, and Pestov's sofic version of it. The word problem of
$G_X$ has the Turing degree of the language of $X$, so every Turing
degree occurs and there are continuum many of these groups.
\end{abstract}
```
**Reasons:**
- It names $G_X$, so the reader can refer to it.
- The last sentence states the formula $WP(G_X)\equiv_T L(X)$, which rev1 proves (Corollary, rev1 l.190–194), and the continuum clause.
- Length: +1 line against rev1.

### Variant B: recommended (gate: rev2 item 6, sk-expanders-limits Option A, reviewed PASS+repair in `sk-review-2-2026-09-13-part2.md` §7b)
**Title:**
```latex
\title{Infinite simple Kazhdan groups that are limits of finite simple groups}
```
**Reasons:**
- The strongest property the note proves, in words a group theorist and an operator algebraist both parse at once.
- A simple group with property (T) is, in its own generators, a limit of the finite simple groups
  $\SL_{3N}(\F_2)$.
- "infinite" is needed: a finite simple group is trivially its own limit.
- The title does not name sofic, but the abstract's second sentence does.

**Abstract:**
```latex
\begin{abstract}
For every infinite minimal subshift $X$, the group
$G_X=\EL_3(\LC(X,\F_2)\rtimes\Z)$ is an infinite, finitely generated,
simple group with property~\textup{(T)}. It is a limit of finite simple
groups $\SL_{3N}(\F_2)$ in the space of marked groups, and their Cayley
graphs form a family of expanders. So $G_X$ is locally embeddable into
finite groups, sofic and hyperlinear. This answers the question of Brown
and Ozawa whether an infinite simple Kazhdan group can be hyperlinear,
and Pestov's sofic version of it. Every Turing degree is the
word-problem degree of some $G_X$.
\end{abstract}
```
**Theorem statement** (replaces rev1 l.43–54; +2 lines):
```latex
\begin{theorem}\label{thm:main}
Let $X\subseteq A^{\Z}$ be an infinite minimal subshift over a finite
alphabet, with shift $T$, and let $\LC(X,\F_2)$ be the ring of locally
constant functions $X\to\F_2$. Then
\[
  G_X=\EL_3\bigl(\LC(X,\F_2)\rtimes_T\Z\bigr)
\]
is an infinite, finitely generated, simple group with Kazhdan's
property~\textup{(T)}. It is the limit, in the space of marked groups, of
finite simple groups $\SL_{3N}(\F_2)$ whose Cayley graphs, with respect to
the images of a fixed generating set, form a family of expanders. So $G_X$
is locally embeddable into finite groups \textup{(LEF)}, sofic and
hyperlinear. The same holds for $\EL_n\bigl(\LC(X,\F_2)\rtimes_T\Z\bigr)$
for every $n\ge3$.
\end{theorem}
```
**Accuracy checks:**
- **Marked convergence:** `finite-simple-groups-converge-to-simple-kazhdan-group`, reviewed PASS twice (ex-review part 8 §8.6; ex-pestov91-second-review N5).
- **The surjection:** the free algebra maps onto $M_N(\F_2)$ when $N$ is the least period; this is checked in sk-expanders-limits Option A.
- **Expansion and the uniform Kazhdan constant:** they come from EJZ for $\EL_3(\F_2\langle x_1,\dots,x_{|A|+2}\rangle)$ (reviewed PASS, `sk-review-2` part 2, rows 6–7).
- **Credit:** Kassabov 2007 belongs in the text next to the expanders, not in the abstract.
- **The $n\ge3$ clause:** it covers the same statements with $\SL_{nN}(\F_2)$ and $\EL_n$ of the free algebra; EJZ holds for every $n\ge3$.
- **LEF:** for finitely generated groups, LEF is equivalent to being a marked limit of finite groups, so "So $G_X$ is LEF" is one line.
- **Length:** abstract +1 line, theorem +2 lines, both against rev1.

**MSC (optional, 0 lines):** add 05C48 (expander graphs) to the secondary list.

### Variant C: universal (gate: PASS for `rf-groups-embed-in-simple-kazhdan-lef-groups`, 3bcc003284, and rev2 item 22 adopted)
**Title:**
```latex
\title{Sofic simple Kazhdan groups and their residually finite subgroups}
```
**Reasons:** the title names the new structural theorem, that every finitely generated residually finite group is a subgroup of such a group, next to the answer. It gives the reader two statements in the title.

The title is plain, but a sentence-title such as "Every residually finite group lies in a simple Kazhdan LEF group" would drop "finitely generated" and "infinite". I recommend Variant C only if the corollary goes in with its proof.

**Abstract:**
```latex
\begin{abstract}
We construct infinite, finitely generated, simple groups with
property~\textup{(T)} that are locally embeddable into finite groups,
so sofic and hyperlinear. This answers the question of Brown and Ozawa
whether an infinite simple Kazhdan group can be hyperlinear, and
Pestov's sofic version of it. For an infinite minimal subshift $X$ the
group is $\EL_3(\LC(X,\F_2)\rtimes\Z)$, and its word problem has the
Turing degree of the language of $X$. Over residually finite acting
groups the same construction shows that every finitely generated
residually finite group is a subgroup of an infinite simple Kazhdan LEF
group.
\end{abstract}
```
**Credit for the body text:** without property (T), the embedding theorem is Kionke–Schesler (arXiv:2304.09307, Thm 1.2). The body must say so next to the corollary; the abstract claims only the Kazhdan version.

### Recommendation
- Take Variant B once item 6 is applied. It is the most memorable true statement at almost no extra length, and it replaces the partial-homomorphism wording both referees flagged.
- Use Variant A for any interim landing of rev1.
- Use Variant C only if the RF corollary goes in; it costs about +20 lines of body text.

## 3. Opening paragraph O1 (all variants; +1 line)
Current (rev1 l.37–41):
```latex
Can an infinite simple Kazhdan group be hyperlinear? Brown asked this
in its von Neumann algebra form in 2001~\cite[\S11, Question~7]{Brown},
and Ozawa in the hyperlinear form in 2003~\cite[p.~527]{Ozawa}.
Pestov's Open question~9.1 adds the sofic version~\cite{Pestov}.
The following construction answers all three forms positively.
```
Replacement:
```latex
Can an infinite simple group with property~\textup{(T)} be hyperlinear?
Brown asked this in 2001 as a question about embeddings into unitary
groups of $R^\omega$-embeddable McDuff factors~\cite[\S11,
Question~7]{Brown}. Ozawa stated the hyperlinear form in
2003~\cite[p.~527]{Ozawa}, and Pestov's Open question~9.1 adds the sofic
form~\cite{Pestov}. The groups below answer all three forms positively.
```
**Reasons:**
- "its von Neumann algebra form" does not say what Brown asked. The replacement glosses his printed question in one clause, so the reader can check that the note answers it. The bridge sentence of rev2 item 17 (L(G) ⊂ R^ω, so G ⊂ U(L(G)⊗̄R)) then has a visible target.
- "Ozawa stated" matches his sentence "It is unknown whether …".
- "The following construction" → "The groups below": the theorem states groups, not a construction.
- Names, years, citations and locators are unchanged.

## 4. L1: Ozawa bibitem (+1 line; factual consistency)
Current (rev1 l.263–266):
```latex
\bibitem{Ozawa}
N.~Ozawa, \emph{About the QWEP conjecture},
Internat. J. Math. \textbf{15} (2004), 501--530.
\doi{10.1142/S0129167X04002417}.
```
Replacement:
```latex
\bibitem{Ozawa}
N.~Ozawa, \emph{About the QWEP conjecture},
Internat. J. Math. \textbf{15} (2004), 501--530.
\doi{10.1142/S0129167X04002417}.
Preprint \href{https://arxiv.org/abs/math/0306067}{arXiv:math/0306067} (2003).
```
**Reason:** the text dates Ozawa's formulation 2003, and the bibliography then shows where 2003 comes from. Metadata comes from `sk-citations-bibliography-2026-09-13-part1.md` row "Ozawa" (arXiv v1, 3 Jun 2003, VERIFIED).

## 5. What I did not propose
- **Naming Pestov in the title:** the user's earlier decision was to keep it out.
- **A method sentence in the abstract:** rev1 removed it; that was main's decision 5.
- **Kirchberg, the factorization property and the LLP in the abstract:** rev2 item 17 puts them in the body. They strengthen nothing a first-time reader needs from the abstract.
- **"limit of finite simple groups" without the gate:** the finite models in rev1 are partial embeddings, and rev1 never states marked convergence.

## 6. Status
- **Variant A:** reviewed content only (rev1 texts, PASS by sk-referee-1 and sk-referee-2).
- **Variant B:** reviewed content (convergence node PASS twice; the explicit Kazhdan constant PASS; Option A LaTeX PASS+repair), but it needs rev2 item 6 in the body.
- **Variant C:** gated on the unreviewed `rf-groups-embed-in-simple-kazhdan-lef-groups` (queued with sk-verify-3).
- **O1 and L1:** wording and bibliographic consistency; the quotes they rest on were checked by sk-citations.
