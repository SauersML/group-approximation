# sk-novelty: proposals for the simple Kazhdan sofic group note (RULES §6)

**Evidence.** `research/artifacts/sk-novelty-prior-art-2026-09-13-part1.md` (e8c3931be3) and `-part2.md`.
**Line numbers.** `$SK/manuscript-disk-1646.tex` (the disk version of 16:46).

## Summary
- **The novelty claims hold within the bounded search.** Two sentences need no change:
  - l.31–32, "This answers the questions of Brown, Ozawa, and Pestov";
  - l.58, "The new step is the simplicity argument".
- **Recommended changes:**
  - **P1:** the credit sentence for the simplicity step. Replace Stepanov with Matui, the verified precedent that uses
    the same localization.
  - **P2:** a missing credit. Grigorchuk–Medynets proved the decidability form of "word problem versus language" for
    derived topological full groups.
- **Optional:** P3, one context sentence (simple LEF groups from the same subshift are amenable).
- **Passed to sk-citations:** P4.

## P1. Credit for the simplicity step (recommended)

**(a) Current text, l.58–62:**
```latex
Grigorchuk--Medynets~\cite{GM}. The new step is the simplicity argument:
a nontrivial normal subgroup meets a finite simple matrix group
supported on a clopen tower, and therefore contains an elementary
matrix. This is an explicit elementary-matrix extraction argument,
in the normal-structure tradition described by Stepanov~\cite{Stepanov}.
```

**Replacement:**
```latex
Grigorchuk--Medynets~\cite{GM}. The new step is the simplicity argument:
a nontrivial normal subgroup meets a finite simple matrix group
supported on a clopen tower, and therefore contains an elementary
matrix. For derived topological full groups, Matui showed in the same
way that a nontrivial normal subgroup meets a simple union of alternating
groups on towers~\cite[Lemma~3.4 and Theorem~4.9]{Matui}.
```

**Bibliography.** Delete `\bibitem{Stepanov}` (l.328–332); l.62 is its only citation. Insert in alphabetical order:
```latex
\bibitem{Matui}
H.~Matui, \emph{Some remarks on topological full groups of Cantor minimal
systems}, Internat. J. Math. \textbf{17} (2006), 231--251.
\doi{10.1142/S0129167X06003448}.
```

**(b) Proof text.** None; this is a credit sentence.

**(c) Length.** Text +1 line; bibliography +4 −5; net 0.

**(d) Reader-facing trade-off.**
- The replacement credits the closest verified precedent, which uses the same localization: a commutator with an element
  of small clopen support lands in a simple group on towers.
- The current sentence credits a tradition whose central lemma the proof does not use (Stepanov's Lemma 4.3, extraction
  from zero-divisor entries).
- The reader gets one citation to trust and no new mathematics.

**(e) Status.**
- The Matui quotes come from the PDF text layer (part 2 §4.1). The DOI is Crossref data read through the fetch tool.
- sk-citations should confirm pages and DOI before print. No Cairn node.

**Variant P1′** (if the user wants Stepanov kept). Use the P1 replacement, keep `\bibitem{Stepanov}`, and cite Stepanov
at the level ideal instead, since it matches his standard description (§1.6(3)). Current l.223:
```latex
Finally, $I_N=\{r\in R:e_{12}(r)\in N\}$ is a two-sided ideal:
```
Replacement:
```latex
Finally, the level $I_N=\{r\in R:e_{12}(r)\in N\}$ is a two-sided
ideal~\cite{Stepanov}:
```
Net length: +1 line of text; bibliography +4.

## P2. Credit for the word-problem mechanism (recommended)

**(a) Current text, l.238–239:**
```latex
The word problem of $G_X$, in the finite generators above, has the same
Turing degree as the language $L(X)$ of finite words occurring in $X$.
```

**Replacement:**
```latex
The word problem of $G_X$, in the finite generators above, has the same
Turing degree as the language $L(X)$ of finite words occurring in $X$.
For derived topological full groups, Grigorchuk and Medynets proved that
the word problem is decidable if and only if $L(X)$ is
recursive~\cite[Theorem~1.1(3)]{GMpres}.
```

**Bibliography**, inserted after `\bibitem{GM}`:
```latex
\bibitem{GMpres}
R.~Grigorchuk and K.~Medynets, \emph{Presentations of topological full
groups by generators and relations}, J. Algebra \textbf{500} (2018), 46--68.
\doi{10.1016/j.jalgebra.2016.10.027}.
```

**(b) Proof text.** None.

**(c) Length.** Text +3 lines; bibliography +4.

**(d) Reader-facing trade-off.**
- The reader learns that the link between language and word problem is already known, at the level of decidability,
  for another simple group built from the same subshift.
- The note's contribution there is the degree-level statement for simple Kazhdan LEF groups.
- Cost: three lines and one reference.

**(e) Status.**
- Theorem 1.1(3) is quoted verbatim from the text layer (part 2 §5.1): "The group G'_T has decidable word problem if and
  only if L(Ω) is recursive."
- The journal data is Crossref through the fetch tool.

## P3. Context sentence (optional, neutral)

Insert after l.65 ("is not simple."):
```latex
The derived topological full group of $X$ is also infinite, finitely
generated, simple and LEF~\cite{Matui,GM}, but it is amenable~\cite{JM}.
```

Bibliography (P1 already adds Matui):
```latex
\bibitem{JM}
K.~Juschenko and N.~Monod, \emph{Cantor systems, piecewise translations and
simple amenable groups}, Ann. of Math. (2) \textbf{178} (2013), 775--787.
\doi{10.4007/annals.2013.178.2.7}.
```

**(c) Length.** Text +2 lines; bibliography +4.

**(d) Reader-facing trade-off.**
- The reader sees that simplicity plus LEF was already available from the same subshift, so the new ingredient of the
  theorem is property (T). One dynamical system then gives an amenable simple group and a Kazhdan simple group.
- Cost: two lines and one reference.

**(e) Status.**
- Sources: Matui Theorems 4.9 and 5.4 (text layer plus fetch tool), GM 2014 Theorem 2.6 (R: P).
- The Juschenko–Monod data is recalled and NOT Crossref-checked. Check it before print.

## P4. Passed to sk-citations (no text proposed here)
- **l.63–64, "[Thom, Theorem 1.4]" for "not residually finite".**
  - Theorem 1.4 states "a finitely generated Kazhdan group G which is locally embeddable into finite groups … but does
    not have the factorization property".
  - "Not residually finite" is in Thom's abstract, and for Kazhdan groups it follows from Kirchberg's theorem.
  - Exact alternative: "a finitely generated Kazhdan LEF group without Kirchberg's factorization property, hence not
    residually finite".
- **l.150–152** cite Pestov's guide for LEF ⇒ sofic ⇒ hyperlinear. The primary source is Elek–Szabó, Math. Ann. 332
  (2005). The survey citation is adequate under the short constraint.

## Checked and unchanged
- **l.31–32 and l.38–42:** no earlier answer within the bound (part 1 §1).
- **l.63–65:** Thom's group is non-Hopfian, so it has a proper nontrivial normal subgroup and is not simple (part 1
  §1.2).
- **l.231–235:** "continuum many isomorphism classes of these groups" is new for simple Kazhdan LEF groups (part 2
  §5.2). No qualifier is needed.
