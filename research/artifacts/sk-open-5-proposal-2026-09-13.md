# sk-open-5 proposal: the questions the note should end with

Lane `sk-open-5`, 2026-09-13. Line numbers refer to `sk/manuscript-disk-1646.tex` (md5 7b3dc4ec…).
The plan is `research/artifacts/sk-open-5-plan-2026-09-13.md`.

## Summary
Three questions pass every test:
- they are sharp;
- they are open after a bounded check (recorded below);
- the note's construction is the natural starting point;
- an answer would matter.

The questions:
- **Q1** finite presentation. It overlaps sk-fp-sofic-a's Option A: use one text, not both.
- **Q2** soficity over Z² subshifts of finite type.
- **Q3** rigidity: what G_X remembers about X.

Everything else I tested either falls at once, and so should not be posed, or belongs to another lane (§4). When this proposal was written, sk-characters and sk-universal-embedding-a/b had landed nothing that would add a fourth question.

## 1. Proposed text (a, b)

**Preamble**, after l.9 (`\newtheorem{corollary}[theorem]{Corollary}`), insert:
```latex
\newtheorem{question}{Question}
```

**Body**, insert before l.264 (`\subsection*{Origin and authorship}`):
```latex
\section{Questions}

The groups $G_X$ are not finitely presented. In a finitely presented
group, a local embedding into a finite group of a ball containing all
relators extends to a homomorphism, so a finitely presented LEF group is
residually finite. An infinite simple group is not.

\begin{question}\label{q:fp}
Is there a finitely presented infinite simple group with
property~\textup{(T)} that is sofic, or at least hyperlinear?
\end{question}

A positive answer would also answer Open problem~6.1 of
Alekseev--Thom~\cite{AlekseevThom}, which asks for a finitely presented
sofic group with property~\textup{(T)} that is not residually finite.

The finite models of Section~1 use periodic points with the same patterns
as $X$. An aperiodic subshift of finite type $X\subseteq A^{\Z^2}$ has
none, since a periodic configuration whose patterns of the forbidden size
occur in $X$ lies in $X$. Labb\'e's 19-tile Wang shift is such a subshift,
and it is minimal~\cite[Theorem~1]{Labbe}.

\begin{question}\label{q:z2}
Let $X\subseteq A^{\Z^2}$ be a minimal aperiodic subshift of finite type.
Is $\EL_3\bigl(\LC(X,\F_2)\rtimes\Z^2\bigr)$ sofic?
\end{question}

If $(X,T)$ is conjugate to $(Y,S)$ or to $(Y,S^{-1})$, then $G_X\cong G_Y$.

\begin{question}\label{q:rigid}
Does $G_X\cong G_Y$ imply that $X$ and $Y$ are flip conjugate? Does it
imply that they are strongly orbit equivalent~\cite{GPS}?
\end{question}
```

**Bibliography**, inserted in alphabetical position:
```latex
\bibitem{AlekseevThom}
V.~Alekseev and A.~Thom,
\emph{Centralizers of sofic approximations of Kazhdan groups},
\href{https://arxiv.org/abs/2608.05362}{arXiv:2608.05362} (2026).

\bibitem{GPS}
T.~Giordano, I.~F. Putnam, and C.~F. Skau,
\emph{Topological orbit equivalence and $C^*$-crossed products},
J. Reine Angew. Math. \textbf{469} (1995), 51--112.
\doi{10.1515/crll.1995.469.51}.

\bibitem{Labbe}
S.~Labb\'e, \emph{A self-similar aperiodic set of 19 Wang tiles},
Geom. Dedicata \textbf{201} (2019), 81--109.
\doi{10.1007/s10711-018-0384-8}.
```

Proof content, line by line:
- **Opening sentence.**
  - Take a finite presentation, g ≠ e, and a ball B containing every relator and a word for g.
  - A local embedding φ of B into a finite group Q defines a homomorphism of the free group on the generators. It kills the relators, since φ(e) = e, so it factors through the group.
  - φ is injective on B, so the image of g is nontrivial. So the group is residually finite.
  - An infinite simple group has no proper nontrivial normal subgroup of finite index, so it is not residually finite.
  - This is `finitely-presented-lef-groups-are-residually-finite` on main (reviewed PASS by un-verify-3). The sentence needs no citation.
- **Z² paragraph.**
  - Let w bound the diameter of the forbidden patterns.
  - A configuration whose w-patterns all occur in X avoids the forbidden patterns, so it lies in X.
  - A periodic configuration in X is a periodic point, and X is aperiodic.
  - So no periodic configuration has all its w-patterns in X, and the Section 1 models (windows evaluated along a periodic point with the same patterns) exist at no scale ≥ w.
- **Flip-conjugacy sentence.**
  - A conjugacy h with h∘T = S∘h gives LC(Y) ≅ LC(X) intertwining the shifts, hence R_X ≅ R_Y.
  - For S^{-1}, compose with LC(Y) ⋊_{S^{-1}} Z ≅ LC(Y) ⋊_S Z, f ↦ f, u ↦ u^{-1}.
- **Q2 has no centre to divide by.** The note's centre argument goes through for free minimal Z² actions: Z(R) = F_2, so Z(EL_3) = 1.

## 2. Length (c)
- Body: about +33 source lines. Bibliography: +12 (three bibitems). Preamble: +1. Total about +46 source lines, about half a page rendered.
- **Minimal variant:** keep the opening sentence, Q1, the Alekseev–Thom sentence, the flip sentence and Q3. Drop the Z² paragraph, Q2 and the Labbé bibitem. That is about +23 body lines and +8 bibliography lines.
- **Relation to sk-fp-sofic-a.** Its Option A (+28 lines) poses Q1 alone with a longer middle paragraph. Its Option B (+3 lines, intro remark) fits with the minimal variant here.

## 3. Trade-off (d) and status (e)
- **(d)** The reader gets the three natural next problems, each stated precisely with a one-line motivation. The motivating facts are proved in a line, apart from Labbé's Theorem 1 and the definition of strong orbit equivalence. The cost is about half a page.
- **(e) Q1.** Main roots `hyperlinear-fp-infinite-simple-kazhdan-group` and `hyperlinear-fp-infinite-simple-group` are OPEN. Alekseev–Thom 6.1 is recorded open on main: `arithmetic-defect-saturated-kazhdan-group-is-sofic` (OPEN) would answer it, and `fp-kernel-crosses-alekseev-thom-open-problem` is only a reduction.
- **(e) Q2.** Main root `free-minimal-subshift-elementary-groups-are-sofic` is OPEN.
- **(e) Q3.** Main `subshift-elementary-group-isomorphism-forces-orbit-equivalence` is OPEN. sk-rigidity-ring's plan reduces strong orbit equivalence to one step in characteristic 2. If that lane proves strong orbit equivalence, delete the second sentence of Q3 and state the result instead.
- **New node from this lane:** `tower-subshift-elementary-group-is-el-3k-of-base` (ESTABLISHED, landed 4720566fb1, queued with sk-verify-3). It calibrates Q3 and does not appear in the proposed text.
- **Citation checks.**
  - Alekseev–Thom: verified from the arXiv HTML (title, authors, 2026-08-05, Open problem 6.1 verbatim, below).
  - GPS: Crossref, doi 10.1515/crll.1995.469.51, Crelle 469 (1995) 51–112.
  - Labbé: Crossref, Geom. Dedicata 201(1) (2019) 81–109, doi 10.1007/s10711-018-0384-8. Theorem 1 is quoted verbatim on main in `minimal-aperiodic-wang-shift-citation`: "The Wang shift Ω_U is self-similar, aperiodic and minimal."

## 4. Bounded checks, and questions tested and not posed

**Q1 openness (bounded).**
- ex-open-status row 3.
- sk-fp-sofic-a's three web searches.
- This lane's searches:
  - "finitely presented" infinite simple group sofic open question;
  - Burger–Mozes simple lattice sofic OR hyperlinear OR "Connes embedding";
  - arXiv:2604.19174, read through WebFetch: it lists Thompson's groups only as candidates for nonsoficity.
- No finitely presented infinite simple sofic or hyperlinear group was found.
- Candidates with unknown status: Kac–Moody lattices (`km-246-lattice-is-sofic` OPEN), Burger–Mozes lattices, Thompson-like groups.
- Deligne's central extensions of Sp(2g,Z) are finitely presented, Kazhdan and not residually finite. We found no theorem making them sofic: the permanence property we know covers extensions with an amenable quotient, and here the amenable part is the kernel.
- Alekseev–Thom Open problem 6.1, verbatim: "Are there examples of finitely presented sofic groups with Kazhdan's property (T) that are not residually finite?"

**Q2.** No printed source was found; this is the note's own question.

**Tested and not posed:**
- *Is G_X finitely presented?* Falls: it becomes the opening sentence.
- *Does G_X have a nontrivial finite-dimensional unitary representation?* Falls. A faithful one would make G_X a f.g. linear group, which is residually finite (Mal'cev). By simplicity, any other one is trivial.
- *Is G_X P-stable or HS-stable?* Falls. Infinite Kazhdan groups are never locally HS- or P-stable (arXiv:2307.13155, as quoted by sk-questions-ggt).
- *Uniform Kazhdan constants, and expanders from the finite models?* Falls through EJZ's universal lattice; it belongs to sk-expanders-limits.
- *Does passing from EL_3 to EL_n add groups?* Falls for n = 3k: EL_{3k}(R_X) ≅ G_{X^(k)} (`tower-subshift-elementary-group-is-el-3k-of-base`).
- *Characters (only 1 and δ_e?)* Belongs to sk-characters. Pose it as Q4 only if that lane leaves it open.
- *Does every f.g. LEF group embed in an infinite simple Kazhdan LEF group?* Belongs to sk-universal-embedding-a/b. Pose it only if they leave it open.
- *LEF growth of G_X* (the analogue of Bradford's Question 7.2; `elementary-group-lef-growth-separates-subshifts` OPEN). Narrower, and it belongs to sk-lef-growth.
- *Torsion-free version; C*-simplicity; MF reduced C*-algebra.* Lower impact for this note, and no printed question was found.
