# sk-lit-novelty-2: novelty table and credit sentences for revision 3 (2026-09-13)

Lane `sk-lit-novelty-2` (roster F). The task is to bound and state precisely the novelty of the three results that revision 3 of `simple_kazhdan_sofic_group.tex` carries or plans. Main's tip when I started was 898d91700d; the note is rev2 e80dcf20ad. No mathematics is claimed here; this is literature and credit only.

## 0. Search bound (read this before relying on any "new within the search")
- About 12 web searches (US engine, 13 Sep 2026). Queries:
  - embeddings into simple groups with (T);
  - LEF envelopes;
  - marked limits of finite simple groups with (T);
  - universal residually finite hosts;
  - Belegradek–Osin; Osin's small cancellation; Ol'shanskii SQ-universality.
- Read at source:
  - Kionke–Schesler arXiv:2304.09307v1: pp. 1–3 (intro, Theorems 1.1–1.2) and pp. 38–41 (Questions, bibliography), from the arXiv PDF as page images;
  - the arXiv abstract pages of math/0601590 (Arzhantseva–Minasyan–Osin), math/0411039 (Osin), 2209.00580 (X. Ma) and 2407.05533 (Schesler).
- Crossref-confirmed today: Kionke–Schesler (doi 10.4171/jca/103), Schupp 1976, Wilson 1980, Ore 1951.
- Reused from main: `sk-novelty-prior-art-2026-09-13-part1/2.md`, `sk-questions-ggt-literature-2026-09-13-part1/2.md`, `sk-strong-3-universal-host-2026-09-13.md`, `sk-strong-1-universal-kazhdan-group-2026-09-13.md`, `sk-expanders-limits-proposal-2026-09-13.md`.
- NOT done: MathSciNet or zbMATH queries; full reading of Osin 2010, Belk–Zaremsky, Darbinyan–Steenbock or Ol'shanskii 1995; Russian-language sources.

## 1. Novelty table

| # | Result (rev3) | Closest prior work | What the note adds | Status of novelty |
|---|---|---|---|---|
| N1 | A f.g. group is LEF iff it is a subgroup of an infinite f.g. simple Kazhdan LEF group | Gorjuškin 1974; Schupp 1976 (countable groups into 2-generated simple groups; no approximation, no (T)). Kionke–Schesler 2024 Thm 1.2 (f.g. RF, optionally amenable, groups into f.g. simple LEF groups; no (T); RF input). Osin 2010, Belk–Zaremsky 2022, Darbinyan–Steenbock 2022 (simple hosts with other extra properties). | Property (T) for the host, and LEF input instead of RF, so the class is characterized exactly. | NEW within the search for the (T)+LEF host. See risk R1. |
| N2 | One infinite f.g. simple Kazhdan LEF group contains every f.g. linear group and every f.p. RF group | Wilson 1980 Thm A (countable RF groups into 2-generator RF groups; no simplicity). Schupp/Gorjuškin (one simple host for all countable groups; no approximation). Kionke–Schesler (one envelope per group). | The host is simultaneously simple, Kazhdan and LEF. The proof is a short composition, Wilson + N1's RF case. | NEW within the search, as a composition. Credit Wilson in the same sentence. |
| N3 | G_X is a marked limit of finite simple groups SL_{3N}(F_2) whose Cayley graphs form expanders | Kassabov 2007 (SL_{3k}(F_p) expanders as quotients of EL_3(Z⟨x_1,x_2⟩)). Ershov–Jaikin-Zapirain–Kassabov, Mem. AMS 2017 (Kazhdan mother groups for finite simple groups of Lie type of rank ≥ 2). Grigorchuk–Medynets 2014 (infinite simple LEF groups, amenable). Thom 2010 (Kazhdan LEF non-RF, not simple). | The limit is an infinite simple Kazhdan group; the expansion is Kassabov's. | NEW within the search for "infinite simple limit". The expander part is PRIOR (Kassabov); rev2 already credits him. |

## 2. Details behind each row

### N1
- **Kionke–Schesler, verbatim** (arXiv:2304.09307v1, p. 2): "Theorem 1.2 (Theorem 9.14). Let H be a finitely generated, residually finite (amenable) group. There is a finitely generated, residually finite (amenable) group G and an infinite, simple, (amenable) LEF group Q such that (1) there is an embedding ι: H → G, (2) there is a projection π: G → Q, (3) the composition π∘ι is injective."
  - Q is a quotient of the f.g. group G, so it is finitely generated, and H embeds in Q.
  - Their abstract: "every finitely generated residually finite (amenable) group embeds into a finitely generated (amenable) LEF simple group".
  - Neither the abstract nor the intro mentions (T) for Q. The only property (T) in the paper, Question 10.4 (p. 38), concerns Grothendieck pairs.
- **The classical line, as Kionke–Schesler record it** (p. 2): "It is an easy consequence of the Baer-Schreier-Ulam theorem [3] that every group G embeds into a simple group Q. In the case where G is countable, it was shown by Gorjuškin [30] that Q can be chosen to be 2-generated (see also [67]). Since then, many embedding results of specific classes of groups into simple groups with additional properties have been obtained; see e.g. [8, 20, 60]."
  - [8] = Belk–Zaremsky, Twisted Brin–Thompson groups, Geom. Topol. 26 (2022);
  - [20] = Darbinyan–Steenbock, Embeddings into left-orderable simple groups, J. LMS (2) 105 (2022);
  - [60] = Osin, Small cancellations over relatively hyperbolic groups and embedding theorems, Ann. of Math. 172 (2010).
  - Matte Bon [52] embeds groups generated by bounded automata in f.g. simple amenable groups.
- **Kazhdan-flavoured embedding results found; none gives a simple Kazhdan host containing a given group:**
  - Belegradek–Osin (Rips construction and Kazhdan property (T), Groups Geom. Dyn. 2): every countable group embeds in Out(N) for some Kazhdan N. This is not a subgroup of a simple group. Metadata from the search snippet; not opened.
  - Ol'shanskii's SQ-universality: every countable group embeds in a quotient of any non-elementary hyperbolic group. Quotients of a hyperbolic Kazhdan group are Kazhdan, but not simple in general. Recalled and from search snippets; not opened.
  - Arzhantseva–Minasyan–Osin (math/0601590), abstract read: SQ-universality for relatively hyperbolic groups, no simple-quotient statement.
  - Tarski-monster quotients of hyperbolic Kazhdan groups are simple Kazhdan groups, but every proper subgroup is cyclic, so they contain no given group.
- **Adjacent, not prior for N1:**
  - X. Ma, arXiv:2209.00580 (abstract): topological full groups of minimal topologically free residually finite actions are LEF, and on some Toeplitz subshifts over free groups. No (T), no simplicity of a host containing a given group.
  - E. Schesler, arXiv:2407.05533 (abstract): f.g. RF torsion groups embed in f.g. torsion groups that are residually finite simple. Not simple.
- **Risk R1 (the real one):** small cancellation over hyperbolic Kazhdan groups might already give "every countable group embeds in a f.g. simple Kazhdan group", with no approximation property, somewhere in the Ol'shanskii–Osin literature. I found no such statement, but did not read Osin 2010 or Ol'shanskii's papers in full.
  - If it exists, the (T) half of N1 without LEF is prior, and the note's novelty is the combination with LEF.
  - The credit sentences below never claim the first simple Kazhdan host, only "adds property (T)" to Kionke–Schesler's LEF host, so they stay true either way.

### N2
- Wilson 1980, Theorem A, verbatim on main (sk-strong-1/3, from the Springer PDF p. 149): "Every countable residually finite group can be embedded in a 2-generator residually finite group". It carries no simplicity and no (T).
- Schupp 1976 applied to the countable direct sum gives a simple host with no approximation property (sk-strong-3 §5).
- Sharpness: no f.g. group contains all f.g. RF groups, by Chong–Wise arXiv:2207.00410 plus countability. That was checked at abstract level only by sk-strong-1; not re-read here.

### N3
- Kassabov, Invent. Math. 170 (2007) 297–326, arXiv:math/0502237 p. 5 (quoted on main by sk-expanders-limits): "These two observations allow us to consider the groups SL_{3l}(F_p) as quotients of EL_3(Z⟨x_1,x_2⟩)."
- Ershov–Jaikin-Zapirain–Kassabov, Property (T) for groups graded by root systems, Mem. Amer. Math. Soc. 249 (2017), no. 1186. From the Kionke–Schesler bibliography [25]; the search snippet of arXiv:1102.0031 names the mother-group statement.
- Infinite simple LEF groups (derived topological full groups) were known as limits of finite groups (Grigorchuk–Medynets 2014, Matui 2006). They are amenable, so they have no uniform Kazhdan constant.
- Searches for "limit of finite simple groups" with "property (T)" in the space of marked groups returned no infinite simple Kazhdan limit.

## 3. Proposal for the note (§6 format)
Line numbers are those of main's rev2 (e80dcf20ad); rev3 is in assembly, so these are insertion texts.

(a) **Credit sentence before the LEF corollary**, the first sentence of the new §2. +4 lines.
```latex
Every countable group embeds in a finitely generated simple
group~\cite{Gorjuskin,Schupp}, and Kionke and Schesler proved that every
finitely generated residually finite group embeds in a finitely generated
simple LEF group~\cite[Theorem~1.2]{KionkeSchesler}. The next corollary
adds property~\textup{(T)} and applies to every LEF group. Since LEF
passes to subgroups, it characterizes LEF groups.
```
- Trade-off: the reader sees exactly what is prior; no new fact to trust.
- If the §2 text already names Kionke–Schesler, drop the second clause, not the first sentence.

(b) **Credit clause for the universal host**, inside its paragraph. +2 lines.
```latex
Wilson proved that every countable residually finite group embeds in a
2-generator residually finite group~\cite[Theorem~A]{Wilson}. Applying
Corollary~\ref{cor:lef} to such a group ...
```

(c) **N3:** no change. rev2 l.68 already says "the expanders arise as in Kassabov's construction". Optional: "and Kazhdan mother groups for finite simple groups of Lie type are due to Ershov, Jaikin-Zapirain and Kassabov~\cite{EJZK}". I recommend against it: the note does not use EJZK.

(d) **Do NOT write:**
- "the first simple Kazhdan group containing every ..." (risk R1);
- "no simple Kazhdan host was known";
- "first infinite simple limit of finite simple groups" without "with property (T)" (derived topological full groups are LEF simple).

## 4. Bibitems (verified where stated)
```latex
\bibitem{Gorjuskin}
A.~P. Gorju\v{s}kin, \emph{Imbedding of countable groups in 2-generator
simple groups}, Mat. Zametki \textbf{16} (1974), 231--235.

\bibitem{KionkeSchesler}
S.~Kionke and E.~Schesler, \emph{From telescopes to frames and simple
groups}, J. Comb. Algebra (2024).
\doi{10.4171/jca/103}. \href{https://arxiv.org/abs/2304.09307}{arXiv:2304.09307}.

\bibitem{Ore}
O.~Ore, \emph{Some remarks on commutators}, Proc. Amer. Math. Soc.
\textbf{2} (1951), 307--314. \doi{10.1090/S0002-9939-1951-0040298-4}.

\bibitem{Schupp}
P.~E. Schupp, \emph{Embeddings into simple groups}, J. London Math. Soc.
(2) \textbf{13} (1976), 90--94. \doi{10.1112/jlms/s2-13.1.90}.

\bibitem{Wilson}
J.~S. Wilson, \emph{Embedding theorems for residually finite groups},
Math. Z. \textbf{174} (1980), 149--157. \doi{10.1007/BF01293535}.
```
- Gorjuškin: data from the Kionke–Schesler bibliography [30] (MR 382456), not Crossref-checked; the English translation is not located.
- Kionke–Schesler: Crossref gives J. Comb. Algebra, published online 2024-11-15, with NO volume or pages in the record; theorem numbers are from arXiv v1.
- Schupp, Wilson, Ore: Crossref-confirmed on 2026-09-13.

## 5. Status
- Nothing here is mathematics.
- Verbatim quotes: Kionke–Schesler Theorem 1.2 and the intro paragraph (from the PDF page images); Wilson Theorem A (main's import).
- Unverified: Belegradek–Osin and Ol'shanskii (snippets only); EJZK metadata (secondary); Gorjuškin page data (secondary).
