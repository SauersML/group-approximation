# sk-intro-writer proposal: the introduction (RULES §6)

- **Lane:** sk-intro-writer, 2026-09-13, resumed after the ~20:00 restart.
- **Base:** main's note, rev2 (e80dcf20ad, md5 4ad49212…). `sk/drafts/rev3.tex` dates from 19:55, before the restart, so it is not the base. Line numbers "l." refer to rev2.
- **Label:** `cor:lef` matches rev3-partB l.69.
- **Target:** at most one printed page: the question and its history, why it matters, the results in words, method and credit.
- **Mathematics:** none new.
- **What it supersedes.** This is one merged text. It replaces the intro-level insertions of:
  - sk-lit-credit-audit P1 (Kazhdan) and P2 (Rădulescu, Gromov, Weiss);
  - sk-lit-background part 2 §2 (draft background paragraph);
  - sk-panel-referee-3 F1 (Ozawa's LLP clause);
  - sk-panel-referee-6 F3 (earlier simple Kazhdan groups);
  - rev3-partA l.86–89 (results sentence).

  Apply this text once. The other lanes' proof-level credits are compatible and stay separate: Margulis at l.163–164, Elek–Szabó at l.164–166, the Gorjuškin/Schupp sentence opening §2.
- **Compile probe:** MSI, texlive/2025, 3 passes, rev2 preamble plus the text below plus the bibliography: 0 errors, 0 overfull, 0 undefined. The two underfull boxes are rev2's own Brown and Ozawa bibitems.
- **Length:** the intro including Theorem 1 runs from 194pt on page 1 to 140pt on page 2, about 545pt against a 628.75pt page (0.87 page).
- **Probe file:** `sk/lanes/sk-intro-writer/probe-intro.tex`.

## 1. (a) Current text: rev2 l.40–79
The opening paragraph l.40–46; Theorem 1, l.48–62, which is unchanged; the method paragraph l.64–79 ("Property~\textup{(T)} follows from the theorem of Ershov and Jaikin-Zapirain~\cite{EJZ}. … Thom constructed a finitely generated Kazhdan LEF group that is not residually finite~\cite{Thom}, but his example is not simple."). Every sentence of l.40–46 and l.64–79 is kept, reordered, or extended below. The Thom sentence moves into the opening.

## 2. (b) Replacement, verbatim LaTeX (Variant I, for rev3 with §2 on LEF groups and the universal host)
```latex
Can an infinite simple group with property~\textup{(T)} be hyperlinear?
Brown asked this in 2001 as a question about embeddings into unitary
groups of McDuff factors that embed in an ultrapower $\mathcal R^\omega$
of the hyperfinite $\mathrm{II}_1$ factor~\cite[\S11, Question~7]{Brown}.
Ozawa stated the hyperlinear form in 2003, noting that the full
$C^*$-algebra of such a group cannot have the local lifting
property~\cite[p.~527]{Ozawa}, and Pestov's Open question~9.1 adds the
sofic form~\cite{Pestov}. Hyperlinear groups were named by
R\u{a}dulescu~\cite{Radulescu}, and sofic groups were introduced by
Gromov~\cite{Gromov99} and named by Weiss~\cite{Weiss}. Infinite simple
Kazhdan groups arise as quotients of hyperbolic Kazhdan
groups~\cite{Gromov87} and as Kac--Moody lattices, which gave the first
finitely presented examples~\cite{CapraceRemy}. Thom constructed a
finitely generated Kazhdan LEF group that is not residually
finite~\cite{Thom}, but his example is not simple. Pestov and Kwiatkowska
then wrote that a hope of constructing groups that are not hyperlinear
from property~\textup{(T)} remained, as it was unknown whether finitely
generated simple Kazhdan groups can be hyperlinear~\cite{PestovKwiatkowska}.
The groups below answer all three forms positively.

\begin{theorem}\label{thm:main}
   ... rev2 l.48--62 verbatim ...
\end{theorem}

The same proof applies to the action of the lamplighter group
$\F_2\wr\Delta$ on $\F_2^{\Delta}$, for an infinite finitely generated
group $\Delta$. So a finitely generated group is LEF if and only if it is
a subgroup of an infinite, finitely generated, simple group with
property~\textup{(T)} that is LEF (Corollary~\ref{cor:lef}). Kionke and
Schesler proved that every finitely generated residually finite group
embeds in a finitely generated simple LEF
group~\cite[Theorem~1.2]{KionkeSchesler}. With Wilson's embedding
theorem~\cite{Wilson}, one such group contains every finitely generated
linear group (Corollary~\ref{cor:host}), and the word problems of the
groups $G_X$ realize every Turing degree (Corollary~\ref{cor:wp}).

Property~\textup{(T)}, introduced by Kazhdan~\cite{Kazhdan}, follows from
the theorem of Ershov and Jaikin-Zapirain~\cite{EJZ}. The finite models
use periodic approximation, as in the proof by Grigorchuk and Medynets
that topological full groups of minimal Cantor systems are
LEF~\cite[Theorem~2.6]{GM}. The derived subgroups of these topological
full groups are infinite, finitely generated and simple for minimal
subshifts~\cite{Matui}, but they are amenable~\cite{JuschenkoMonod}, so
they do not have property~\textup{(T)}. The expanders arise as in
Kassabov's construction~\cite{Kassabov}. Simplicity of $G_X$ also follows
from Stepanov's theorem on the normal structure of
$\GL_n$~\cite[Theorem~4.4]{Stepanov}, since the ring is simple and any
two of its elements $p,q$ satisfy $pr+qs=0$ with $(r,s)\ne0$, by a
dimension count on one cylinder. Our proof is direct: a nontrivial normal
subgroup contains a nontrivial commutator lying in a copy of the finite
simple group $\GL_d(\F_2)$ over a clopen tower, so it contains this group
and with it an elementary matrix. For derived topological full groups,
Matui showed in the same way that a nontrivial normal subgroup meets a
simple union of alternating groups on
towers~\cite[Lemma~3.4 and Theorem~4.9]{Matui}.
```
**Labels:** `cor:lef` matches rev3-partB l.69. rev3 has neither `cor:host` (partB l.143 is unlabeled) nor `cor:wp` (partC l.4); the editor adds both.

**New bibitems, in alphabetical position:**
```latex
\bibitem{CapraceRemy}
P.-E. Caprace and B.~R\'emy, \emph{Simplicity and superrigidity of twin
building lattices}, Invent. Math. \textbf{176} (2009), 169--221.
\doi{10.1007/s00222-008-0162-6}.

\bibitem{Gromov87}
M.~Gromov, \emph{Hyperbolic groups}, in: Essays in group theory, Math.
Sci. Res. Inst. Publ. \textbf{8}, Springer, New York, 1987, 75--263.
\doi{10.1007/978-1-4613-9586-7_3}.

\bibitem{Gromov99}
M.~Gromov, \emph{Endomorphisms of symbolic algebraic varieties},
J. Eur. Math. Soc. \textbf{1} (1999), 109--197.
\doi{10.1007/PL00011162}.

\bibitem{JuschenkoMonod}
K.~Juschenko and N.~Monod,
\emph{Cantor systems, piecewise translations and simple amenable groups},
Ann. of Math. (2) \textbf{178} (2013), 775--787.
\doi{10.4007/annals.2013.178.2.7}.

\bibitem{Kazhdan}
D.~A. Kazhdan, \emph{Connection of the dual space of a group with the
structure of its closed subgroups}, Funct. Anal. Appl. \textbf{1} (1967),
63--65. \doi{10.1007/BF01075866}.

\bibitem{KionkeSchesler}
S.~Kionke and E.~Schesler,
\emph{From telescopes to frames and simple groups},
J. Comb. Algebra (2024).
\doi{10.4171/jca/103}.
Preprint \href{https://arxiv.org/abs/2304.09307}{arXiv:2304.09307}.

\bibitem{PestovKwiatkowska}
V.~G. Pestov and A.~Kwiatkowska,
\emph{An introduction to hyperlinear and sofic groups},
in: Appalachian Set Theory 2006--2012, London Math. Soc. Lecture Note
Ser. \textbf{406}, Cambridge Univ. Press, 2012, 145--186.
\doi{10.1017/CBO9781139208574.006}.

\bibitem{Radulescu}
F.~R\u{a}dulescu, \emph{The von Neumann algebra of the non-residually
finite Baumslag group $\langle a,b\mid ab^3a^{-1}=b^2\rangle$ embeds into
$R^\omega$}, \href{https://arxiv.org/abs/math/0004172}{arXiv:math/0004172}
(2000).

\bibitem{Weiss}
B.~Weiss, \emph{Sofic groups and dynamical systems}, Sankhy\={a} Ser.~A
\textbf{62} (2000), 350--359.

\bibitem{Wilson}
J.~S. Wilson, \emph{Embedding theorems for residually finite groups},
Math. Z. \textbf{174} (1980), 149--157.
\doi{10.1007/BF01293535}.
```

## 3. Variants and gates
- **GATE, universal host.** It is unreviewed (queued with sk-verify-4). If it fails, replace "With Wilson's embedding theorem~\cite{Wilson}, one such group contains every finitely generated linear group (Corollary~\ref{cor:host}), and the word problems" with "The word problems", and drop the Wilson bibitem.
- **Variant II, if rev3 carries no §2.** Delete the paragraph "The same proof applies … (Corollary~\ref{cor:wp})." except its last clause, which becomes "The word problems of the groups $G_X$ realize every Turing degree (Corollary~\ref{cor:wp})." Drop the KionkeSchesler and Wilson bibitems.
- **Optional clause, +3 lines and +4 bibliography lines, after the characterization sentence** (sk-panel-referee-5 §2.1):
  ```latex
  The theorem of Boone and Higman characterizes solvability of the word
  problem in the same way: a finitely generated group has solvable word
  problem if and only if it embeds in a simple subgroup of a finitely
  presented group~\cite{BooneHigman}.
  ```
  ```latex
  \bibitem{BooneHigman}
  W.~W. Boone and G.~Higman, \emph{An algebraic characterization of groups
  with soluble word problem}, J. Austral. Math. Soc. \textbf{18} (1974),
  41--53. \doi{10.1017/S1446788700019108}.
  ```
  - Metadata: Crossref today.
  - The statement is standard, but I recalled it and did not re-read it at source. Include it only after sk-lit-locators or sk-verify-6 reads the theorem.

## 4. (c) Length
- **Variant I:** 67 source lines against rev2's 40 (l.40–46 plus l.64–79), so +27. Bibliography +45 lines (10 items).
- **Printed:** 0.87 page including Theorem 1, under the one-page cap.
- **Variant II:** about +18 source lines and +35 bibliography lines.

## 5. (d) Reader-facing trade-off
- **Ozawa clause.** Why the question matters, in Ozawa's own words: the LLP consequence. This is panel-3 B5/F1.
- **Names clause.** Where "hyperlinear" and "sofic" come from, as the credit audit asked for in P2, at two lines.
- **Earlier examples.** They tell the reader the difficulty was never existence of simple Kazhdan groups; the difficulty was approximating them. This is panel-6 F3, now with verbatim sources.
- **Pestov–Kwiatkowska sentence.** Replaces an unsourced absence claim ("no simple Kazhdan group was known to be hyperlinear") by what a printed survey recorded.
- **Results paragraph.** A reader who stops after page 1 knows the full strength of the paper. The characterization is panel-3 part 2's "most memorable sentence". Kionke–Schesler credit comes at first mention without any priority claim, which avoids novelty risk R1 of sk-lit-novelty-2. The note never says "first simple Kazhdan host".
- **Method paragraph.** Adds only Kazhdan's name (P1). It also adds one sentence that says exactly where property (T) is new: derived topological full groups are infinite, finitely generated, simple and LEF, but amenable. This is sk-novelty part 1 §1.2.
- **New machinery:** none.
- **New facts to trust:** Juschenko–Monod amenability; Kionke–Schesler Theorem 1.2 and Wilson, both for credit; the Gromov/Caprace–Rémy background.

## 6. (e) Status of every sentence
| sentence | source, and where it was checked | status |
|---|---|---|
| Brown, printed form | arXiv v1 §11 Q7, verbatim (sk-citations part 2; sk-operator-algebras §1) | VERIFIED |
| Ozawa: hyperlinear form and LLP | verbatim after Thm 7.4: "It is unknown whether there exists a simple property (T) group Γ which is hyperlinear. By the above theorem, the full C*-algebra C*Γ of such a group Γ cannot have the LLP." The journal p. 527 is indirect, via Thom's citation; sk-lit-locators owns it | VERIFIED (arXiv) |
| Pestov 9.1 adds sofic | v8 verbatim (sk-citations part 2) | VERIFIED |
| Rădulescu named hyperlinear; Gromov introduced sofic; Weiss named it | Pestov v8 verbatim: "The expression 'hyperlinear group' belongs to Radulescu"; "first introduced (without a name of its own)" by Gromov; "coined by Benjy Weiss" (sk-lit-background part 2 V3). Gromov99: Crossref. Weiss: zbMATH (sk-lit-credit-audit P2). Rădulescu cited through arXiv only, because the volume title is flagged in P2 | VERIFIED |
| Simple Kazhdan quotients of hyperbolic Kazhdan groups [Gromov87] | Thom main.tex l.96, verbatim (sk-lit-background V1). The text says "quotients of hyperbolic Kazhdan groups", which avoids the non-elementary caveat and makes no Ol'shanskii attribution | VERIFIED as attribution through Thom |
| Kac–Moody lattices, first finitely presented examples | Caprace–Rémy source l.153–161, verbatim (V2); "first finitely presented", not "first finitely generated" (sk-lit-background §3) | VERIFIED |
| Thom's group: LEF, Kazhdan, not RF, not simple | sk-novelty part 1 §1.2; sk-citations | VERIFIED |
| Pestov–Kwiatkowska hope and unknown status | arXiv v4 p. 28, verbatim: "a hope to use property (T) in order to construct non-hyperlinear groups is a bit diminished now, but surely not gone, as it remains in particular unknown whether finitely generated simple Kazhdan groups can be hyperlinear/sofic" (sk-questions-ggt part 1 A1). Crossref: LMS LNS 406 (2012) 145–186 | VERIFIED |
| Lamplighter action; LEF iff subgroup of an infinite f.g. simple Kazhdan LEF group | `lef-groups-embed-in-simple-kazhdan-lef-groups`: sk-review-3 part 6 PASS; sk-lef-embedding-c adversarial PASS (0db6bc6383). Δ must be infinite for topological freeness | REVIEWED |
| Kionke–Schesler Thm 1.2 | verbatim from the arXiv PDF (sk-lit-novelty-2 §2); DOI via Crossref | VERIFIED |
| Wilson; one host contains every f.g. linear group | Wilson Thm A verbatim (sk-strong-1/3), Crossref; host = sk-strong-3 f222686f87 / sk-strong-1 4720705b70 | Wilson VERIFIED; host UNREVIEWED (gate §3) |
| Word problems realize every Turing degree | rev2 Corollary; reviewed nodes | REVIEWED |
| Kazhdan introduced (T) | Crossref (sk-lit-credit-audit P1) | VERIFIED |
| GM Thm 2.6; Matui Thms 4.9, 5.4; Juschenko–Monod | GM verbatim arXiv v4 p. 5 (panel-2 part 2); Matui from the PDFs (sk-subgroups); Juschenko–Monod Crossref today | VERIFIED |
| Kassabov; Stepanov Thm 4.4; Matui pattern | unchanged from rev2 (panel-2 part 2 §1) | VERIFIED |

Nothing here mentions Codex, OpenAI or Astra, and the Origin paragraph is untouched.

## 7. Considered and not proposed
- **Connes' embedding problem.** Pestov's text dates the origin "1979", against the Annals 1976 paper, and Brown's printed form already names 𝓡^ω.
- **Ol'shanskii 1993.** Not read at source (sk-lit-background §3).
- **Margulis for "(T) ⇒ expanders".** Belongs at l.163–164 (sk-lit-credit-audit P5; panel-5 B2; panel-6 §2.3).
- **Elek–Szabó.** Belongs at l.164–166 (credit-audit P3).
- **Camm 1953 and Clapham 1964.** Belong to §3 (panel-5 B5).
- **The Gorjuškin/Schupp background sentence.** Belongs at the start of §2 (sk-lit-novelty-2 (a)).
