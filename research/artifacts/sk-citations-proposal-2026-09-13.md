# sk-citations proposal (2026-09-13)

Subject: `manuscript-disk-1646.tex` (md5 7b3dc4ec92b4581553bc0dc2b0edcb99; line numbers below refer to it).
Evidence: `research/artifacts/sk-citations-bibliography-2026-09-13-part1.md` (metadata) and
`research/artifacts/sk-citations-sources-2026-09-13-part2.md` (verbatim quotes).

## Summary
- **Verified as printed:**
  - every bibitem except Steinberg;
  - Brown §11 Question 7;
  - Ozawa p. 527 (indirectly, through Thom's citation of that page);
  - Pestov Open question 9.1;
  - EJZ Theorem 1.1;
  - Thom Theorem 1.4 and "his example is not simple";
  - the simplicity and centre facts for R;
  - Nekrashevych;
  - the LEF definition.
- **Two fixes:**
  - credit precision for Grigorchuk–Medynets (P1);
  - the published version of Steinberg (P2).
- **Optional precision:**
  - theorem pointers (P3, P5, P6);
  - a pointer to Stepanov's lemmas (P4);
  - Vershik–Gordon for LEF (P7);
  - DOIs (P8);
  - Lothaire for Sturmian facts (P9).
- **Out of scope** (part 2, last section): "both forms" at l.42 is for sk-exposition, and the McDuff deduction is for
  sk-operator-algebras.

## P1 (FIX, credit precision), l.57-58
Current:
```
Our finite models use the periodic-approximation mechanism of
Grigorchuk--Medynets~\cite{GM}.
```
l.58 continues with "The new step is the simplicity argument:", which stays as it is.
Replacement:
```
Our finite models use periodic approximation, as in the proof by
Grigorchuk and Medynets that topological full groups of minimal
Cantor systems are LEF~\cite[Theorem~2.6]{GM}.
```
(c) +1 line.
(d) Same content with the credit stated correctly. GM call periodic approximation "one of the main techniques in
Cantor dynamics" and use it to prove their Theorem 2.6.
(e) Checked against arXiv:1105.0719v4, pp. 2 and 5.

## P2 (FIX, bibliography), l.323-326
Current:
```
\bibitem{Steinberg}
B.~Steinberg, \emph{Simplicity, primitivity and semiprimitivity of
\'etale groupoid algebras with applications to inverse semigroup algebras},
\href{https://arxiv.org/abs/1408.6014}{arXiv:1408.6014} (2014).
```
Replacement:
```
\bibitem{Steinberg}
B.~Steinberg, \emph{Simplicity, primitivity and semiprimitivity of
\'etale groupoid algebras with applications to inverse semigroup algebras},
J. Pure Appl. Algebra \textbf{220} (2016), 1035--1054.
\doi{10.1016/j.jpaa.2015.08.006}.
```
(c) +1 line.
(d) The reader gets the published version.
(e) Crossref: JPAA 220(3) (2016) 1035-1054.

## P3 (recommended precision), l.102-104
Current:
```
We will also need that $R$ is simple and $Z(R)=\F_2$.
These are standard groupoid-algebra facts~\cite{BCFS,ClarkEdie,Steinberg};
here is the direct argument.
```
l.104 continues with "A nonzero two-sided ideal contains an", which stays as it is.
Replacement:
```
We will also need that $R$ is simple and $Z(R)=\F_2$.
These are standard facts about groupoid algebras over any field
\cite[Corollary~4.6 and Theorem~5.2]{ClarkEdie},
\cite[Corollary~3.6 and Proposition~3.7]{Steinberg}, first proved over
$\mathbb C$ in~\cite[Theorem~4.1]{BCFS}; here is the direct argument.
```
(c) +2 lines.
(d) The cited results now cover F_2 and are located, and BCFS keeps its priority credit with its actual scope (ℂ).
(e) Numbering checked in arXiv BCFS v2, CEM v1 and Steinberg v2; the journal numbering was not opened. `\mathbb` is
already available (amssymb is loaded).

Shorter alternative: "These are standard facts~\cite[Corollary~4.6 and Theorem~5.2]{ClarkEdie}; here is the direct
argument."
- Length: -1 line in the text, and the BCFS and Steinberg bibitems go (-10 lines), since l.103 is their only citation.
- Cost: the complex-origin credit is lost.

## P4 (optional precision), l.61-62
Current:
```
matrix. This is an explicit elementary-matrix extraction argument,
in the normal-structure tradition described by Stepanov~\cite{Stepanov}.
```
Replacement:
```
matrix. For elementary-matrix extraction over general rings, see
Stepanov~\cite[Lemmas~4.1 and~4.3]{Stepanov}.
```
(c) 0 lines.
(d) The reader gets the specific lemmas in place of a "tradition", and the sentence loses its metacommentary.
(e) Quotes from main's node `stepanov-linear-dependence-standard-normal-structure`, second-hand.
The novelty sentence at l.58 ("The new step is the simplicity argument") is sk-novelty's call; see part 2 §9.

## P5 (optional precision), l.150-152
Current:
```
The regular permutation actions of these finite groups give sofic
models; their permutation matrices give hyperlinear models
\cite{Pestov}.
```
Replacement:
```
The regular permutation actions of these finite groups give sofic
models; their permutation matrices give hyperlinear models
\cite[Definition~3.1 and Theorem~3.3]{Pestov}.
```
(c) 0 lines.
(d) Points to the definition of sofic and to the Elek–Szabó theorem as printed in the guide.
(e) Numbering from the arXiv v8 source. v8 incorporates the BSL galley corrections, but the journal PDF was not seen.

## P6 (optional precision), l.55
Current: `The subshift algebra is classical; see Nekrashevych~\cite{Nekrashevych}.`
Replacement: `The subshift algebra is classical; see Nekrashevych~\cite[\S4.4.1]{Nekrashevych}.`
(c) 0 lines.
(d) Points to the treatment of exactly this algebra: the crossed-product description, generation, and the simple
Sturmian example.
(e) Checked against arXiv:1501.00722v1, pp. 14-15.

## P7 (optional addition), l.119-120 and the bibliography
Current:
```
A group is LEF if every finite subset embeds injectively into a finite
group, preserving all products that stay in that subset.
```
Replacement:
```
A group is LEF~\cite{VershikGordon} if every finite subset embeds
injectively into a finite group, preserving all products that stay in
that subset.
```
New bibitem, after Thom:
```
\bibitem{VershikGordon}
A.~M. Vershik and E.~I. Gordon, \emph{Groups that are locally embeddable
in the class of finite groups}, Algebra i Analiz \textbf{9} (1997), no.~1,
71--97; English transl., St. Petersburg Math. J. \textbf{9} (1998), 49--67.
```
(c) +5 lines.
(d) Credits the source of the notion the theorem is about.
(e) Data from GM's bibliography (source l.741-743), which agrees with the repository's earlier record. No DOI was
checked, because Crossref was rate-limited.

## P8 (optional consistency): DOIs for the published bibitems that lack one
- BCFS, l.282: `\href{https://arxiv.org/abs/1204.3127}{arXiv:1204.3127}.` becomes `\doi{10.1007/s00233-013-9546-z}.`
- ClarkEdie, l.288: `\href{https://arxiv.org/abs/1403.4684}{arXiv:1403.4684}.` becomes `\doi{10.1007/s10468-015-9522-2}.`
- Nekrashevych, l.311: `\href{https://arxiv.org/abs/1501.00722}{arXiv:1501.00722}.` becomes `\doi{10.1142/S0218196716500156}.`

(c) 0 lines.
(d) Every published bibitem then carries a DOI, as EJZ, GM, MorseHedlund, Ozawa, Pestov, Stepanov and Thom already do.
(e) Crossref for BCFS and ClarkEdie; Nekrashevych's DOI comes from the World Scientific URL found by search
(Crossref was rate-limited).

## P9 (optional addition), l.251-252
Current:
```
Now use the infinite minimal Sturmian subshift of an irrational slope
$\alpha\in(0,1)$~\cite{MorseHedlund}. Its language is computable from
```
Replacement:
```
Now use the infinite minimal Sturmian subshift of an irrational slope
$\alpha\in(0,1)$~\cite{MorseHedlund}, \cite[Chapter~2]{Lothaire}. Its language is computable from
```
New bibitem, after GM:
```
\bibitem{Lothaire}
M.~Lothaire, \emph{Algebraic combinatorics on words}, Cambridge Univ.
Press, Cambridge, 2002. \doi{10.1017/CBO9781107326019}.
```
(c) +3 lines.
(d) A modern textbook source for Sturmian subshifts next to the 1940 original.
(e) Metadata from Crossref (Chapter 2, "Sturmian Words", pp. 45-110). The chapter's statement numbers were not
opened, so the pointer stays at chapter level.

## Verified, no change needed
- l.38-41: Brown §11 Question 7; Ozawa p. 527 (indirect); Pestov Open question 9.1.
- l.56 and l.97-99: EJZ Theorem 1.1, whose hypotheses match the paraphrase.
- l.63-65: Thom Theorem 1.4, not residually finite (via Kirchberg's Theorem 1.1), and not simple (non-hopfian).
- Bibitems Brown, EJZ, GM, MorseHedlund, Ozawa, Pestov, Stepanov, Thom.

## Status
- This lane lands artifacts only: no Cairn nodes, no new mathematics.
- Journal PDFs were not opened for Ozawa, Pestov, EJZ, Thom, CEM or Steinberg, so numbering comes from the named arXiv
  versions.
- Not reviewed by a verifier lane. Nothing here is mathematics that needs review.
