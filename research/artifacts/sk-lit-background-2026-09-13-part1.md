# sk-lit-background, part 1: verified bibliographic data for the note's background literature (2026-09-13)

Lane sk-lit-background (SK swarm, wave 8; brief in `wip/simple-kazhdan-note/swarm/ROSTER-F.md`).
- **Subject:** main's `simple_kazhdan_sofic_group.tex` at e80dcf20ad (revision 2, md5 4ad49212…, 386 lines).
- **This part:** bibliographic data only.
- **Part 2:** what the sources say, quoted verbatim, and the draft background paragraph.
- **Proposal artifact:** the citations the note should add or change.

## 0. Method and bound
- **Crossref run.** The Crossref REST API ran on MSI at about 20:25 CDT:
  - `api.crossref.org/works/<doi>` for 50 DOIs;
  - `query.bibliographic` for 8 items without a known DOI.
- **What the evidence covers.** Title, journal, volume, issue, pages and year in the tables below come from Crossref's record.
  - "first page only": Crossref gives only the first page. The last page is from secondary sources and is marked (2nd).
  - "no Crossref record": the query returned only unrelated items.
- **arXiv metadata.** The arXiv API timed out once. arXiv ids are checked in part 2 from the arXiv abstract pages and e-print sources.
- **Out of scope.** Theorem numbers and verbatim statements are part 2 or other lanes' checks, and are cited per item.
  - sk-citations (686feb0bbc, 6b259b4463) already verified the bibitems of the disk note.
  - sk-lit-locators owns journal-version theorem numbers.

## A. Sources in main's revision 2, re-verified

| key in rev2 | Crossref record (title; journal vol(issue) pages; year) | verdict |
|---|---|---|
| EJZ | Property (T) for noncommutative universal lattices; Invent. Math. 179(2) 303–347; 2010 | VERIFIED |
| GM | On algebraic properties of topological full groups; Sb. Math. 205(6) 843–861; 2014 | VERIFIED |
| GMpres | Presentations of topological full groups by generators and relations; J. Algebra 500, 46–68; 2018 | VERIFIED |
| GPS (1995) | Topological orbit equivalence and C*-crossed products; J. reine angew. Math. 469, 51–112; 1995 | VERIFIED. Crossref lists no author field; the authors are from the publisher page, as sk-open-5 checked |
| Kassabov | Universal lattices and unbounded rank expanders; Invent. Math. 170(2) 297–326; 2007 | VERIFIED |
| Kirchberg | Discrete groups with Kazhdan's property T and factorization property are residually finite; Math. Ann. 299(1) 551–563; 1994 | VERIFIED |
| Matui | Some remarks on topological full groups of Cantor minimal systems; Internat. J. Math. 17(2) 231–251; 2006 | VERIFIED |
| MorseHedlund (1940) | Symbolic Dynamics II. Sturmian Trajectories; Amer. J. Math. 62, first page 1; 1940 | VERIFIED (first page only; 1–42 (2nd), per sk-citations) |
| Ozawa | About the QWEP conjecture; Internat. J. Math. 15(05) 501–530; 2004 | VERIFIED |
| Pestov | Hyperlinear and sofic groups: a brief guide; Bull. Symbolic Logic 14(4) 449–480; 2008 | VERIFIED |
| Stepanov | On the normal structure of the general linear group over a ring; J. Math. Sci. 95(2) 2146–2155; 1999 | VERIFIED |
| Thom | Examples of hyperlinear groups without factorization property; Groups Geom. Dyn. 4(1) 195–208 | VERIFIED. Crossref's online date is 23 Dec 2009; volume 4 is 2010 |
| VershikGordon | no Crossref record (the query returned unrelated St. Petersburg Math. J. items) | NOT RE-VERIFIED here. The printed data rest on formalization.yaml and two citing sources (sk-referee-2, sk-panel-referee-2). Part 2 checks Pestov's bibliography entry |
| Brown | arXiv:math/0111286 (2001) | VERIFIED by sk-citations part 1 |
| AlekseevThom | arXiv:2608.05362 (2026) | title checked in part 2 |

## B. Background sources: verified data, with LaTeX bibitems ready for the note

The proposal decides which of these to cite. Everything below matches Crossref except the parts marked (2nd).

### B1. Property (T), simple Kazhdan groups
```latex
\bibitem{Kazhdan}
D.~A. Kazhdan, \emph{Connection of the dual space of a group with the structure of its closed subgroups},
Funct. Anal. Appl. \textbf{1} (1967), 63--65. \doi{10.1007/BF01075866}.

\bibitem{Gromov87}
M.~Gromov, \emph{Hyperbolic groups}, in: Essays in group theory, Math. Sci. Res. Inst. Publ. \textbf{8},
Springer, New York, 1987, 75--263. \doi{10.1007/978-1-4613-9586-7_3}.

\bibitem{Olshanskii93}
A.~Yu. Ol'shanskii, \emph{On residualing homomorphisms and $G$-subgroups of hyperbolic groups},
Internat. J. Algebra Comput. \textbf{3} (1993), 365--409. \doi{10.1142/S0218196793000251}.

\bibitem{CapraceRemy}
P.-E. Caprace and B.~R\'emy, \emph{Simplicity and superrigidity of twin building lattices},
Invent. Math. \textbf{176} (2009), 169--221. \doi{10.1007/s00222-008-0162-6}.

\bibitem{Ershov08}
M.~Ershov, \emph{Golod--Shafarevich groups with property~\textup{(T)} and Kac--Moody groups},
Duke Math. J. \textbf{145} (2008), 309--339. \doi{10.1215/00127094-2008-053}.
```
- Crossref prints "close subgroups" in Kazhdan's title. The printed English title reads "closed subgroups", so the bibitem uses "closed".
- Ershov's pages 309–339 are (2nd). Crossref gives volume 145(2) and no pages.

### B2. Sofic and hyperlinear groups, Connes embedding
```latex
\bibitem{Connes}
A.~Connes, \emph{Classification of injective factors. Cases $\mathrm{II}_1$, $\mathrm{II}_\infty$,
$\mathrm{III}_\lambda$, $\lambda\ne1$}, Ann. of Math. (2) \textbf{104} (1976), 73--115. \doi{10.2307/1971057}.

\bibitem{Gromov99}
M.~Gromov, \emph{Endomorphisms of symbolic algebraic varieties}, J. Eur. Math. Soc. \textbf{1} (1999),
109--197. \doi{10.1007/PL00011162}.

\bibitem{Weiss}
B.~Weiss, \emph{Sofic groups and dynamical systems}, Sankhy\=a Ser.~A \textbf{62} (2000), 350--359.

\bibitem{ElekSzabo}
G.~Elek and E.~Szab\'o, \emph{Hyperlinearity, essentially free actions and $L^2$-invariants.
The sofic property}, Math. Ann. \textbf{332} (2005), 421--441. \doi{10.1007/s00208-005-0640-8}.

\bibitem{CapraroLupini}
V.~Capraro and M.~Lupini, \emph{Introduction to sofic and hyperlinear groups and Connes' embedding
conjecture}, Lecture Notes in Math. \textbf{2136}, Springer, Cham, 2015. \doi{10.1007/978-3-319-19333-5}.

\bibitem{BrownOzawa}
N.~P. Brown and N.~Ozawa, \emph{$C^*$-algebras and finite-dimensional approximations},
Grad. Stud. Math. \textbf{88}, Amer. Math. Soc., Providence, RI, 2008. \doi{10.1090/gsm/088}.

\bibitem{KirchbergInvent}
E.~Kirchberg, \emph{On non-semisplit extensions, tensor products and exactness of group $C^*$-algebras},
Invent. Math. \textbf{112} (1993), 449--489. \doi{10.1007/BF01232444}.
```
- Connes: pages 73–115 are (2nd); Crossref gives first page 73.
- Weiss: no Crossref record. Part 2 checks the data against Pestov's bibliography.
- Capraro–Lupini: the series number 2136 is (2nd); Crossref gives the LNM book DOI and 2015.
- Rădulescu (the word "hyperlinear", arXiv:math/0004172): part 2.

### B3. Marked groups and LEF
```latex
\bibitem{Grigorchuk84}
R.~I. Grigorchuk, \emph{Degrees of growth of finitely generated groups and the theory of invariant means},
Izv. Akad. Nauk SSSR Ser. Mat. \textbf{48} (1984), 939--985; English transl., Math. USSR-Izv.
\textbf{25} (1985), 259--300. \doi{10.1070/IM1985v025n02ABEH001281}.

\bibitem{Champetier}
C.~Champetier, \emph{L'espace des groupes de type fini}, Topology \textbf{39} (2000), 657--680.
\doi{10.1016/S0040-9383(98)00063-9}.

\bibitem{Stepin}
A.~M. Stepin, \emph{Approximations of groups and group actions, the Cayley topology}, in: Ergodic theory
of $\mathbb Z^d$ actions (Warwick, 1993--1994), London Math. Soc. Lecture Note Ser. \textbf{228},
Cambridge Univ. Press, Cambridge, 1996, 475--484. \doi{10.1017/CBO9780511662812.021}.
```
- The Russian original data for Grigorchuk are (2nd); the English translation is Crossref-verified.
- Stepin's Crossref record is the chapter "Approximations of groups and group actions, Cayley topology", pp. 475–484, with no year. The volume and year are (2nd).

### B4. Topological full groups
```latex
\bibitem{GPS99}
T.~Giordano, I.~F. Putnam, and C.~F. Skau, \emph{Full groups of Cantor minimal systems},
Israel J. Math. \textbf{111} (1999), 285--320. \doi{10.1007/BF02810689}.

\bibitem{JuschenkoMonod}
K.~Juschenko and N.~Monod, \emph{Cantor systems, piecewise translations and simple amenable groups},
Ann. of Math. (2) \textbf{178} (2013), 775--787. \doi{10.4007/annals.2013.178.2.7}.
```

### B5. Property (T) for elementary groups over rings; normal structure; K-theory
```latex
\bibitem{Shalom99}
Y.~Shalom, \emph{Bounded generation and Kazhdan's property~\textup{(T)}}, Publ. Math. IH\'ES
\textbf{90} (1999), 145--168. \doi{10.1007/BF02698832}.

\bibitem{EJZK}
M.~Ershov, A.~Jaikin-Zapirain, and M.~Kassabov, \emph{Property~\textup{(T)} for groups graded by root
systems}, Mem. Amer. Math. Soc. \textbf{249} (2017), no.~1186. \doi{10.1090/memo/1186}.

\bibitem{Bass}
H.~Bass, \emph{$K$-theory and stable algebra}, Publ. Math. IH\'ES \textbf{22} (1964), 5--60.
\doi{10.1007/BF02684689}.

\bibitem{Vaserstein81}
L.~N. Vaserstein, \emph{On the normal subgroups of $\mathrm{GL}_n$ over a ring}, in: Algebraic $K$-theory
(Evanston, 1980), Lecture Notes in Math. \textbf{854}, Springer, Berlin, 1981, 456--465.
\doi{10.1007/BFb0089533}.

\bibitem{Suslin}
A.~A. Suslin, \emph{On the structure of the special linear group over polynomial rings},
Math. USSR-Izv. \textbf{11} (1977), 221--238. \doi{10.1070/IM1977v011n02ABEH001709}.

\bibitem{Milnor}
J.~Milnor, \emph{Introduction to algebraic $K$-theory}, Ann. of Math. Stud. \textbf{72}, Princeton Univ.
Press, Princeton, NJ, 1971. \doi{10.1515/9781400881796}.
```
- Milnor: Crossref gives 1972-12-31 for the De Gruyter record. The book appeared in 1971 (2nd).

### B6. Expanders
```latex
\bibitem{Margulis73}
G.~A. Margulis, \emph{Explicit constructions of expanders}, Problemy Pereda\v{c}i Informacii \textbf{9}
(1973), no.~4, 71--80; English transl., Problems Inform. Transmission \textbf{9} (1973), 325--332.

\bibitem{Lubotzky94}
A.~Lubotzky, \emph{Discrete groups, expanding graphs and invariant measures}, Progr. Math. \textbf{125},
Birkh\"auser, Basel, 1994. \doi{10.1007/978-3-0346-0332-4}.
```
- Margulis: no Crossref record. The data are (2nd); part 2 checks them against Kassabov's bibliography.

### B7. Dynamics: recurrence, complexity, Sturmian sets
```latex
\bibitem{GottschalkHedlund}
W.~H. Gottschalk and G.~A. Hedlund, \emph{Topological dynamics}, Amer. Math. Soc. Colloq. Publ.
\textbf{36}, Amer. Math. Soc., Providence, RI, 1955. \doi{10.1090/coll/036}.

\bibitem{MorseHedlund38}
M.~Morse and G.~A. Hedlund, \emph{Symbolic dynamics}, Amer. J. Math. \textbf{60} (1938), 815--866.
\doi{10.2307/2371264}.

\bibitem{Hedlund44}
G.~A. Hedlund, \emph{Sturmian minimal sets}, Amer. J. Math. \textbf{66} (1944), 605--620.
\doi{10.2307/2371769}.

\bibitem{CovenHedlund}
E.~M. Coven and G.~A. Hedlund, \emph{Sequences with minimal block growth}, Math. Systems Theory
\textbf{7} (1973), 138--153. \doi{10.1007/BF01762232}.
```
- First page only for Morse–Hedlund 1938 (815) and Hedlund 1944 (605); the last pages are (2nd).

### B8. Factors
```latex
\bibitem{MurrayvonNeumann}
F.~J. Murray and J.~von Neumann, \emph{On rings of operators.~IV}, Ann. of Math. (2) \textbf{44} (1943),
716--808. \doi{10.2307/1969107}.

\bibitem{McDuff}
D.~McDuff, \emph{Central sequences and the hyperfinite factor}, Proc. London Math. Soc. (3) \textbf{21}
(1970), 443--461. \doi{10.1112/plms/s3-21.3.443}.
```
- First page only for Murray–von Neumann (716); the last page is (2nd).

### B9. Embedding theorems
```latex
\bibitem{Higman61}
G.~Higman, \emph{Subgroups of finitely presented groups}, Proc. Roy. Soc. London Ser.~A \textbf{262}
(1961), 455--475. \doi{10.1098/rspa.1961.0132}.

\bibitem{BooneHigman}
W.~W. Boone and G.~Higman, \emph{An algebraic characterization of groups with soluble word problem},
J. Austral. Math. Soc. \textbf{18} (1974), 41--53. \doi{10.1017/S1446788700019108}.

\bibitem{Schupp}
P.~E. Schupp, \emph{Embeddings into simple groups}, J. London Math. Soc. (2) \textbf{13} (1976), 90--94.
\doi{10.1112/jlms/s2-13.1.90}.

\bibitem{Wilson80}
J.~S. Wilson, \emph{Embedding theorems for residually finite groups}, Math. Z. \textbf{174} (1980),
149--157. \doi{10.1007/BF01293535}.

\bibitem{Ore}
O.~Ore, \emph{Some remarks on commutators}, Proc. Amer. Math. Soc. \textbf{2} (1951), 307--314.
\doi{10.1090/S0002-9939-1951-0040298-4}.

\bibitem{KionkeSchesler}
S.~Kionke and E.~Schesler, \emph{From telescopes to frames and simple groups}, J. Comb. Algebra (2024),
online 15 November 2024. \doi{10.4171/JCA/103}. arXiv:2304.09307.
```
- Kionke–Schesler: Crossref gives the title, journal, online date and DOI, but no volume or pages. Part 2 checks the arXiv id against the title.
- Wilson's initials "J. S." are (2nd).

### B10. Approximation and stability (background only)
```latex
\bibitem{ArzhantsevaPaunescu}
G.~Arzhantseva and L.~P\u{a}unescu, \emph{Linear sofic groups and algebras}, Trans. Amer. Math. Soc.
\textbf{369} (2017), 2285--2310. \doi{10.1090/tran/6706}.

\bibitem{BeckerLubotzky}
O.~Becker and A.~Lubotzky, \emph{Group stability and property~\textup{(T)}}, J. Funct. Anal.
\textbf{278} (2020), 108298. \doi{10.1016/j.jfa.2019.108298}.

\bibitem{Steinberg10}
B.~Steinberg, \emph{A groupoid approach to discrete inverse semigroup algebras}, Adv. Math.
\textbf{223} (2010), 689--727. \doi{10.1016/j.aim.2009.09.001}.
```
- Arzhantseva–Păunescu: Crossref's date is online 8 April 2016; volume 369(4) is the 2017 print issue.

## C. Not found or not settled in this part
- Rădulescu (arXiv:math/0004172) and Kun–Thom: arXiv-only in this pass; part 2 checks them.
- Hall 1974 (two-generator simple overgroups): not queried. Schupp 1976 is the Crossref-verified entry; what it proves is checked in part 2 before any citation.
- Taylor or Artin as a textbook source for "transvections generate SL_d(F_q), and PSL_d(F_q) is simple for d ≥ 3": part 2.
