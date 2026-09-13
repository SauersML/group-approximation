# sk-citations, part 1: bibliographic metadata of `simple_kazhdan_sofic_group.tex` (2026-09-13)

Lane sk-citations (SK swarm). Subject: the disk version of the note, frozen as `manuscript-disk-1646.tex`
(md5 7b3dc4ec92b4581553bc0dc2b0edcb99, 340 lines). This part checks the bibliographic data of every bibitem
(l.271-338). Part 2 checks what each source says against the sentence that cites it. The proposal artifact
`sk-citations-proposal-2026-09-13.md` collects the fixes.

Sources used: Crossref REST API (`api.crossref.org/works/<doi>` and `query.bibliographic`), arXiv abstract
pages, and the publishers' pages returned by search. Crossref records only the first page for Morse–Hedlund,
so its last page comes from secondary sources (MathSciNet relay MR0000745, Semantic Scholar).

## Verdicts per bibitem

| key | note's data | verified data | verdict |
|---|---|---|---|
| Brown | arXiv:math/0111286 (2001), title as printed | arXiv:math/0111286, "Tracial invariants, classification and II_1 factor representations of Popa algebras", v1 27 Nov 2001, v2 12 Mar 2002, v3 13 Mar 2002; no journal reference | VERIFIED (no journal version located) |
| BCFS | Semigroup Forum 88 (2014) 433-452, arXiv:1204.3127 | Semigroup Forum 88(2) (2014) 433-452, doi:10.1007/s00233-013-9546-z | VERIFIED; DOI available |
| ClarkEdie | Algebr. Represent. Theory 18 (2015) 907-916, arXiv:1403.4684 | Algebras and Representation Theory 18(4) (2015) 907-916, doi:10.1007/s10468-015-9522-2 | VERIFIED; DOI available |
| EJZ | Invent. Math. 179 (2010) 303-347, doi:10.1007/s00222-009-0218-2 | Inventiones mathematicae 179(2) (2010) 303-347, same DOI (online 25 Sep 2009) | VERIFIED |
| GM | Sb. Math. 205 (2014) 843-861, doi:10.1070/SM2014v205n06ABEH004400 | Sbornik: Mathematics 205(6) (2014) 843-861, same DOI | VERIFIED |
| MorseHedlund | Amer. J. Math. 62 (1940) 1-42, doi:10.2307/2371431 | "Symbolic Dynamics II. Sturmian Trajectories", Amer. J. Math. 62 (1940), first page 1 (Crossref), pp. 1-42 (secondary), same DOI | VERIFIED |
| Nekrashevych | Internat. J. Algebra Comput. 26 (2016) 375-397, arXiv:1501.00722 | IJAC 26(2) (2016) 375-397, doi:10.1142/S0218196716500156 | VERIFIED; DOI available |
| Ozawa | Internat. J. Math. 15 (2004) 501-530, doi:10.1142/S0129167X04002417 | IJM 15(05) (July 2004) 501-530, same DOI; arXiv:math/0306067 v1 3 Jun 2003 | VERIFIED |
| Pestov | Bull. Symbolic Logic 14 (2008) 449-480, doi:10.2178/bsl/1231081461 | BSL 14(4) (Dec 2008) 449-480, same DOI; arXiv:0804.3968 v8 (4 Aug 2008) "incorporates minor corrections made in the Bulletin of Symbolic Logic galley proofs" | VERIFIED |
| Steinberg | arXiv:1408.6014 (2014) | published: J. Pure Appl. Algebra 220(3) (2016) 1035-1054, doi:10.1016/j.jpaa.2015.08.006 | FIX: cite the journal version |
| Stepanov | Zap. Nauchn. Sem. POMI 236 (1997) 166-182; J. Math. Sci. 95 (1999) 2146-2155, doi:10.1007/BF02169976 | J. Math. Sci. 95(2) (1999) 2146-2155, same DOI; Springer page: "Translated from Zapiski Nauchnykh Seminarov POMI, Vol. 236, 1997, pp. 166-182" | VERIFIED |
| Thom | Groups Geom. Dyn. 4 (2010) 195-208, doi:10.4171/GGD/80 | Groups, Geometry, and Dynamics 4(1) (2010) 195-208, same DOI | VERIFIED |

## Candidate additional sources (decided in the proposal)

- Vershik–Gordon, the source of the notion of LEF groups: A. M. Vershik and E. I. Gordon, "Groups that are locally
  embeddable in the class of finite groups", Algebra i Analiz 9(1) (1997) 71-97; English transl. St. Petersburg
  Math. J. 9(1) (1998) 49-67. Crossref lookup was rate-limited (HTTP 429); the data above follow the repository's
  earlier verification (memory record of 09-13) and several citing papers. The note defines LEF at l.119-120
  without a source.
- Lothaire, *Algebraic Combinatorics on Words*, Cambridge University Press 2002, doi:10.1017/CBO9781107326019;
  Chapter 2, "Sturmian Words" (J. Berstel and P. Séébold), pp. 45-110, doi:10.1017/CBO9781107326019.003. This
  is a textbook source for the two Sturmian facts at l.253-256 (factors from the rotation partition; the balance
  property giving the minimum number of 1's). Part 2 checks the exact statements.

## What part 1 does not settle

- Whether each cited theorem number and page (EJZ Thm 1.1, Thom Thm 1.4, Brown §11 Question 7, Ozawa p. 527)
  and each attribution sentence match the source text. That is part 2, from the arXiv PDFs on MSI.
