# sk-novelty-db: database novelty search for the simple Kazhdan note (2026-09-14)

Lane sk-novelty-db, for sk-referee-top's R3 through main.
- **Subject:** rev4.5 of `simple_kazhdan_sofic_group.tex` (md5 29d63f7944bccccbf9a91b0b2714c0b4).
- **Scope:** literature only. No mathematics; no Cairn claim nodes touched.
- **Earlier lanes:** sk-prior-art-2/3, sk-lit-novelty-2 and sk-perfect-b used web searches and e-print greps; none queried MathSciNet or zbMATH.

## 0. Verdict
- **No PRIOR found** for any of the three targets:
  - (i) an infinite simple Kazhdan group that is sofic, hyperlinear or LEF;
  - (ii) "a f.g. group is LEF iff it is a subgroup of a simple Kazhdan LEF group";
  - (iii) EL_n over crossed products of minimal subshifts being simple and Kazhdan.
- **New relative to the earlier lanes:**
  - the first MathSciNet (25 queries) and zbMATH (15 queries) searches;
  - forward-citation scans of EJZ 2010, GM 2014, Kionke–Schesler 2024, Thom 2010, Coulon–Fournier-Facio 2023 and Alekseev–Thom 2026.
- **Two new RELATED papers:** Thomas–Williams 2016 and Thomas 2013, on the Borel complexity of isomorphism and bi-embeddability for f.g. simple and Kazhdan groups, built from topological full groups of minimal subshifts. No change to the paper is required.
- NOT FOUND is bounded by §1.

## 1. Search bound
- **MathSciNet.**
  - Reachable from MSI with no credentials (institutional IP), through `mathscinet.ams.org/mathscinet/api/publications/search`.
  - 25 distinct any-field queries (§4). Review texts were not retrieved: the API format endpoint returned empty fields.
- **zbMATH Open API** (`api.zbmath.org/v1/document/_search`): 15 queries. 9 returned HTTP 404 (query syntax), 6 answered (§4).
- **arXiv.**
  - The export API from MSI returned HTTP 429 for all 6 queries.
  - arxiv.org/search through the fetch tool: 6 queries, 0 results each (§4).
- **Forward citations** (Semantic Scholar Graph API; all titles read):
  - EJZ 2010, Invent. Math. 179: 97 citing works;
  - Grigorchuk–Medynets 2014, Sb. Math. 205: 24;
  - Kionke–Schesler, doi 10.4171/JCA/103 and arXiv:2304.09307: 2 each;
  - Thom 2010, GGD 4: 43;
  - Coulon–Fournier-Facio arXiv:2312.11684: 4;
  - Alekseev–Thom arXiv:2608.05362: 2;
  - Elek–Szabó 2005: 194. Keyword filter only (title or abstract containing "simple", a (T) word and an approximation word): 1 hit, a false positive (arXiv:1509.03189).
  - Abstracts were fetched for 16 candidates.
  - Semantic Scholar coverage is incomplete for recent papers; the Kionke–Schesler count of 2 suggests this.
- **OpenAlex:** HTTP 429 on the first request; not used.
- **Web searches:** 3.
- **Read at source:**
  - Thomas–Williams accepted manuscript (Rutgers repository PDF): l.1–125, and every theorem line;
  - Thomas 2013 (Rutgers PDF): l.36–95;
  - BLSW arXiv:2303.08943: pp. 1–3, plus a full-text grep;
  - Akhtiamov–Dogon arXiv:2010.10304 and Becker–Lubotzky arXiv:1809.00632: full-text greps.
- **Not done:** MathSciNet review texts; Google Scholar; Russian sources; OpenAlex.

## 2. Classification

### PRIOR
None.

### RELATED (not prior)

**Thomas–Williams, "The bi-embeddability relation for finitely generated groups II", Arch. Math. Logic 55 (2016) 385–396, MR3490909.**
- **What it proves:**
  - Abstract, verbatim: "We study the isomorphism and bi-embeddability relations on the spaces of Kazhdan groups and finitely generated simple groups."
  - Thm 1.5: the isomorphism relation on the space of Kazhdan groups is a weakly universal countable Borel equivalence relation.
  - Intro: by Thomas [22], the isomorphism relation on f.g. simple groups is not smooth, "and … this implies that the bi-embeddability relation on G_sim is also not smooth."
  - Conjecture 1.8: both relations on f.g. simple groups are universal.
- **Bearing:** Corollary 5, the clause "continuum many G_X, none a subgroup of another".
  - A non-smooth countable Borel equivalence relation has continuum many classes. So continuum many f.g. simple groups, pairwise not bi-embeddable, follow from these papers.
  - The note's clause is stronger: an antichain under embeddability, inside simple Kazhdan LEF groups. Not prior.

**S. Thomas, "Topological full groups of minimal subshifts and just-infinite groups", Proc. 12th Asian Logic Conf., World Sci. (2013) 298–313, MR3289549.**
- **What it proves:**
  - Thm 1.2: "The isomorphism relation on the space G_sim of infinite finitely generated simple groups is not smooth."
  - Method: TF(X)′ for minimal subshifts, with TF(X)′ ≅ TF(Y)′ iff X and Y are flip conjugate (GPS, Bezuglyi–Medynets, Matui), and non-smoothness of flip conjugacy for Toeplitz subshifts.
  - Conjecture 1.4 (isomorphism on f.g. Kazhdan groups is nonsmooth) is settled by Thomas–Williams Thm 1.5.
- **Bearing:** the Questions paragraph "Does G_X ≅ G_Y imply that X and Y are flip conjugate". This is the same rigidity input Thomas uses for derived topological full groups. A yes would give the analogous Borel-complexity statement for f.g. simple Kazhdan LEF groups.

**Other related papers:**

| Paper | Content | Why not prior |
|---|---|---|
| Chatterji–Kassabov, arXiv:2601.22907 (2026) | Abstract: "a finitely presented group with property (T) … using an generalization of Hall embedding theorem, where property (T) is added at the expense of weakening the simplicity requirement" | Not simple; no approximation |
| Caprace–Kassabov arXiv:2210.00730; Caprace–Conder–Kaluba–Witzel arXiv:2011.09276; Bartholdi–Kassabov arXiv:2308.14529 | Kazhdan (often hyperbolic) groups with infinitely many alternating or finite simple quotients | Context for Theorem 1's finite simple models; these groups are not simple |
| Elek arXiv:1211.0621 | Full groups of sofic equivalence relations are sofic; a short proof of Grigorchuk–Medynets's LEF theorem | LEF mechanism only; no (T) |
| Kun–Thom arXiv:2608.06222; Fournier-Facio arXiv:2608.02025 | Nonsofic groups from Kazhdan elementary groups | Open-status context; no sofic simple Kazhdan example |
| Juschenko–Monod 2013, MR3071509 | F.g. simple amenable groups | Amenable, so no (T) |
| Mimura–Sako arXiv:1310.4736, 1804.10614 | Cayley accumulation points and coarse geometry | Context for marked limits |

### NOT (keyword matches only)
- **Bader–Lubotzky–Sauer–Weinberger,** J. Anal. Math. 151 (2023), arXiv:2303.08943, MR4682943: stability of lattices. A full-text grep finds no "sofic" or "hyperlinear"; "simple" occurs only for Lie groups.
- **Akhtiamov–Dogon,** PAMS 150 (2022), arXiv:2010.10304, MR4375766: uniform HS stability. The only hit is "or even hyperlinear groups" (l.106).
- **Becker–Lubotzky,** arXiv:1809.00632, MR4027744: infinite hyperlinear or sofic groups with (T) are not stable. No simple example.
- **Dogon,** arXiv:2211.10492, MR4660281: conditional non-hyperlinear groups.
- **Fournier-Facio,** arXiv:2512.09180: f.p. Frobenius-stable (T) groups far from (T₂). Abstract only; no simple or approximable-simple claim.
- **By topic, not opened:** Hyde–Lodha 2019 (MR3994586), André–Guirardel 2024 (MR4797534), Monod 2017 (MR3654077), Juschenko–de la Salle 2015 (MR3351042), S. Thomas 2012 (MR2914864), Kida's survey (zbl 1512.37002), Matte Bon–Triestino 2020 (MR4157429), Nathanson (MR4043258), de Cornulier–Guyot–Pitsch 2007 (zbl 1132.20018), Stalder 2009 (zbl 1220.20040), Fournier-Facio–Sauer arXiv:2601.00074.
- **Citing works:** none of the titles or fetched abstracts claims (i)–(iii), among the EJZ, GM, Kionke–Schesler, Thom, CFF and Alekseev–Thom citers.

## 3. For the paper
- **No change required.** The sentence "Simple hosts with only one of property (T) and LEF were known" and the open-status record stand within this bound.
- **Optional, main's call; about 2 lines;** after the continuum clause of Corollary 5, or in the Questions paragraph on flip conjugacy:
  `For derived topological full groups of minimal subshifts, the isomorphism rigidity was used by Thomas to show that isomorphism of finitely generated simple groups is not smooth~\cite{ThomasSubshifts}.`
  - Bibitem data from the Thomas 2013 PDF and the MathSciNet record: S. Thomas, *Topological full groups of minimal subshifts and just-infinite groups*, in: Proceedings of the 12th Asian Logic Conference, World Sci. Publ., Hackensack, NJ, 2013, 298–313.
  - Recommendation: skip it for length. The note claims no novelty for the continuum clause.

## 4. Queries, verbatim, with hit counts

**MathSciNet (25 distinct):**
- sofic AND simple AND Kazhdan (3)
- hyperlinear AND simple AND Kazhdan (2)
- "property (T)" AND simple AND sofic (1)
- "property (T)" AND simple AND hyperlinear (1)
- "locally embeddable" AND simple AND "property (T)" (0)
- LEF AND simple AND Kazhdan (1, algebraic geometry)
- "Steinberg algebra" AND Kazhdan (0)
- "crossed product" AND "elementary" AND "property (T)" AND simple (1, a proceedings volume)
- subshift AND Kazhdan (2)
- "full group" AND Kazhdan AND simple (4)
- "space of marked groups" AND simple AND Kazhdan (1)
- "infinite simple" AND "property (T)" (6)
- "simple group" AND hyperlinear (0)
- "simple group" AND sofic AND "property (T)" (0)
- "locally embeddable into finite groups" AND simple (3)
- "bi-embeddability" AND "simple groups" (1)
- "elementary group" AND ("crossed product" OR "Steinberg algebra" OR "Leavitt") (2, unrelated)
- "topological full group" AND "property (T)" (0)
- "limit of finite simple groups" (2, locally finite groups)
- "Leavitt path algebra" AND ("elementary" OR "Steinberg group") AND simple (0)
- "Steinberg algebra" AND ("general linear" OR "normal subgroups") (0)
- "crossed product" AND "general linear group" AND "normal subgroups" (1, unrelated)
- Kazhdan AND "universal lattice" AND simple (3)
- "hyperlinear" AND "property (T)" (4)
- "LEF" AND "property (T)" (0)

**zbMATH, answered:**
- Kazhdan & simple & (sofic | hyperlinear) (1)
- "property (T)" & (subshift | "Cantor minimal" | "full group") & simple (4)
- simple & Kazhdan & ("marked groups" | "limit of finite") (3)
- sofic & simple & Kazhdan (1)
- LEF & simple & Kazhdan (1, unrelated)
- subshift & Kazhdan (1)

**zbMATH, HTTP 404:**
- "property (T)" & simple & (sofic | hyperlinear)
- "property (T)" & simple & ("locally embeddable" | LEF)
- "property (T)" & ("Steinberg algebra" | "crossed product") & (elementary | "EL_n" | "Steinberg group")
- "property T" & simple & (sofic | hyperlinear)
- "locally embeddable" & simple & Kazhdan
- "Steinberg algebra" & Kazhdan
- "crossed product" & Kazhdan & elementary
- "topological full group" & Kazhdan
- "infinite simple" & Kazhdan & (sofic | hyperlinear | LEF | approximation)

**arxiv.org/search (0 results each):**
- abstract: sofic simple Kazhdan
- abstract: "property (T)" simple sofic
- abstract: hyperlinear simple "property (T)"
- abstract: "locally embeddable" simple "property (T)"
- all: "Steinberg algebra" Kazhdan
- abstract: "crossed product" "property (T)" "elementary group"

**Web searches:**
- infinite simple group property (T) sofic example 2026 arXiv
- "elementary group" crossed product minimal subshift property (T) simple
- "simple" "Kazhdan" group "locally embeddable into finite groups" OR "LEF" OR "sofic" September 2026

Raw outputs are on MSI in `/scratch.global/sauer354/sk/novelty-db/`: `mathscinet.json`, `zbmath.json`, `tw2.txt`, `thomas-subshifts.txt`, `blsw.txt`, `ad.txt`, `bl.txt`.
