# sk-review-6, part 2: queue items sk-lit-novelty-2, sk-lit-credit-audit, sk-intro-writer (2026-09-13)

Lane sk-verify-6 (literature and credit verifier).

**Queue:** `sk/queue/sk-verify-6.txt`, entries 1–3.

**Method:** sources fetched on MSI into `/scratch.global/sauer354/sk/sk-verify-6/`.
- arXiv e-print TeX sources were grepped for statements and theorem counters.
- Springer PDFs (Elek–Szabó, Wilson) were read locally as page images.
- Crossref records came from api.crossref.org; zbMATH records from api.zbmath.org.
- I checked everything independently of the lanes under review.

**Subject note:** main's `simple_kazhdan_sofic_group.tex` at e80dcf20ad (rev2).

## Verdict summary

| # | Item | Verdict |
|---|---|---|
| 1 | sk-lit-novelty-2 (`research/artifacts/sk-lit-novelty-2-2026-09-13.md`): novelty table N1–N3, credit sentences (a)–(d), bibitems | PASS. Two bibliographic data points rest on secondary sources (§1.4). |
| 2 | sk-lit-credit-audit (`research/artifacts/sk-lit-credit-audit-proposal-2026-09-13.md`, and the artifact §1 table): P1–P7 plus the rev3 data | PASS P1–P4, P6, P7. P5 PASS with one title FIX. Two recalled flags are resolved here, four remain (§2.8). |
| 3 | sk-intro-writer (`research/artifacts/sk-intro-writer-proposal-2026-09-13.md`): credit and background sentences of Variant I | PASS. It is NOT on main yet: I reviewed the lane-dir copy (12,743 bytes, 20:00). One optional precision (§3). |

No FAIL.

## 1. sk-lit-novelty-2

### 1.1 Kionke–Schesler
Source: arXiv:2304.09307v1 TeX (`tree-permutations.tex`, e-print dated 20 Apr 2023).

**Numbering:** `\newtheorem{theorem}{Theorem}[section]`. §1 Introduction (l.135) has exactly two numbered theorems before l.195, at l.161 and l.187, so the intro embedding theorem is Theorem 1.2. PASS.
- Its target, `thm:embeddings-into-simple-groups`, is at l.2345. The e-print has a commented-out `%\section` at l.1940, so the real section there is §9, which fits the lane's "Theorem 9.14". I did not count within §9.

**Theorem 1.2, verbatim (l.187–195):** "Let $H$ be a finitely generated, residually finite (amenable) group. There is a finitely generated, residually finite (amenable) group $G$ and an infinite, simple, (amenable) $\LEF$ group $Q$ such that (1) there is an embedding $\iota \colon H \rightarrow G$, (2) there is a projection $\pi \colon G \rightarrow Q$, (3) the composition $\pi \circ \iota$ is injective." Matches the lane's quote. PASS.

**Abstract (l.128):** "We show that every finitely generated residually finite (amenable) group embeds into a finitely generated (amenable) $\LEF$ simple group." PASS.

**Intro, verbatim (l.173–174):** "It is an easy consequence of the Baer-Schreier-Ulam theorem~\cite{Baer34} that every group $G$ embeds into a simple group $Q$. In the case where $G$ is countable, it was shown by Gorju\v{s}kin~\cite{Gorjushkin74} that $Q$ can be chosen to be $2$-generated (see also \cite{Schupp76})." PASS.
- The `.bbl` matches the lane's references: `BelkZaremsky22` (Geom. Topol. 26 (2022) 1189–1223), `DarbinyanSteenbock22` (J. Lond. Math. Soc. (2) 105 (2022) 2011–2045), `Osin10` (Ann. of Math. (2) 172 (2010) 1–39) and `Schupp76`.

### 1.2 Wilson
Math. Z. 174, 149–157 (1980), Springer PDF, p. 149, verbatim: "Theorem A. Every countable residually finite group G can be embedded in a 2-generator residually finite group Ĝ." PASS for credit sentence (b).

### 1.3 Crossref records

| key | record | proposal bibitem |
|---|---|---|
| KionkeSchesler | "From telescopes to frames and simple groups", J. Combinatorial Algebra, 2024; no volume or pages in the record | matches; flag stands |
| Schupp | "Embeddings into Simple Groups", J. London Math. Soc. s2-13(1), 90–94, 1976 | matches |
| Wilson | "Embedding theorems for residually finite groups", Math. Z. 174(2), 149–157, 1980 | matches |
| Ore | "Some remarks on commutators", Proc. AMS 2(2), 307–314, 1951 | matches |

### 1.4 Credit sentence (a), and secondary data
- **"Every countable group embeds in a finitely generated simple group [Gorjuskin, Schupp]":** PASS, supported by Kionke–Schesler's intro quoted above, which says 2-generated, so the sentence is weaker than the source and true.
  - **Secondary:** Schupp's paper was not opened (Wiley returned HTML from MSI).
  - **Secondary:** the Gorjuškin data (Mat. Zametki 16 (1974), 231–235, MR 382456) agrees with Kionke–Schesler's `.bbl`, but the zbMATH API search returned nothing, so it is not independently checked.
- **"Kionke and Schesler proved … [Theorem 1.2]":** PASS. Q is finitely generated as a quotient of the finitely generated G, and H embeds in Q.
- **"The next corollary adds property (T) and applies to every LEF group. Since LEF passes to subgroups, it characterizes LEF groups.":** PASS as credit wording. It claims no priority for simple Kazhdan hosts.
- **Item (d), the do-not-write list:** correct and consistent with risk R1.
- **Risk R1, bounded re-check:** three arXiv API abstract queries (`"property (T)" AND simple AND embed`; `Kazhdan AND simple AND "countable group"`; `"simple groups with property (T)"`, up to 40 results each). No abstract combines "embed", "simple" and (T) or Kazhdan. This is not a full search, so R1 stays open, as the lane says.

## 2. sk-lit-credit-audit

### 2.1 P1, Kazhdan
- Crossref: Funct. Anal. Appl. 1(1), 63–65, 1967. The record title reads "…its close subgroups", a metadata typo; the bibitem correctly writes "closed".
- PASS.

### 2.2 P2, origins of the terms
Pestov, arXiv:0804.3968v8 `hypsof.tex`, verbatim:
- l.378: "…Gromov's article \cite{gromov99} where the concept of a sofic group was first introduced (without a name of its own) in order to attack Gottschalk's Surjunctivity Conjecture … The current expression ``sofic group'' was coined by Benjy Weiss \cite{weiss}."
- l.385: "The expression ``hyperlinear group'' belongs to Radulescu \cite{radulescu00}."

The proposed sentence "Hyperlinear groups were named by Rădulescu, and sofic groups were introduced by Gromov and named by Weiss." is faithful. PASS.

Bibitems:
- **Gromov:** Crossref, JEMS 1(2), 109–197, 1999. PASS.
- **Weiss:** zbMATH 1148.37302, "Sofic groups and dynamical systems", Sankhyā Series A 62(3), 350–359, 2000. PASS.
- **Rădulescu:** zbMATH 1199.46137, title as in the bibitem, pp. 173–185, book record "Bucharest: Theta", 2008, ISBN 978-973-87899-2-0. The book title ("Hot topics in operator theory") and the series number (Theta Ser. Adv. Math. 9) are NOT in the record. FLAG stands.

### 2.3 P3, Elek–Szabó
Math. Ann. 332, 421–441 (2005), Springer PDF read locally:
- p. 421: "In [18] the authors studied the limit groups of finite marked groups, which they called LEF-groups."
- p. 422: "It is known [8],[19],[6] that the LEF-groups are sofic."
- p. 423: "We shall prove that countable sofic groups are hyperlinear (Theorem 2)."
- p. 430, §3: "Theorem 2. All countable sofic groups are hyperlinear."

The locator [Theorem 2] is correct. Crossref gives 332(2), 421–441. Keeping [Pestov, Example 4.5] for LEF ⇒ sofic is correct (part 1 §3). PASS.

### 2.4 P4, marked groups
- Crossref: Grigorchuk, Math. USSR-Izv. 25(2), 259–300, 1985; Champetier, Topology 39(4), 657–680, 2000.
- Both are the standard references for the space of marked groups. I did not re-read their content.
- PASS.

### 2.5 P5, Margulis
- zbMATH 0312.22011: "Explicit construction of a concentrator", Problemy Peredachi Informatsii 9(4), 71–80, 1973. The attribution of (T) ⇒ expanders to Margulis is standard. PASS.
- **FIX (minor):** the proposal's bibitem title "Explicit construction of concentrators" does not match the zbMATH record ("… of a concentrator"). Use the zbMATH title, or the Russian original's transliteration, since the bibitem cites the Russian journal.

### 2.6 P6, McDuff and Murray–von Neumann
- **McDuff:** Crossref, Proc. LMS (3) 21(3), 443–461, 1970. PASS.
- **Murray–von Neumann:** Crossref gives Ann. of Math. 44(4), start page 716. zbMATH gives pp. 716–808, which resolves the lane's end-page FLAG. PASS.

### 2.7 P7, Hedlund and Lothaire
- **Hedlund:** Crossref, Amer. J. Math. 66(4), start page 605. zbMATH gives pp. 605–620, which resolves the end-page FLAG. PASS.
- **Lothaire:** Crossref for the book (CUP 2002, doi 10.1017/CBO9781107326019) and for the chapter "Sturmian Words", pp. 45–110. PASS. The series number (Encyclopedia Math. Appl. 90) is not in the record: FLAG stands.
- **Justification not verified:** the artifact's table says "MorseHedlund 1940 alone names Sturmian trajectories but does not give the codings as stated". I did not open Morse–Hedlund 1940, and that paper does treat Sturmian trajectories through rotation numbers. So do not repeat this sentence anywhere. The proposal itself only ADDS Hedlund 1944 and Lothaire while keeping MorseHedlund, which is harmless whichever way that point falls.

### 2.8 Rev3 data (artifact §4) and remaining flags
- **Crossref:** Archbold–Spielberg, Proc. Edinburgh Math. Soc. 37(1), 119–124, 1994; Milnor, Introduction to Algebraic K-Theory (AM-72), Princeton 1972; Stepin, Russian Math. Surveys 38(6), 131–132, 1983.
- **Flags that remain open:**
  - the Rădulescu book title and series number;
  - the Lothaire series number;
  - the Milnor locator for Whitehead's lemma;
  - the Kionke–Schesler volume and pages.
- **Resolved here:** the Murray–von Neumann and Hedlund end pages.

## 3. sk-intro-writer (lane-dir copy; not landed on main at review time)
- **Ozawa clause** ("Ozawa stated the hyperlinear form in 2003, noting that the full C*-algebra of such a group cannot have the local lifting property [p. 527]"): PASS on content. Verbatim remark after Theorem 7.4 (part 1 §2): "By the above theorem, the full C*-algebra C*Γ of such a group Γ cannot have the LLP." Journal p. 527 is still indirect.
- **Pestov–Kwiatkowska paraphrase:** PASS. From the arXiv:0911.4266 e-print `cornell.tex`, l.1213 verbatim: "It is in view of such results that Ozawa asked whether every finitely generated Kazhdan group that is sofic is residually finite. A negative answer was announced by Thom \cite{thom}. Consequently, a hope to use property $(T)$ in order to construct non-hyperlinear groups is a bit diminished now, but surely not gone, as it remains in particular unknown whether finitely generated simple Kazhdan groups can be hyperlinear/sofic."
  - The proposal's "Pestov and Kwiatkowska noted that simple Kazhdan groups still left open the possibility of using property (T) to construct groups that are not hyperlinear" is faithful.
  - **Optional precision:** "finitely generated simple Kazhdan groups", as printed.
- **PestovKwiatkowska bibitem:** PASS. Crossref for doi 10.1017/CBO9781139208574.006 gives "An introduction to hyperlinear and sofic groups", in "Appalachian Set Theory 2006–2012", pp. 145–186. The arXiv jref gives LMS Lecture Note Ser. 406, CUP (2012), pp. 145–186.
- **Kionke–Schesler credit** ("For residually finite groups, and without property (T), this is a theorem of Kionke and Schesler"): PASS (§1.1). It credits the embedding direction for RF input.
- **Matui background** ("The derived subgroups of these topological full groups are infinite, finitely generated and simple for minimal subshifts [Matui]"): PASS. From the arXiv math/0404117 e-print `srtfg.tex`, counter `thm[section]`:
  - Theorem 4.9 (l.795), verbatim: "Let $\xp$ be a Cantor minimal system. The commutator subgroup $D([[\phi]]_0)$ is simple."
  - Theorem 5.4 (l.955), verbatim: "Let $\xp$ be a Cantor minimal system. The commutator subgroup $D([[\phi]]_0)$ is finitely generated if and only if $\xp$ is conjugate to a minimal subshift."
  - Juschenko–Monod's intro confirms the identification with the commutator subgroup of the full group: "Matui proved that the commutator subgroup of $\full{T}$ is simple for any minimal Cantor system, see Theorem~4.9 in~\cite{Matui06} and the remark preceding it."
  - The existing main locator "[Lemma 3.4 and Theorem 4.9]" also checks: Lemma 3.4 (l.513) is `DAFsimple`, "the commutator subgroup D(G) equals to the union ⋃H_m. Furthermore, D(G) is simple if the Bratteli diagram B is simple". I did not re-read the proof pattern behind "in the same way".
- **Juschenko–Monod** ("but they are amenable [JuschenkoMonod], so they do not have property (T)"): PASS.
  - arXiv:1204.2132 e-print `jm_15.tex`, intro theorem environment `itheorem`, verbatim: "The topological full group of any minimal Cantor system is amenable."
  - Subgroups of amenable groups are amenable, and infinite amenable groups do not have (T).
  - Crossref: Ann. of Math. 178(2), 775–787, 2013, doi 10.4007/annals.2013.178.2.7, matching the bibitem.
  - The letter "A" of the environment was not checked; the note text uses no locator.
- **Results paragraph:**
  - the LEF characterization and the Turing clause restate reviewed nodes (not literature);
  - the universal host clause is correctly gated on sk-verify-4.
- No Codex, OpenAI or Astra mentions. The Origin paragraph is untouched.

## 4. For main
- All three proposals are safe for rev3 on credit and bibliography, subject to:
  - the P5 title fix;
  - carrying the four open flags into sk-lit-locators;
  - optionally, "finitely generated" in the Pestov–Kwiatkowska clause.
- No Cairn node was changed by this part.
