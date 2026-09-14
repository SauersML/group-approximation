# sk-prior-art-2: adversarial novelty grades for the headline claims (2026-09-13)

Lane sk-prior-art-2 (roster H, wave 10), ~21:45–22:20 CDT.
- **Subject:** rev3 on main (9047d0d3c9, md5 274f19367f7f706b05c017af721c3884); line numbers below refer to it. Also the rev4 plan: decision log items 71, 79 and 83 in `wip/simple-kazhdan-note/decisions.md`, and the landed candidate proposals.
- **Scope:** literature and credit only. Nothing here is mathematics, and no Cairn claim nodes are touched.
- **Grades:** KNOWN (cite) / PARTIALLY KNOWN / NOT FOUND (within the bound of §0).

## 0. Search bound (read before relying on any NOT FOUND)
**This lane.**
- 12 web searches (US engine, 13 Sep 2026), covering:
  - simple Kazhdan hosts via small cancellation;
  - 2025–2026 answers to Pestov 9.1;
  - LEF-input simple LEF hosts;
  - infinite simple Kazhdan marked limits;
  - distortion in full groups and automorphism groups of subshifts;
  - universal separable R^ω-embeddable factors;
  - universal simple hosts for linear groups;
  - Nekrashevych alternating full groups;
  - soficity of Kac–Moody lattices.
- Opened (A = read through the fetch tool, which summarizes with a small model; V = verbatim on page images):
  - Coulon–Fournier-Facio arXiv:2312.11684: abstract, plus the HTML introduction (Theorem 1.5, Remark 4.5) (A).
  - Nicoara–Popa–Sasyk arXiv:math/0401139v8: abstract and HTML introduction (A).
  - Peterson arXiv:2605.16669: HTML abstract, introduction, Theorem 1.5 (A).
  - Chifan–Drimbe–Ioana 2205.07442 (A); Chifan–Ioana–Osin–Sun 2304.07455 (A).
  - Osin math/0411039v2 HTML introduction (A).
  - Cyr–Franks–Kra–Petite 1611.05913 (A); Callard–Salo 2208.00685 (A).
  - Ioana–Tucker-Drob 2512.04531 (A); Mimura–Ozawa–Sako–Suzuki 1402.5105 (A); Popa math/0209130 abstract (A).
  - Hull arXiv:1308.4345v2, pp. 1–5 (V).
- Crossref:
  - Hull, Groups Geom. Dyn. 10(4), 1077–1119, doi 10.4171/ggd/377 (Crossref year 2017);
  - Cyr–Franks–Kra–Petite, J. Mod. Dyn. 13(1) (2018) 147–161, doi 10.3934/jmd.2018015.
  - One query found no record for Coulon–Fournier-Facio, and the arXiv abstract page shows no journal reference.

**Reused from main (their bounds apply):** `sk-lit-novelty-2-2026-09-13.md`, `sk-novelty-prior-art-2026-09-13-part1.md` and `-part2.md`.

**NOT done:**
- MathSciNet and zbMATH;
- full reading of CFF, NPS or Popa 2006;
- Ol'shanskii's SQ-universality papers; Russian sources;
- Kionke–Schesler §11 beyond what sk-lit-novelty-2 read (pp. 38–41);
- the de Cornulier–Guyot–Pitsch isolation results (recalled only).

## 1. Grades

| # | Claim | Grade | Prior work | New within the bound |
|---|---|---|---|---|
| 1 | an infinite f.g. simple Kazhdan LEF (so sofic, hyperlinear) group | NOT FOUND | open-status record through Alekseev–Thom arXiv:2608.05362 §5 (Aug 2026), sk-novelty part1 §1 | the whole claim |
| 2 | f.g. LEF iff subgroup of a f.g. simple LEF group (no (T)) | PARTIALLY KNOWN | RF inputs: Kionke–Schesler Thm 1.2 | LEF inputs (the characterization) |
| 3 | the same with (T) | PARTIALLY KNOWN | simple Kazhdan hosts WITHOUT LEF: immediate from Coulon–Fournier-Facio Thm 1.5 | (T) and LEF together |
| 4 | an infinite simple Kazhdan marked limit of finite simple groups with expander Cayley graphs | NOT FOUND (reduces to #1) | expander mechanism: Kassabov 2007; mother groups EJZK 2017 | an infinite simple Kazhdan limit |
| 5 | one universal LEF host | PARTIALLY KNOWN (by composition) | no (T): Wilson Thm A + Kionke–Schesler; no LEF: Higman + CFF Thm 1.5 | (T) and LEF together; recursively presented LEF inputs |
| 6 | no distorted elements in GL_m(LC(X,F_q)⋊Z) | NOT FOUND (for these groups) | analogue for Aut(X): Cyr–Franks–Kra–Petite 2018 | the ring/matrix statement and its SL_3(Z), H_3(Z) corollary |
| 7 | a separable II_1 factor contains G_X for only countably many X | PARTIALLY KNOWN | mechanism: Ozawa 2004 Thm 2; no separable universal R^ω-embeddable factor: NPS 2007 | the witnesses are property (T) factors of simple groups |

### 1.1 Claim 1
- **Record** (sk-novelty part1 §1 read these at source):
  - Ozawa 2003: "It is unknown whether there exists a simple property (T) group Γ which is hyperlinear."
  - Pestov v8, Open question 9.1; Pestov–Kwiatkowska v4 p. 28; Cornulier 0906.3374.
  - Alekseev–Thom (5 Aug 2026) §5: its list of sofic non-RF Kazhdan groups names only Thom's group.
- **This lane:** two further searches for 2025–2026 claims found none. The 2504.10988 hit characterizes hyperlinearity through amenable near representations; it is not an example.
- **Known infinite simple Kazhdan groups, and why none is prior:**
  - Caprace–Rémy lattices are f.p., so any LEF one would be RF, which a simple infinite group is not; their soficity is unknown.
  - Gromov's monsters and CFF's simple quotients of hyperbolic Kazhdan groups: soficity unknown.

### 1.2 Claims 2 and 3: the risk R1 of sk-lit-novelty-2 resolves against (T) alone
- **Coulon–Fournier-Facio, arXiv:2312.11684, Theorem 1.5 (A, HTML introduction):** "Let Γ be a torsion-free, non-elementary hyperbolic group. Then, for every countable group L, there exists a characteristic subgroup N<Γ such that Γ/N is simple, 2-generated, contains L as a subgroup, and contains an element of order n∈ℕ if and only if L does."
  - Take Γ a torsion-free hyperbolic Kazhdan group, for instance a torsion-free cocompact lattice in Sp(n,1), n ≥ 2 (Selberg's lemma; (T) of Sp(n,1) is classical, recalled). Then Γ/N has (T) as a quotient of Γ.
  - So **every countable group is a subgroup of a 2-generated infinite simple Kazhdan group.** This is prior, though not printed with the word (T) in Theorem 1.5.
- **CFF Remark 4.5 (A):** "if we first replace H by a common quotient of H and an acylindrically hyperbolic group with Property (T)", giving simple characteristic quotients with (T), citing [Hul16, Corollary 1.6].
- **Hull, arXiv:1308.4345v2, p. 4 (V):**
  - "Corollary 1.6. Let G_1, G_2 ∈ 𝒜ℋ, with G_1 finitely generated, G_2 countable. Then there exists an infinite group Q and surjective homomorphisms α_i: G_i → Q for i = 1, 2. If in addition G_2 is finitely generated, then we can choose Q ∈ 𝒜ℋ."
  - "Corollary 1.7. Every countable G ∈ 𝒜ℋ has an infinite quotient with Property (T)."
  - These are quotient statements, not embeddings. The embedding form is CFF's Theorem 1.5.
- **Checked and not prior:**
  - Osin 2010 (math/0411039) introduction: Theorems 1.1 and 1.5 and Corollary 1.2 embed countable groups in 2-generated groups with few conjugacy classes, or verbally complete groups. No simplicity-with-(T) statement (A).
  - Chifan–Ioana–Osin–Sun (2304.07455): Out(G) ≅ Q for acylindrically hyperbolic Kazhdan G. Not an embedding into a simple group (A).
- **LEF inputs without (T):** no statement found.
  - Kionke–Schesler Thm 1.2 needs RF input (verbatim on main, sk-lit-novelty-2 §2).
  - One unexamined route: Nekrashevych's alternating full groups are simple for minimal actions and f.g. for expansive ones (arXiv:1511.08241, search snippet). No source found puts a given LEF group inside a LEF one.
- **Verdict:**
  - The (T) half alone is prior (CFF 2023, by a one-line application).
  - What the note adds is (T) and LEF in one host, and LEF input, which the characterization needs.
  - The rev3 credit paragraph omits CFF (gap G1 below).

### 1.3 Claim 4
A f.g. group is LEF iff it is a limit of finite groups in the space of marked groups (standard), so an infinite simple Kazhdan limit is claim 1.
- Finite simple models with expanders follow Kassabov, Invent. Math. 170 (2007), credited in rev3 l.75.
- Contrast (recalled, not opened): f.p. infinite simple groups are isolated in the space of marked groups (de Cornulier–Guyot–Pitsch), so Caprace–Rémy's lattices are never such limits.
- Mimura–Ozawa–Sako–Suzuki (1402.5105) study (T) for boundary groups of finite families; the abstract names no simple example (A).

### 1.4 Claim 5
- **Without (T):**
  - Wilson Thm A puts the countable direct sum of all f.p. RF groups and all f.g. linear groups into a 2-generator RF group H. Kionke–Schesler Thm 1.2 then gives an infinite f.g. simple LEF group containing H.
  - For recursively presented inputs, Higman's universal f.p. group plus Gorjuškin/Schupp gives a f.g. simple group containing every f.g. recursively presented group (no LEF).
- **Without LEF:** CFF Thm 1.5 applied to Higman's universal f.p. group gives one 2-generated simple Kazhdan group containing every f.g. recursively presented group, so every f.p. RF group and every f.g. linear group.
- **With both (T) and LEF** (rev3 Corollary 3; sk-universal-lef-host-b Theorem C for recursively presented LEF inputs): NOT FOUND.
- **Verdict:** each single property is prior by composition; their conjunction is the note's point (gap G2).

### 1.5 Claim 6
- **Cyr–Franks–Kra–Petite,** J. Mod. Dyn. 13 (2018) 147–161 (A abstract; Crossref): "the Baumslag-Solitar groups BS(1,n) and all other groups that contain exponentially distorted elements cannot embed into Aut(X) when h_top(X)=0. We further show that distortion in nilpotent groups gives a nontrivial obstruction to embedding such a group in any low complexity shift."
- **Callard–Salo,** Ergodic Theory Dynam. Systems 44 (2024) 1757–1817 (A, arXiv journal-ref): a polylogarithmically distorted element in a f.g. subgroup of Aut of the full shift. This is positive entropy, so consistent.
- **Verdict:** the automorphism-group analogue is prior; GL_m over the crossed product ring is a different group. NOT FOUND for the ring statement.
- The sk-sl3z-bandwidth proposal's credit to CFKP as nearest prior is right.

### 1.6 Claim 7
- **Mechanism:** Ozawa, PAMS 132 (2004), Thm 2, credited by sk-strong-7.
- **No separable universal R^ω-embeddable factor: PRIOR.**
  - NPS 2007 abstract (A): the factors M_α(Γ) = L_{μ_α}(ℤ²⋊Γ) "are mutually non-isomorphic, modulo countable sets, and cannot all be embedded into the same separable II₁ factor".
  - Their introduction (A): "The factors M_α(Γ) are easily seen to be 'approximately embeddable' into the hyperfinite II₁ factor R … i.e., M_α(Γ)⊂R^ω."
  - These factors have only relative property (T) for ℤ² ⊂ ℤ²⋊Γ, not (T).
  - Peterson (arXiv:2605.16669, A) states "there is no universal separable factor containing all separable factors that embed into R^𝒰" with reference [60] = Popa, "On a class of type II₁ factors with Betti numbers invariants". Popa's abstract does not say it, so that attribution is unverified here. sk-verify-10 owns the source check.
- **Continuum many R^ω-embeddable property (T) factors with countable isomorphism classes: NOT FOUND.**
  - Peterson's Theorem 1.5 family consists of free products L(T_α(Γ)∗T_α(Γ)), which are not (T) factors (A).
  - Ioana–Tucker-Drob's continuum of (T) groups (2512.04531): hyperlinearity not stated (A).
  - Chifan–Drimbe–Ioana (2205.07442) embeds every separable tracial algebra into a (T) factor, the other direction (A).
- **Verdict:** the factor-level "no universal" statement is prior. The note adds group factors of simple Kazhdan groups as R^ω-embeddable witnesses.

## 2. Overclaims and credit gaps, with verbatim fixes
**No false statement found in rev3.** Sentences checked:
- the abstract, l.29–41;
- introduction l.45–53, l.71–87, l.89–93;
- Brown's formulation, l.254–265;
- §2 credit, l.269–274; Corollary 3, l.348–361;
- §3, l.365–404; Questions, l.406–420.

### G1. Credit gap: simple Kazhdan hosts without LEF (rev3 l.269–274). Sent to main at once.
Before:
```latex
Every countable group embeds in a finitely generated simple
group~\cite{Gorjuskin,Schupp}, and Kionke and Schesler proved that every
finitely generated residually finite group embeds in a finitely generated
simple LEF group~\cite[Theorem~1.2]{KionkeSchesler}. The next corollary
adds property~\textup{(T)} and applies to every LEF group. Since LEF
passes to subgroups, it characterizes LEF groups.
```
After:
```latex
Every countable group embeds in a finitely generated simple
group~\cite{Gorjuskin,Schupp}, and even in a simple quotient of a
torsion-free hyperbolic Kazhdan group~\cite[Theorem~1.5]{CoulonFournierFacio}.
Kionke and Schesler proved that every finitely generated residually finite
group embeds in a finitely generated simple LEF
group~\cite[Theorem~1.2]{KionkeSchesler}. The next corollary gives
property~\textup{(T)} and LEF together, for every LEF group. Since LEF
passes to subgroups, it characterizes LEF groups.
```
- Cost: +2 text lines, +3 bibliography lines.
- Trade-off: the reader sees that (T) alone and LEF alone were available, and that the conjunction is the new point.
- Bibitem (journal status VERIFY-PENDING; no Crossref record found in one query):
```latex
\bibitem{CoulonFournierFacio}
R.~Coulon and F.~Fournier-Facio, \emph{Infinite simple characteristic
quotients}, preprint (2023). \arxiv{2312.11684}.
```
- Before printing, check against the PDF:
  - the Theorem 1.5 numbering in the latest arXiv version;
  - "torsion-free, non-elementary hyperbolic" as the hypothesis;
  - the existence of torsion-free hyperbolic Kazhdan groups (for example torsion-free cocompact lattices in Sp(n,1), n ≥ 2). If a citation is wanted, use the standard Kazhdan/Kostant plus Selberg references.

### G2. Credit clause for the universal host (rev3 Corollary 3 or rev4 item 71(d)); optional
After the proof's last sentence (l.360), add:
```latex
Without property~\textup{(T)}, Wilson's theorem and
\cite[Theorem~1.2]{KionkeSchesler} already give such a simple LEF group;
without LEF, Higman's universal finitely presented group and
\cite[Theorem~1.5]{CoulonFournierFacio} give such a simple Kazhdan group.
```
- Cost: +3 lines; a Higman bibitem is needed (Proc. Roy. Soc. A 262 (1961); not checked here).
- Trade-off: it states exactly what the corollary adds. Main may drop it for length, since G1 already names both sources.

### G3. Wording for rev4 P1 (sk-strong-7, decision item 83)
- Do NOT write "answers Ozawa's question". His printed remark asks whether his Γ_α embed in U(R^ω); G_X is a different family.
- Do NOT write "the first continuum of R^ω-embeddable property (T) factors". It is NOT FOUND, not verified absent.
- Safe form:
```latex
Nicoara, Popa and Sasyk showed that no separable $\mathrm{II}_1$ factor
contains all factors that embed in $\mathcal R^\omega$~\cite{NPS}. The
factors $L(G_X)$ give such a family of property~\textup{(T)} group
factors, by Ozawa's argument~\cite[Theorem~2]{OzawaUniversal}.
```
- Check NPS's journal data at source (search snippet only: J. Funct. Anal. 242 (2007), no. 1, 230–246).

### G4. Wording for the SL_3(Z) paragraph (item 78)
- Keep the scope "lies in no $G_X$", and credit CFKP as the analogue for automorphism groups of zero-entropy shifts.
- Do not write "first obstruction to embedding SL_3(Z)". The obstruction is for these groups only, and amenability already excludes SL_3(Z) from topological full groups.

### G5. Headline wording (claims 1 and 4)
- Rev3's phrasing ("answers the question … positively") is supported by the record.
- Keep "first" out of the note: "first simple Kazhdan host" is now false by CFF, and "first infinite simple Kazhdan LEF group" rests on a bounded search. This matches sk-lit-novelty-2 §3(d).

## 3. Status
- Literature only; no Cairn claims; not reviewed.
- G1 sent to main (~22:10). G2–G5 are for sk-editor-4 through main.
- Handed to other lanes (no messages sent):
  - sk-verify-10: the NPS source check and the Popa [60] attribution;
  - sk-answered-questions: printed questions answered.
