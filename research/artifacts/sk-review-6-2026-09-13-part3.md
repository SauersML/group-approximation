# sk-review-6, part 3: sk-lit-background quotations and sk-lit-locators spot-checks (2026-09-13)

Lane sk-verify-6 (literature and credit verifier). Queue `sk/queue/sk-verify-6.txt`, entries 4 and 5. Coordinator priority: the Stepin credit and the GPS page fix, both going into revision 4.

**Method.** Sources fetched on MSI into `/scratch.global/sauer354/sk/sk-verify-6/`:
- arXiv e-print TeX of Thom 0810.2180, Caprace–Rémy math/0607664, Rădulescu math/0004172, Pestov 0804.3968v8, Ozawa math/0306067v2 and Lubotzky 1105.2389;
- the Vershik–Gordon Algebra i Analiz PDF from mathnet.ru, read locally as page images (pp. 71, 72, 97);
- Crossref records (api.crossref.org) and zbMATH records (api.zbmath.org).

Everything here was checked independently of the two lanes under review.

## Verdict summary

| # | Item | Verdict |
|---|---|---|
| 4 | sk-lit-background, part 2 (V1–V10) and proposal BG1–BG3 | PASS for BG1, BG2, BG3 and every quotation. One **GAP (false caution)**: the claim that Rădulescu's 2.5 is a Definition is wrong (§1.4). |
| 5 | sk-lit-locators table, rows 14, 18, 19 and F2 (GPS pages), plus the Stepin credit F4/P3 | PASS on all spot-checked rows. **Priority items: P3 (Stepin) PASS; P1 (GPS 51–111) PASS.** |

No FAIL.

## 1. sk-lit-background (entry 4)

### 1.1 Thom, arXiv:0810.2180 (`main.tex`, v1, 13 Oct 2008)
- **l.96, full sentence** (V1, PASS): "There are two sources of simple groups with Kazhdan's property (T). Such groups appear for example as lattices in certain Kac-Moody groups, see \cite{caprem}. Much earlier, it was also shown by Gromov (\cite{MR919829}) that every hyperbolic group surjects onto a Tarski monster, i.e.\ every proper subgroup of this quotient is finite cyclic; in particular: this quotient group is simple and is a Kazhdan group if the hyperbolic group was a Kazhdan group."
- **l.56** (V8, PASS): "In \cite{MR2072092}, N.\ Ozawa observed that there are no hyperlinear groups known which do not have E.\ Kirchberg's factorization property … In this note, we give examples of groups with this behaviour. As a consequence, the maximal group $C^*$-algebra of such a group can[not have the local lifting property]"
- **l.200** (V7, PASS): "Following ideas of M.\ Gromov, R.\ Grigorchuk (see \cite{MR764305}) has introduced the space of marked groups with $n$ generators."
- **l.341** (V3, second quote, PASS): "Sofic groups (with an equivalent definition in terms of Cayley graphs) were first studied by Gromov in \cite{gromov} and later by B.\ Weiss in \cite{MR1803462} who also coined the name. Later, G.\ Elek and E.\ Szab{\'o} continued a more systematic study … and proved that sofic groups are hyperlinear."
- **Another source for BG1's last clause:** the intro reads "…a finitely generated hyperlinear (in fact locally embeddable into finite groups (LEF), hence sofic) Kazhdan group which is not residually finite and hence does not have the factorization property." BG1's "not residually finite and so lacks the factorization property" is faithful.

### 1.2 Caprace–Rémy, arXiv:math/0607664 (`SimplSuperrigid.tex`; jref Invent. Math. 176 (2009) 169–221)
All three V2 quotes PASS:
- l.153–154: "As pointed out to us by Y.~Shalom, we obtain the first infinite {\it finitely presented}~discrete groups to be both simple and Kazhdan."
- l.158–161: the corollary, "… $\Lambda/Z(\Lambda)$ is finitely presented, simple and Kazhdan. Moreover there exist infinitely many isomorphism classes …".
- l.1827–1828: "The above simple groups seem to be the first examples of infinite finitely generated simple groups enjoying property (T)."

The lane's recommendation is right: print "first finitely presented", which is CR's own words credited to Shalom, never "first finitely generated". The l.1827 sentence conflicts with Thom's Gromov attribution.

### 1.3 Pestov, arXiv:0804.3968v8 (`hypsof.tex`)
V4, V5, V6 and V10 all PASS:
- l.385: "The origin of this conjecture is Connes' 1979 paper \cite{connes-injective}. The expression ``hyperlinear group'' belongs to Radulescu \cite{radulescu00}."
- l.1044–1046: `connes-injective` is "Classification of injective factors, Ann. of Math. **104** (1976), 73--115". So "1979" in the text is a slip, and BG3's "use 1976" is correct.
- l.799–802, verbatim as V5: "\begin{theorem}[Kirchberg \cite{kirchberg94}; Radulescu \cite{radulescu00}, Prop. 2.5; Ozawa \cite{ozawa}, Prop. 7.1] Let $G$ be a countable group. Then $VN(G)$ embeds into $R^\omega$ if and only if $G$ is hyperlinear."
- l.1240: "VG … St. Petersburg Math. J. **9** (1998), 49--67".
- l.1250–1253: "Weiss … Sankhyā Ser. A 62 (2000), no. 3, 350--359".

### 1.4 Rădulescu, arXiv:math/0004172 (`convexsets.tex`, latest version v3). GAP: the caution is false
The lane (part 2 V4 and proposal BG2 (e)) says: "In arXiv v3 of Rădulescu, 2.5 is a *Definition* (convexsets.tex l.290). … never write 'Proposition 2.5'." That inference comes from the label NAME `\label{definition2.5}` at l.290, not from the printed counter.

Counter check from the source:
- `\newtheorem{theorem}{Theorem}[section]`, with corollary, lemma, proposition, example, definition AND `\newtheorem{remark}[theorem]{Remark}` (l.39) sharing the counter.
- §1 (l.75) has no numbered environments.
- §2 (l.147) has these active, uncommented environments:
  - 2.1 definition (l.164, label `definition2.1`);
  - 2.2 remark (l.175);
  - 2.3 definition (l.186, label `definition2.2`);
  - 2.4 proposition (l.200, label `proposition2.3`);
  - **2.5 proposition (l.266, label `proposition2.4`)**;
  - 2.6 definition (l.289, label `definition2.5`);
  - 2.7 theorem (l.296).
- The labels are stale by one because the Remark at l.175 shares the counter.
- Printed **Proposition 2.5** (l.266–270): "Let $\Gamma$ be a discrete i.c.c.\ group that embeds faithfully into the unitary group of $R^{\omega}$. Then $\mathcal{L}(\Gamma)\subseteq R^{\omega}$."

That is exactly the statement Pestov credits as "Radulescu, Prop. 2.5". So Pestov's locator is **correct** for arXiv v3; the earlier versions and the Theta 2008 printed version were not seen.

**Consequences:**
- BG2's replacement text, citing without a locator, still PASSES and loses nothing.
- Retract the caution sentence in part 2 V4 and in proposal BG2 (e). `[Radulescu, Proposition~2.5]` would be correct for the arXiv version.
- Retract the "Prop. 2.5 number … FLAG" in sk-lit-credit-audit's table, for the same reason.

### 1.5 Which Kirchberg paper Ozawa credits (supports BG2)
Ozawa `qwep.tex` l.1942–1944: "It turns out \cite{kf}, \cite{radulescu2} that embeddability of $L\G$ into $R^\omega$ is equivalent to that of $\G$ into the unitary group $\U(R^\omega)$."
- l.2501–2504: `\bibitem[Ki3]{kf}` is "E. Kirchberg, *Discrete groups with Kazhdan's property T and factorization property are residually finite*", the Math. Ann. 299 (1994) paper already in the note.
- l.2580–2583: `radulescu2` is "The von Neumann algebra of the non-residually finite Baumslag group … embeds into $R^\omega$", which is math/0004172.

So two independent surveys, Ozawa and Pestov, credit the equivalence to Kirchberg 1994 and Rădulescu, and BG2's `\cite{Kirchberg,Radulescu}` matches both. PASS. I did not find the statement inside Kirchberg's paper (only p. 552 was read, in part 1).

### 1.6 Crossref records for BG1 and BG3 bibitems

| key | Crossref | bibitem | verdict |
|---|---|---|---|
| CapraceRemy | Caprace; Rémy, "Simplicity and superrigidity of twin building lattices", Invent. Math. 176(1), 169–221, online 2008-11-25 | Invent. Math. 176 (2009) 169–221, doi 10.1007/s00222-008-0162-6 | PASS (print year 2009, arXiv jref agrees) |
| GromovHyperbolic | Gromov, "Hyperbolic Groups", MSRI Publications, pp. 75–263, 1987 | Essays in group theory, MSRI Publ. 8, 1987, 75–263, doi 10.1007/978-1-4613-9586-7_3 | PASS (the volume number 8 is not in the record; it is standard) |
| Connes (BG3) | Connes, "Classification of Injective Factors …", Ann. of Math. 104(1), start page 73, 1976 | 104 (1976) 73–115, doi 10.2307/1971057 | PASS (end page 115 from Pestov's bibliography) |

### 1.7 BG1 wording
- "quotients of hyperbolic Kazhdan groups~\cite{GromovHyperbolic}": PASS as secondary, via Thom l.96. Gromov 1987 itself was not read; the lane correctly avoids "every" and "Tarski monster".
- "Kac--Moody lattices, which gave the first finitely presented examples": PASS (§1.2).
- "none was known to be hyperlinear~\cite{Ozawa,Pestov}": PASS (part 1, Ozawa remark after Thm 7.4; Pestov 9.1).
- "not residually finite and so lacks the factorization property~\cite{Thom}": PASS (§1.1).

## 2. sk-lit-locators (entry 5)

### 2.1 Row 14: Matui Lemma 3.4 and Theorem 4.9 (indirect). PASS
- The arXiv v3 counters (part 2 §3) give Lemma 3.4 = `DAFsimple`, Theorem 4.9 = `CMsimple`, Theorem 5.4 = `Dfg` and Theorem 5.7.
- An independent printed citation confirms the 4.9 locator: Juschenko–Monod, arXiv:1204.2132 `jm_15.tex` intro, "Matui proved that the commutator subgroup of $\full{T}$ is simple for any minimal Cantor system, see Theorem~4.9 in~\cite{Matui06} and the remark preceding it."
- GM's Mat. Sb. printed citations were not re-read (no arXiv source located).

### 2.2 Row 18: Ozawa p. 527 (indirect). PASS
Thom's arXiv source, l.120, carries the same page locators as the lane read in GGD p. 198: "This answers the question whether all hyperlinear groups could have the factorization property, see \cite[p.\ 524]{MR2072092}. As Ozawa points out (see \cite[p.\ 527]{MR2072092}), the maximal group $C^*$-algebra of $G$ cannot have the local lifting property". `MR2072092` is Ozawa's IJM paper. This agrees with part 1's position estimate (the remark is about 82% of the way through pp. 501–530). The IJM PDF itself was still not seen.

### 2.3 Row 19: Ozawa Proposition 7.1 (indirect). PASS
- Pestov v8 §8 counters before l.799: conjecture 8.1 (l.774), remark 8.2 (l.781), conjecture 8.3 (l.788), remark 8.4 (l.793), **theorem 8.5 (l.799)**. That matches the lane's BSL p. 471 "Theorem 8.5 (Kirchberg [53]; Radulescu [68] Prop. 2.5; Ozawa [64], Prop. 7.1)", so the journal and v8 numbering agree.
- Ozawa's own arXiv counter gives Proposition 7.1 (part 1 §2).
- The IJM numbering was not seen directly.

### 2.4 F2 / P1: GPS page range. PASS (use 51--111)
- Crossref for doi 10.1515/crll.1995.469.51 gives Crelle 1995, issue 469, pp. **51–112** (publisher deposit).
- zbMATH 0834.46053 gives "Topological orbit equivalence and $C^*$-crossed products", J. Reine Angew. Math. 469 (1995), pp. **51–111**.
- The lane's second printed source (GM Mat. Sb. [34], 51–111) was not re-read.
- Recommendation: 51--111, the reviewing-database value. The publisher deposit's 112 most likely counts a trailing page. Either is defensible and nothing hangs on it for the reader.

### 2.5 F4 / P3: the Stepin credit. PASS (priority item for rev4)
Vershik–Gordon, Algebra i Analiz 9 (1997), no. 1, PDF from mathnet.ru, read locally:
- **p. 71**, verbatim: "Замечательным образом класс ЛВК групп находится в общем положении с классом аменабельных групп, а класс конечно представимых ЛВК групп совпадает с классом конечно представимых финитно аппроксимируемых (ФА) групп [9, 10]." ("The class of finitely presented LEF groups coincides with the class of finitely presented residually finite groups [9, 10].")
- **p. 72**, verbatim: "В §2 … показано, что все локально финитно аппроксимируемые группы являются ЛВК и все конечно представимые ЛВК группы являются ФА." So VG also prove the fact in §2.
- **p. 72, §1 1°:** the LEF definition ("Группа G называется локально вложимой в класс конечных групп (ЛВК группой), если для любого конечного множества H ⊆ G существуют конечное множество K, H ⊆ K ⊆ G, и бинарная операция ⊙ …"), which agrees with the note's definition.
- **p. 97**, bibliography:
  - "[8] Стёпин А. М., *Аппроксимируемость групп и групповых действий*, Успехи мат. наук **38** (1983), № 6, 123–124."
  - "[9] Стёпин А. М., *Замечание об аппроксимируемости групп*, Вестн. Моск. ун-та. Сер. 1. Математика, Механика (1984), № 4, 85–87."
  - "[10] Stepin A. M., *Approximations of groups and group actions. Cayley topology*, Ergodic Theory of Z^d-Actions, London Math. Society Lecture Notes Series, vol. 228, Cambridge University Press, 1996, pp. 475–484."
- **zbMATH 0565.20014:** "Remark on approximability of groups", Moscow University Mathematics Bulletin 39 (1984), no. 4, pp. 90–93 (the English translation of [9]).
- **P3 text:** "A finitely presented LEF group is residually finite~\cite{Stepin,VershikGordon}" is supported by VG's own credit [9, 10] and by their §2.
- **Proposed bibitem:** it agrees with VG p. 97 (Russian original, 85–87) and zbMATH (translation, 39 (1984), no. 4, 90–93). PASS.
- **Optional addition:** VG credit [10] alongside [9]. A one-item citation of [9] is sufficient.
- **F8 (optional credit for the LEF notion to Stepin):** not re-read in GM. VG's intro supports a related attribution: Stepin's "free approximation", introduced in [2] and studied in [8, 9, 10], is equivalent to LEF for countable groups (p. 71). VG present the class itself as arising from model theory [1] and their own work. So "introduced by Stepin" is a stronger phrasing than VG's; prefer "studied by Stepin" if F8 is adopted.

### 2.6 Also consistent (not requested)
Lubotzky arXiv:1105.2389 bibliography l.2279–2281: "G.A. Margulis, *Explicit constructions of expanders*. (Russian) Problemy Peredac(i Informacii 9 (1973), no. 4, 7180. English translation: Problems of Information Transmission 9 (1973), no. 4, 325--332 (1975)." This is secondary. Note the title varies across sources (zbMATH "Explicit construction of a concentrator"; Lubotzky "Explicit constructions of expanders"); part 2 §2.5's recommendation stands.

## 3. For main
- **Rev4 priority items:** P3 (Stepin, with bibitem as proposed) PASS; P1 (GPS 51--111) PASS.
- **BG1, BG2, BG3:** safe as proposed.
- **Retract the Rădulescu "2.5 is a Definition" caution** wherever it was copied: part 2 V4, proposal BG2 (e), and the sk-lit-credit-audit table flag. In arXiv v3, printed 2.5 is the Proposition "i.c.c. Γ ⊂ U(R^ω) ⇒ L(Γ) ⊆ R^ω", as Pestov says.
- No Cairn node was changed by this part.
