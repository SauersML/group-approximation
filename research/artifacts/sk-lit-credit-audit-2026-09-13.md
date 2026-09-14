# sk-lit-credit-audit: sentence-by-sentence citation audit of the note (2026-09-13)

Lane sk-lit-credit-audit, wave 8 (ROSTER-F). The user's order: "all credit and background lit properly attributed and mentioned".

- **Subject:** main's `simple_kazhdan_sofic_group.tex` at tip bf2b24fa92, revision 2 (landed e80dcf20ad), md5 4ad49212…, 386 lines. Line numbers below refer to it.
- **Scope:** citations and credit for statements the note uses. It does not cover novelty (sk-lit-novelty-2), journal locators of existing bibitems (sk-lit-locators), or the background paragraph (sk-lit-background).
- **The proposal** with verbatim before/after and bibitems is `research/artifacts/sk-lit-credit-audit-proposal-2026-09-13.md`.

## 0. Verdict
- Every citation already in rev2 credits the right source for its sentence.
- Seven places use a notion or implication whose origin is not credited. Each is fixable with a citation, at +3 to +5 text lines.
  - The notions: Kazhdan's property (T); the terms sofic and hyperlinear; the space of marked groups; McDuff factors.
  - The implications: (T) ⇒ expanders; sofic ⇒ hyperlinear; ICC ⇒ II_1 factor; rotation codings of Sturmian subshifts.
- No citation in rev2 is wrong.

## 1. Sources verified by this lane
Crossref records were read today through api.crossref.org; zbMATH records through api.zbmath.org. Raw outputs: `sk/lanes/sk-lit-credit-audit/crossref-1.txt`, `crossref-2.txt`, `zbmath.txt`, `zbmath-margulis.txt`.

| key | data verified | how |
|---|---|---|
| Kazhdan | D. A. Kazhdan, Funct. Anal. Appl. 1 (1967), no. 1, 63–65, doi:10.1007/BF01075866 | Crossref. Crossref's title field reads "close subgroups", a metadata typo for "closed subgroups". |
| Gromov | M. Gromov, Endomorphisms of symbolic algebraic varieties, JEMS 1 (1999), no. 2, 109–197, doi:10.1007/PL00011162 | Crossref |
| Weiss | B. Weiss, Sofic groups and dynamical systems, Sankhyā Ser. A 62 (2000), no. 3, 350–359 | zbMATH 1148.37302 (no DOI) |
| Radulescu | F. Rădulescu, The von Neumann algebra of the non-residually finite Baumslag group ⟨a,b∣ab³a⁻¹=b²⟩ embeds into R^ω, pp. 173–185 (2008) | zbMATH 1199.46137, which gives pages and year only. The volume "Hot topics in operator theory", Theta Ser. Adv. Math. 9, is recalled and not seen: FLAG for sk-lit-locators. arXiv:math/0004172. |
| ElekSzabo | G. Elek, E. Szabó, Math. Ann. 332 (2005), no. 2, 421–441, doi:10.1007/s00208-005-0640-8 | Crossref. Quotes in `pestov91-literature-background-2026-09-13-part2.md` §12 (publisher PDF): p. 423 "We shall prove that countable sofic groups are hyperlinear (Theorem 2)." |
| Grigorchuk | R. I. Grigorchuk, Degrees of growth of finitely generated groups, and the theory of invariant means, Math. USSR-Izv. 25 (1985), no. 2, 259–300, doi:10.1070/IM1985v025n02ABEH001281 | Crossref (English translation). The Russian original (Izv. 48 (1984)) is not checked. |
| Champetier | C. Champetier, L'espace des groupes de type fini, Topology 39 (2000), no. 4, 657–680, doi:10.1016/S0040-9383(98)00063-9 | Crossref |
| Margulis | G. A. Margulis, Explicit construction of a concentrator (Russian), Problemy Peredachi Informatsii 9 (1973), no. 4, 71–80 | zbMATH 0312.22011. The English translation (Problems Inform. Transmission 9, 325–332) is recalled and not seen, so the bibitem omits it. |
| McDuff | D. McDuff, Central sequences and the hyperfinite factor, Proc. London Math. Soc. (3) 21 (1970), no. 3, 443–461, doi:10.1112/plms/s3-21.3.443 | Crossref |
| MurrayvonNeumann | F. J. Murray, J. von Neumann, On rings of operators. IV, Ann. of Math. 44 (1943), no. 4, 716–?, doi:10.2307/1969107 | Crossref gives the start page only. The end page 808 is recalled: FLAG. |
| Hedlund | G. A. Hedlund, Sturmian minimal sets, Amer. J. Math. 66 (1944), no. 4, 605–?, doi:10.2307/2371769 | Crossref gives the start page only. The end page 620 is recalled: FLAG. |
| Lothaire | M. Lothaire, Algebraic Combinatorics on Words, Cambridge Univ. Press (2002), doi:10.1017/CBO9781107326019; Chapter 2 "Sturmian Words", pp. 45–110, doi:10.1017/cbo9781107326019.003 | Crossref (book and chapter). The series number Encyclopedia Math. Appl. 90 is recalled: FLAG. |
| Stepin | A. M. Stepin, Approximability of groups and group actions, Russian Math. Surveys 38 (1983), no. 6, 131–132, doi:10.1070/rm1983v038n06abeh003464 | Crossref. Checked only for §3; not proposed. |
| Lubotzky, BdlHV, Wilson GTM 251, Kirchberg 1993, Coven–Hedlund 1973, Morse–Hedlund 1938 | DOIs 10.1007/978-3-0346-0332-4; 10.1017/CBO9780511542749; 10.1007/978-1-84800-988-2; 10.1007/BF01232444; 10.1007/BF01762232; 10.2307/2371264 | Crossref. Checked, but none is proposed (§3). |
| rev3 inputs: Ore, Wilson 1980, Kionke–Schesler, Archbold–Spielberg, Milnor | Proc. AMS 2(2) (1951) 307–314, doi:10.1090/S0002-9939-1951-0040298-4; Math. Z. 174(2) (1980) 149–157, doi:10.1007/BF01293535; J. Comb. Algebra (2024), doi:10.4171/jca/103; Proc. Edinburgh Math. Soc. 37(1) (1994) 119–124, doi:10.1017/S0013091500018733; Introduction to Algebraic K-Theory, Ann. of Math. Stud. 72, Princeton (1972), doi:10.1515/9781400881796 | Crossref. The Kionke–Schesler volume and pages are missing from Crossref: FLAG. |

**Attributions checked against Pestov's survey** (arXiv:0804.3968v8, e-print source `hypsof.tex`, fetched on MSI today):
- l.378: "Gromov's article [gromov99] where the concept of a sofic group was first introduced (without a name of its own) … The current expression "sofic group" was coined by Benjy Weiss [weiss]."
- l.385: "The expression "hyperlinear group" belongs to Radulescu [radulescu00]."
- l.799: "\begin{theorem}[Kirchberg \cite{kirchberg94}; Radulescu \cite{radulescu00}, Prop. 2.5; Ozawa \cite{ozawa}, Prop. 7.1]", the theorem giving the equivalence of hyperlinearity with L(G) ⊂ R^ω.

## 2. Sentence-by-sentence table
Verdicts:
- OK: cited correctly.
- ADD: credit missing, citation proposed.
- OPT: optional credit.
- NN: no citation needed (classical, or proved in the note).

| l. | sentence or claim | verdict | action |
|---|---|---|---|
| 27–37 | abstract | NN | Abstracts carry no citations. |
| 40–43 | Brown's question, McDuff factors in R^ω | OK | [Brown §11 Q7]. The notion "McDuff factor" is credited at l.172 (P6). |
| 44–45 | Ozawa 2003, Pestov 9.1 | OK | |
| 44–46 | the terms "hyperlinear" and "sofic" are used without origin | ADD | P2: Rădulescu (hyperlinear); Gromov, named by Weiss (sofic). |
| 55–56, 64–65 | "Kazhdan's property (T)" | ADD | P1: Kazhdan 1967. |
| 56–58 | "limit, in the space of marked groups … expanders" | covered at l.162–164 | P4, P5 |
| 64–68 | EJZ; GM Thm 2.6; Kassabov | OK | |
| 69–72 | Stepanov Thm 4.4 | OK | Read from the page images by sk-panel-referee-1. |
| 75–77 | Matui Lemma 3.4, Thm 4.9 | OK | |
| 77–79 | Thom | OK | |
| 99–108 | elementary matrices, Steinberg relations (1) | NN | Standard identities, displayed. |
| 110–113 | EJZ Thm 1.1 | OK | |
| 117–119 | LEF [VershikGordon] | OK | |
| 121–123 | minimality ⇒ every word occurs in x and recurs | NN | Standard (uniform recurrence), and it follows from minimality in one line. |
| 130–132 | "a subshift with boundedly many words of each length is finite" | NN | Immediate: C+1 distinct points are separated by one window length. Morse–Hedlund's p(n) ≤ n theorem is not needed. |
| 147–161 | free algebra surjections; EL_3(M_N(F_2)) = SL_{3N}(F_2); transvections | NN | Proved or classical. |
| 162–163 | "space of marked groups" | ADD | P4: Grigorchuk 1984/85; Champetier 2000. |
| 163–164 | "(T) ⇒ Cayley graphs of finite quotients form expanders" | ADD | P5: Margulis 1973 is the origin of the implication; Kassabov (already cited) for this family. |
| 164–166 | "LEF groups are sofic, and sofic groups are hyperlinear" [Pestov Ex. 4.5, Thm 3.3] | ADD primary | P3: Elek–Szabó Thm 2 for sofic ⇒ hyperlinear. Keep [Pestov, Example 4.5] for LEF ⇒ sofic (Pestov v8 l.481–484). |
| 168 | L(G) ⊂ R^ω [Ozawa Prop 7.1] | OK / OPT | Pestov credits the equivalence to Kirchberg 1994, Rădulescu Prop. 2.5 and Ozawa Prop. 7.1. Adding Rădulescu is optional and costs nothing once P2 adds the bibitem. The Prop. 2.5 number is taken from Pestov, not seen in Rădulescu: FLAG. |
| 169–171 | ICC ⇒ L(G) is a II_1 factor | OPT | P6: Murray–von Neumann IV. |
| 171–172 | "McDuff factor" | ADD | P6: McDuff 1970 (the notion). |
| 173–177 | Kirchberg Thm 1.1; Ozawa p. 527 (LLP) | OK | The Kirchberg 1993 (Invent.) definitions of the factorization property and the LLP are not needed; Kirchberg 1994 and Ozawa suffice. |
| 180–237 | simplicity proof; "GL_d(F_2) = PSL_d(F_2) … simple as d ≥ 3"; "transvections generate GL_d(F_2)" | NN | Classical (Jordan, Dickson). A textbook citation would only add length. |
| 247–249 | GMpres Thm 1.1(3) | OK | |
| 252–260 | word problem ≡ L(X) | NN | Proved in the note. |
| 261–268 | Sturmian subshift as the closure of rotation codings; words read off arcs | ADD | P7: Hedlund 1944 (Sturmian minimal sets as codings of rotations), Lothaire Ch. 2 as the textbook account. MorseHedlund 1940 alone names Sturmian trajectories but does not give the codings as stated. |
| 269–276 | counting formula; continued-fraction degrees; WP degree an isomorphism invariant | NN | Proved in the note, or standard. |
| 281–282 | f.p. LEF ⇒ RF [VershikGordon] | OK | |
| 285–287 | Alekseev–Thom Open problem 6.1 | OK | Quote verified by sk-open-5 and sk-questions-ggt. |
| 289–291 | flip conjugacy ⇒ isomorphism; strong orbit equivalence [GPS] | OK | |
| 293–297 | origin paragraph | OK | Matches the user's wording order ("no OpenAI or Astra"). |

## 3. Checked and not proposed
- **Stepin 1983** (LEF ⟺ marked limit of finite groups): the note proves LEF directly from the word-triviality comparison, so no import is used.
- **Lubotzky 1994 and BdlHV 2008** as textbook sources for (T) ⇒ expanders: I could not verify their theorem locators today, so Margulis's primary paper is proposed instead.
- **Wilson, The Finite Simple Groups** for simplicity of PSL_d(F_2): classical; the citation would add length and give the reader nothing.
- **Coven–Hedlund 1973** and **Morse–Hedlund 1938**: the note never uses the complexity theorem.
- **Kirchberg 1993**: the definitions of the factorization property and the LLP are standard, and the note cites the theorems it uses.

## 4. For revision 3 (§2 "LEF groups", universal host)
Verified bibitem data ready for sk-editor-3:
- **Ore 1951:** Γ ⊆ [Δ,Δ] (even permutations are commutators).
- **Wilson 1980, Thm A:** countable RF groups embed in 2-generator RF groups.
- **Kionke–Schesler 2024:** the version without (T). Its Crossref record lacks volume and pages: FLAG for sk-lit-locators.
- **Archbold–Spielberg 1994:** the term "topologically free", if §2 uses it.
- **Milnor 1972:** Whitehead's lemma diag(a,a⁻¹) ∈ E_2. The locator (§3, Lemma 3.1) is recalled and not seen: FLAG.

## 5. Flags for sk-lit-locators
- Rădulescu volume title/series and the Prop. 2.5 number;
- Murray–von Neumann end page;
- Hedlund 1944 end page;
- the Lothaire series number;
- the Margulis English translation;
- the Kionke–Schesler volume/pages;
- the Milnor locator.
