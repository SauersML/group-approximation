# sk-review-6, part 1: primary-source check of the Kirchberg, Ozawa, Pestov and Brown citations (2026-09-13)

Lane sk-verify-6 (literature and credit verifier).

**Subject:** main's `simple_kazhdan_sofic_group.tex` at e80dcf20ad (revision 2, md5 4ad49212…). Line numbers below refer to that blob.

**Method:**
- All sources were fetched on MSI into `/scratch.global/sauer354/sk/sk-verify-6/`.
- arXiv e-print TeX sources were grepped for theorem counters, section order and the quoted environments.
- Kirchberg's Springer PDF was downloaded and read locally as page images.
- The check was done from the sources, independently of the earlier lanes (sk-citations, sk-operator-algebras, sk-review-2, sk-panel-referee-2).

## Verdict summary

| # | Note location | Claim in the note | Source read | Verdict |
|---|---|---|---|---|
| 1 | l.173–175 | Kirchberg: a Kazhdan group with the factorization property is residually finite, [Theorem 1.1] | Math. Ann. 299 (1994), PDF p. 552 | PASS |
| 2 | l.340–344 | Kirchberg bibitem: title, volume, year, pages, DOI | PDF p. 551 header; DOI download | PASS |
| 3 | l.168 | L(G) embeds in R^ω, [Ozawa, Proposition 7.1] | arXiv:math/0306067v2 source, §7 | PASS (arXiv numbering) |
| 4 | l.44 | "Ozawa stated the hyperlinear form in 2003", [p. 527] | arXiv source, remark after Theorem 7.4; abs page | PASS on content and year; p. 527 unverified |
| 5 | l.176–177 | C*(G) lacks the local lifting property, [Ozawa, p. 527] | same remark | PASS on content; p. 527 unverified |
| 6 | l.164–166 | LEF ⇒ sofic ⇒ hyperlinear, [Pestov, Example 4.5 and Theorem 3.3] | arXiv:0804.3968v8 source | PASS |
| 7 | l.45 | Pestov's Open question 9.1 adds the sofic form | v8 source, §9 | PASS |
| 8 | l.41–43 | Brown 2001, [§11, Question 7] | arXiv:math/0111286v1 source; abs page | PASS |

No FAIL and no GAP.

## 1. Kirchberg

**Source:** Math. Ann. 299, 551–563 (1994).
- p. 551 header: "Math. Ann. 299, 551-563 (1994)". Title: "Discrete groups with Kazhdan's property T and factorization property are residually finite". Author: Eberhard Kirchberg.
- Springer's `content/pdf` URL for doi:10.1007/BF01459798 returned exactly this article (814,733 bytes), which confirms the DOI.

**Verbatim, p. 552:**
- "Theorem 1.1 A discrete group with property (F) and property T is residually finite."
- "Corollary 1.2 For a discrete group G with property T, the following properties are equivalent: (i) G has property (F). (ii) There exists a faithful unitary representation from G into the hyperfinite II₁-factor. (iii) There exists a faithful group homomorphism from G into a locally compact group H with nuclear universal group C*-algebra C*(H). (iv) G is residually finite. (v) There exists a faithful group homomorphism from G into an almost connected locally compact group."
- "The implications (iv)⇒(v)⇒(iii)⇒(i) and (iv)⇒(ii)⇒(i) are true in full generality."

**Note, l.173–175:** "Kirchberg proved that a Kazhdan group with the factorization property is residually finite~\cite[Theorem~1.1]{Kirchberg}."
- The statement is faithful. Kirchberg defines (F) for locally compact groups (p. 551) and states Theorem 1.1 for discrete groups; G_X is discrete. PASS.
- The bibitem at l.340–344 matches the title, volume, year and pages. PASS.

**For main:** if the optional clause "G_X has no faithful unitary representation into the hyperfinite factor R" is ever wanted, it is correct. The reason is (ii)⇒(i) in full generality plus (i)⇒(iv) for Kazhdan groups, while G_X is not residually finite.

## 2. Ozawa

**Source:**
- arXiv:math/0306067 v2 TeX (`qwep.tex`, last modified 10 May 2004).
- abs page: "Submitted on 3 Jun 2003 (v1)"; comments "30 pages. Any comments are welcome. Minor changes".

**Numbering:**
- `\newtheorem{thm}{Theorem}[section]`, with `prop`, `lem`, `cor`, `defn` sharing the counter.
- Sections in order: Introduction, Preliminary Background, WEP and LLP, Permanence Properties of the QWEP, Finite Representability in the Trace Class, Connes' Embedding Problem, Groups with the Factorization Property (§7), Further Topics and Open Problems.
- Numbered environments in §7: prop (7.1), defn (7.2), prop (7.3), thm (7.4).

**Verbatim:**
- Just before 7.1: "We say a group Γ is hyperlinear if it embeds into U(R^ω)."
- Proposition 7.1: "A group Γ is hyperlinear if and only if LΓ is *-isomorphic to a von Neumann subalgebra of R^ω."
- Theorem 7.4, last sentence: "In particular, a group Γ with the properties (F) and (T) is residually finite."
- Remark after its proof: "It is unknown whether there exists a simple property (T) group Γ which is hyperlinear. By the above theorem, the full C*-algebra C*Γ of such a group Γ cannot have the LLP."

**Verdicts:**
- l.168, `\cite[Proposition~7.1]{Ozawa}` for L(G) ⊂ R^ω: PASS.
- l.44, "Ozawa stated the hyperlinear form in 2003": PASS for the content and the year (v1, 3 Jun 2003).
- l.176–177, "$C^*(G)$ does not have the local lifting property~\cite[p.~527]{Ozawa}": PASS on content. G_X is simple, Kazhdan and hyperlinear, which is exactly Ozawa's "such a group".

**Unverified:**
- **Journal page 527:** World Scientific's PDF for doi:10.1142/S0129167X04002417 returned HTML from MSI (two URLs tried). Only a consistency check was possible: the remark sits at source line 2190 of 2656, about 82% through, and the article spans pp. 501–530, so p. ≈ 525–527 is plausible.
- **Journal numbering of Proposition 7.1:** not seen. v2 describes itself as "Minor changes", so the risk is low.

Both go to sk-lit-locators.

**Precision (no change needed):** Ozawa writes "simple property (T) group" without "infinite". The note's gloss "whether an infinite simple Kazhdan group can be hyperlinear" is fair, since finite groups are trivially hyperlinear.

## 3. Pestov

**Source:**
- arXiv:0804.3968 v8 TeX (`hypsof.tex`, last modified 4 Aug 2008).
- abs page: journal reference "The Bulletin of Symbolic Logic 14 (2008), pp. 449-480"; comments "This version incorporates minor corrections made in the Bulletin of Symbolic Logic galley proofs".

**Numbering:**
- `\newtheorem{theorem}{Theorem}[section]`, shared by corollary, lemma, proposition, definition, question ("Open question"), conjecture, remark, remarks and example.
- No starred environments. One commented-out `% \begin{theorem}` in §3 comes after l.277 and affects nothing below.

**Theorem 3.3.** §3 is "Definitions". Its numbered environments are definition (3.1, l.253), definition (3.2, l.260), theorem (3.3, l.277): "\begin{theorem}[Elek and Szabó \cite{ES}] Every sofic group is hyperlinear." PASS.

**Example 4.5.** §4 is "Examples". Its environments are example 4.1 (l.432), 4.2 (l.442), 4.3 (l.455), 4.4 (l.464) and 4.5 (l.483): "Every initially subamenable group is sofic." Immediately before it (l.478–481) come:
- Gromov's definition of initially subamenable groups;
- "every residually finite or, more generally, residually amenable group is initially subamenable";
- "So is every LEF group G in the sense of Vershik and Gordon [VG], defined by the property that one can embed every finite F ⊆ G into a suitable finite group so as to preserve the partial multiplication."

PASS. Example 4.5 is stated for initially subamenable groups, and LEF ⇒ initially subamenable is the sentence just before it, so the locator "[Example 4.5 and Theorem 3.3]" is a correct pointer.

**Open question 9.1.** §9 is "Some classes of groups to look at", and its first numbered environment is at l.843: "\begin{question}[Cf. Ozawa \cite{ozawa}] Let $G$ be an infinite simple group with Kazhdan's property $(T)$. Can it be hyperlinear (sofic)?" PASS for l.45. Pestov's own "Cf. Ozawa" supports the lineage at l.44–45.

**Bibitem (l.363–366):** BSL 14 (2008), 449–480 matches arXiv's journal reference. The DOI was not re-resolved here.

**Unverified:** the BSL printed numbering. The Project Euclid download returned HTML. v8 incorporates the galley corrections, so the risk is low; flag for sk-lit-locators.

## 4. Brown

**Source:**
- arXiv:math/0111286 v1 TeX (`AFDtraces.tex`, last modified 27 Nov 2001).
- abs page: "Submitted on 27 Nov 2001 (v1)"; v3 comments "minor revisions and (hopefully) improved exposition".

**Numbering:** `\section{Questions}` is the 11th `\section`, and item 7 of its enumerate (source l.3071) reads: "Can an infinite, simple, discrete group with Kazdan's property T be embed into the unitary group of an $R^{\omega}$-embeddable McDuff factor? (Compare with \cite{robertson} where it is shown that no such embedding exists into the unitary group of $L({\mathbb F}_n)\bar{\otimes} R$ or, more generally, $L(\Gamma)$ for any a-T-amenable …"

**Verdict:** l.41–43, "Brown asked this in 2001 as a question about embeddings into unitary groups of McDuff factors that embed in an ultrapower $\mathcal R^\omega$ … [§11, Question 7]": PASS in v1. Not re-checked in v3 by this lane (sk-citations reports v3 item 7 at p. 34). The bibitem gives the arXiv id without a version, and the year 2001 matches v1.

## 5. Open for other lanes
- **sk-lit-locators:** the journal page and numbering for Ozawa (IJM 15 (2004): p. 527, Proposition 7.1) and the BSL numbering for Pestov.
- **Checks outside this part:** the Kassabov, Matui, GM, GMpres, Stepanov, Thom, Vershik–Gordon, GPS, Alekseev–Thom and Morse–Hedlund entries.
- No Cairn node changed.
