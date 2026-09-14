# sk-rev5-locators: three rev5 locators checked at published sources

Lane sk-rev5-locators, 2026-09-14. Drafts checked: `$SK2/drafts/rev5b.tex` (sk-editor-7b, md5 32207a76…) and `$SK2/drafts/rev5a.tex` (sk-editor-7a). Sources were fetched on MSI through University of Minnesota institutional access and read as page images.

## 1. Bekka–de la Harpe–Valette, Theorem 1.3.1 and series: VERIFIED at the published source, no change

**Source.** Cambridge Core, chapter 1, "Definitions, first consequences, and basic examples", pp. 27–72 (PDF `9780511542749c1_p27-72_CBO.pdf`, doi 10.1017/CBO9780511542749.002). Page footer: "Downloaded from https://www.cambridge.org/core. University of Minnesota Libraries, on 14 Sep 2026".

**Evidence.**
- p. 36, §1.3 "Compact generation and other consequences": "The first spectacular application of Property (T) is the following result, due to Kazhdan."
- "**Theorem 1.3.1** *Let G be a locally compact group with Property (T). Then G is compactly generated. In particular, a discrete group Γ with Property (T) is finitely generated.*"
- p. 40, Example 1.3.7(iv), refers back to it as "Theorem 1.3.1", which confirms the printed numbering.
- Series, from the Cambridge Core book page metadata: "New Mathematical Monographs", `"SeriesNumber":"11"`. Crossref: Cambridge University Press, issued 2008-04-17, ISBN 9780521887205.

**Verdict.**
- rev5b l.203 `\cite[Theorem~1.3.1]{BHV}` and bibitem l.766–769 ("New Math. Monogr. \textbf{11}, Cambridge Univ. Press, Cambridge, 2008") are correct. NO CHANGE.
- rev5a has no BHV citation.

## 2. Arzhantseva 2014: VERIFIED at the published source; one bibitem fix

**Source.** Springer chapter PDF, doi:10.1007/978-3-319-05488-9_2, pp. 7–15, 9 pages.

**Evidence.**
- p. 7 footer: "J. González-Meneses et al. (eds.), *Extended Abstracts Fall 2012*, Trends in Mathematics 1, DOI 10.1007/978-3-319-05488-9_2, © Springer International Publishing Switzerland 2014".
- p. 11, §3 "New Idea: Approximate "Easy" Groups by "Complicated" Ones": "In particular, the following is unknown." Then the bullet: "Does there exist an infinite simple sofic group with Kazhdan's property (T)?"
- p. 12, Definition 9: G is asymptotically approximated if "for each n ∈ ℕ there exist a finite generating set S_n of G and a map π: B_{S_n}(n) → (F, dist)…". This matches the note's gloss "the generating set may change with the radius".
- p. 13, Theorem 11: "In addition, there exists an infinite simple asymptotically residually finite (hence, asymptotically sofic) group with Kazhdan's property (T)." This matches the note's sentence.
- Crossref container-title: ["Trends in Mathematics", "Extended Abstracts Fall 2012"], page "7-15".

**Fix.** The printed chapter shows "Trends in Mathematics 1". The sub-series name "Research Perspectives CRM Barcelona" appears nowhere on the chapter's pages, so the rev5 abbreviation is not supported by what could be read. Use the printed form.

OLD (rev5b l.760–764; rev5a l.713–717, identical):
```
\bibitem{Arzhantseva}
G.~Arzhantseva, \emph{Asymptotic approximations of finitely generated
groups}, in: Extended Abstracts Fall 2012, Trends Math. Res. Perspect. CRM
Barc. \textbf{1}, Springer, Cham (2014), 7--15.
\doi{10.1007/978-3-319-05488-9_2}.
```
NEW:
```
\bibitem{Arzhantseva}
G.~Arzhantseva, \emph{Asymptotic approximations of finitely generated
groups}, in: Extended Abstracts Fall 2012, Trends Math. \textbf{1},
Springer, Cham (2014), 7--15. \doi{10.1007/978-3-319-05488-9_2}.
```

**Optional locator, 0 lines.** `~\cite{Arzhantseva}` → `~\cite[\S3]{Arzhantseva}` (rev5b l.67; rev5a l.60).

## 3. Ozawa, "p. 527": journal PDF UNREACHABLE; switch to a section locator checked in the e-print

**Published source, attempted and blocked.** From MSI, the World Scientific landing page for doi:10.1142/S0129167X04002417 shows institutional access ("UNIVERSITY OF MINNESOTA TWIN CITIES", "full access"). Every PDF endpoint was tried: `doi/pdf`, `?download=true`, `doi/epdf`, `doi/reader`, plus a cookie jar, a referer and browser headers. Each returned HTML: HTTP 403 with a Cloudflare challenge ("challenge-platform", "captcha-ajax"), or `action/cookieAbsent`. No journal page could be read, so "p. 527" is NOT verified at the published source. Crossref confirms IJM 15 (2004), 501–530.

**e-print, arXiv:math/0306067v2, main.tex (2656 lines), read on MSI.**
- Sections: §1 Introduction (l.76), §2 Preliminary Background (l.247), §3 WEP and LLP (l.530), §4 Permanence Properties of the QWEP (l.1294), §5 Finite Representability in the Trace Class (l.1509), §6 Connes' Embedding Problem (l.1720), **§7 Groups with the Factorization Property (l.1934)**, §8 Further Topics and Open Problems (l.2206); bibliography from l.2305.
- Numbering: `\newtheorem{thm}{Theorem}[section]`, with prop, lem, cor and defn sharing that counter. The numbered environments in §7 are l.1947 prop (7.1), l.1977 defn (7.2), l.2019 prop (7.3) and l.2138 thm (7.4).
- l.2190–2192, the paragraph right after the proof of Theorem 7.4: "It is unknown whether there exists a simple property (T) group Γ which is hyperlinear. By the above theorem, the full C*-algebra C*Γ of such a group Γ cannot have the LLP."
- Proposition 7.1 (l.1947–1950): "A group Γ is hyperlinear if and only if LΓ is *-isomorphic to a von Neumann subalgebra of R^ω." This matches rev5's `\cite[Proposition~7.1]{Ozawa}` (rev5b l.367, rev5a l.333) in e-print numbering. Keep it.

**Position estimate, NOT verification.** The remark sits about 95% of the way through the text (l.76–2305), and the article's text fills about pp. 501–528. So p. 527 is consistent with where the remark falls, but unconfirmed.

**Recommendation, 0 lines.** Use the section locator, which is checked in the e-print and in the bibitem's arXiv version:
- OLD (rev5b l.56; rev5a l.56): `property~\cite[p.~527]{Ozawa}, and Pestov asked the sofic form as Open`
- NEW: `property~\cite[\S7]{Ozawa}, and Pestov asked the sofic form as Open`

If main prefers to keep "p. 527", it rests on the position estimate and on Thom's citation, and it remains unverified at the journal.

## Summary

| Locator | Published source read? | Verdict | Change |
|---|---|---|---|
| BHV Theorem 1.3.1; New Math. Monogr. 11; CUP 2008 | yes, Cambridge Core ch. 1, p. 36 | VERIFIED | none |
| Arzhantseva question; Theorem 11; series | yes, Springer chapter, pp. 7, 11–13 | VERIFIED (question p. 11, §3) | bibitem series → "Trends Math. \textbf{1}"; optional `\cite[\S3]` |
| Ozawa "p. 527" | no, Cloudflare 403 | UNVERIFIED at journal; remark verified in e-print §7 after Theorem 7.4 | `\cite[p.~527]{Ozawa}` → `\cite[\S7]{Ozawa}` |
| Ozawa Proposition 7.1 | e-print only | verified in e-print numbering | none |

Local copies: `$SK2/lanes/sk-rev5-locators/bhv_ch1.pdf` and `arzh.pdf`. MSI work directory: `/scratch.global/sauer354/sk/locators/`.
