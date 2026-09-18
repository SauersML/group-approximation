# Krstić–McCool, *Presenting GL_n(k⟨T⟩)*: access log and verbatim review (lane gq-lit-arxiv, 2026-09-17)

S. Krstić and J. McCool, *Presenting GL_n(k⟨T⟩)*, J. Pure Appl. Algebra 141 (1999), no. 2, 175–183,
DOI 10.1016/S0022-4049(98)00022-X. Zbl 0930.19001 (zbMATH Open document 1340433); MSC 19C20, 20F05.

## 1. Primary text: NOT read (every free channel refused, 2026-09-17)

- **Crossref** (api.crossref.org/works/10.1016/S0022-4049(98)00022-X): the record exists. License entries
  are the Elsevier user license (1999) and the **Elsevier open-archive user license, effective
  2013-07-17**. So the article is free to read on ScienceDirect in a normal browser. The text-mining
  links point to api.elsevier.com.
- **Semantic Scholar API**: `isOpenAccess: true`, `openAccessPdf.status: "BRONZE"`. The url is only
  https://doi.org/10.1016/s0022-4049(98)00022-x. **Unpaywall**: oa_status "bronze", publisher copy only,
  `url_for_pdf: null`.
- **ScienceDirect**: HTTP 403 for the article page, the /abs/ page, and the open-archive PDF link
  `.../pii/S002240499800022X/pdf?md5=ef1beb0eb76999b6a8dc318673ffec7d&pid=1-s2.0-S002240499800022X-main.pdf`.
  api.elsevier.com text/plain returns 400 without an API key.
- **Others**:
  - CORE (web search and API v3): 403.
  - IA Scholar: browser verification wall.
  - web.archive.org: not fetchable by this tool.
  - fatcat API: timeout.
  - No author or departmental copy found. S. Krstić is now in industry; J. McCool (Toronto) has no
    online list found.
  - zbmath.org web pages: 403. The zbMATH Open **API** works (§2).
- **How to get the primary**: open the DOI in an ordinary browser (open archive, no subscription), or
  use the MSI library proxy. Then copy Theorem 3 and Corollary 2 into §3 below.

## 2. zbMATH Open review Zbl 0930.19001 (reviewer W. van der Kallen, Utrecht), verbatim

Fetched from https://api.zbmath.org/v1/document/1340433 on 2026-09-17. Reproduced character for character,
with zbMATH's TeX markup:

> It was proved by \textit{H. Behr} that \(SL_3(\mathbb{F}_q[t])\) is not finitely presentable [In: Homological
> group theory, Proc. Symp., Durham 1977, Lond. Math. Soc. Lect. Note Ser. 36, 213-224 (1979; Zbl
> 0434.20025)]. The authors use the notion of an essentially infinite set of relations of a group \(G\)
> on a set of generators \(S\) to derive from his proof that in fact the following holds. Let \(R\) be
> a ring such that there is an epimorphism from \(R\) to \(k[t]\), for some field \(k\). Then any subgroup
> of \(GL_3(R)\) which contains \(E_3(R)\) is not finitely presentable. And similarly the Steinberg group
> \(St_3(R)\) is not finitely presentable. Next they prove an analogue for noncommutative rings of a
> result of \textit{U. Rehmann} and \textit{C. Soulé} [``Finitely presented groups of matrices'', in:
> Algebr. K-Theory, Proc. Conf. Evanston 1976, Lect. Notes Math. 551, 164-169 (1976; Zbl 0445.20025)]:
> If \(n\geq 4\) and \(R\) is a finitely presentable ring, then \(St_n(R)\) is finitely presentable. They
> apply all this to polynomial rings in noncommutating variables over a field. Finally they show finite
> presentability of \(GL_n(\mathbb Z[G])\) for a poly-\(\mathbb Z\)-group when \(n\) is in a stable range.

The review ("noncommutative rings", "finitely presentable ring") confirms:
- the hypotheses: a finitely presentable ring, possibly noncommutative, with no stable-rank or Noetherian
  condition;
- the rank bound n ≥ 4;
- the St_3 obstruction, for R mapping onto k[t].

It does **not** number the theorem. The number **Theorem 3** comes from two independent secondary sources
already quoted in `gq-steinberg-q-krstic-mccool-source.md`: Ershov–Jaikin-Zapirain arXiv:0809.4095v2,
"[Theorem 3]{KrM}", and Khanh arXiv:2609.08428v1, "[10, Theorem 3]".

## 3. Status for consumers

- **Theorem content**: three independent secondary witnesses (van der Kallen's review, Ershov–Jaikin-Zapirain,
  Khanh) agree: St_n(R) is finitely presented for every finitely presented (associative, unital) ring R and
  every n ≥ 4.
  - Unitality is implicit in the Steinberg group of a ring. It is stated explicitly only by Khanh
    ("associative unital ℤ-algebra").
- **Theorem number and exact wording**: secondary only, and unverified against the primary.
- `steinberg-finite-presentation-and-kazhdan-theorem` may cite the review as a third witness. Its
  citation route should keep saying the primary text was not read.
