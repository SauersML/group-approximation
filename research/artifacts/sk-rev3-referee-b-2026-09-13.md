# sk-rev3-referee-b: referee report on revision 3 (credit, exposition, claims proved)

Lane sk-rev3-referee-b (ROSTER-G), 2026-09-13, second landing after the 21:20 resume. Referee (b) covers credit, exposition, and whether every claim in the abstract and theorem is proved in the text. Referee (a) owns correctness in depth.

## Subject
- **Refereed:** main's `simple_kazhdan_sofic_group.tex` as landed at 9047d0d3c9 (tip a1f1820bd9), md5 274f19367f7f706b05c017af721c3884, 618 lines. **Line numbers below refer to this blob.**
- **Predecessor:** the first landing (2e9f7b8b29) refereed the draft `sk/drafts/rev3.tex` (md5 2a0264d7…).
  - The landed text differs from that draft only in typesetting: `\arxiv` macro, keywords and pdfkeywords, MSC 22D10→22D55, `\qed`, `\section*{Origin and authorship}`, bibitem formatting, the Stepanov journal name.
  - So every finding carries over; body line numbers shift by +2.
- **My compile of the landed blob:** MSI texlive/2025, pdflatex 3 passes: 0 errors, 0 overfull, 0 undefined, 1 underfull, 7 pages.
- **Mechanical checks** (draft, unchanged by the diff): every `\cite` key has a bibitem and every bibitem is cited (35 keys); `thm:main`, `cor:lef` and `eq:elementary` resolve; no Codex, OpenAI or Astra. MSC 22D55 (property (T) and generalizations) is the right secondary class.
- **Read for context:** the rev3 changelog; sk-panel-referee-4/5/6 part1; the sk-lit-credit-audit proposal; sk-lit-novelty-2; sk-lit-background part1.

## 0. Verdict
- **No ERROR in scope.** Every claim of the abstract and of Theorem 1 has a proof or a correct citation in the text (§1).
- **Two credit GAPs, each a one-line fix for rev4:**
  - B1: the introduction asserts "the ring is simple" (l.78) with no proof and no citation. Rev1 removed the ring-simplicity paragraph and its citations; the direct proof no longer needs it, but the Stepanov sentence does.
  - B2: Mal'cev's theorem is used by name (l.354) with no citation.
- **UNCLEAR, short fixes:**
  - U1: quantifiers in the marked-limit step (l.173–180);
  - U2: §2's "word for word" substitution list omits the index set and d (l.307–312);
  - U3: "as for the Fibonacci subshift" (l.367) names an object that is never defined;
  - U4: letter clashes in §2 (R, G, Z, ψ, ℓ, P, ω);
  - U5: the countability of f.g. linear groups has no reason given (l.355);
  - U6: "the lamplighter action of a group Δ" (l.89).
- **Credit precision:**
  - C1, Caprace–Rémy: VERIFIED OK (§4).
  - C2, Ozawa's journal p. 527: unseen, low risk.
  - C3, Kionke–Schesler numbering: arXiv v1 verified.
  - C4–C6: optional background.
- **Doctrine:** D1 "hence" (l.208); D2 "This is Brown's formulation." (l.261); D3 "The next corollary adds" (l.272).
- **For rev4:** B1, B2, U1–U3, U6 and D1–D3, about +5 text lines and +7 bibliography lines. U4 strongly recommended.

## 1. Claims of the abstract and of Theorem 1, and where they are proved

| claim | location | verdict |
|---|---|---|
| G_X infinite | l.127–128 | proved |
| finitely generated | l.111–124 | proved |
| property (T) | l.124–127 | cited (EJZ Thm 1.1) |
| simple | l.188–252 | proved |
| marked limit of finite simple SL_{3N}(F_2) | l.162–180 | proved; U1 quantifiers |
| expanders w.r.t. images of a fixed generating set | l.180–185 | proved: (T) of EL_3(F) with Margulis/Kassabov, transfer through e_ij(1)=∏_a e_ij(τ_a) in both quotients; N_ℓ→∞ at l.144–147 |
| LEF | l.180 | proved (marked limit of finite groups) |
| sofic, hyperlinear | l.185–186 | cited (Pestov Ex. 4.5; Elek–Szabó Thm 2) |
| same for EL_n, n≥3, with SL_{nN} | l.97–98 | substitution stated; each n-dependent step checked below |
| answers Brown, Ozawa, Pestov | l.45–53, l.254–265 | proved; Brown's printed form through L(G)⊗̄𝓡 |
| LEF iff subgroup of an infinite f.g. simple Kazhdan LEF group | §2, l.276–345 | proved; U2, U4 |
| one such group contains every f.g. linear group | l.347–360 | proved; B2, U5 |
| every Turing degree is the word-problem degree of some G_X | §3, l.364–399 | proved |
| solvable WP iff L(X) recursive, "as for the Fibonacci subshift" | l.366–367 | iff proved; example needs U3 |
| G_X not finitely presented (Questions) | l.407–409 | cited (Vershik–Gordon) |

**n-dependent steps for EL_n:** each survives the substitution.
- EJZ holds for n≥3.
- Identities (1) need three distinct indices.
- EL_n(M_N(F_2)) = SL_{nN}(F_2).
- The criterion for commuting with e_ij(r) holds for every n.
- d = n(2w+1).
- The in-block transvection uses p′≠p, and the level ideal uses l∉{p,q}.

## 2. Findings with verbatim fixes

### B1 (GAP, credit): "the ring is simple" has no source (l.76–79)
Rev3 keeps main's decision 44 that simplicity also follows from Stepanov's Theorem 4.4. For a simple ring that theorem applies at level I=0, so the sentence needs R simple. The note no longer proves it: rev1 deleted the ring-simplicity paragraph together with the Clark–Edie-Michell, Steinberg and BCFS citations.

Before (l.76–79):
```latex
construction~\cite{Kassabov}. Simplicity also follows from Stepanov's
theorem on the normal structure of $\GL_n$~\cite[Theorem~4.4]{Stepanov},
since the ring is simple and any two of its elements $p,q$ satisfy
$pr+qs=0$ with $(r,s)\ne0$, by a dimension count on one cylinder. Our
```
After:
```latex
construction~\cite{Kassabov}. Simplicity also follows from Stepanov's
theorem on the normal structure of $\GL_n$~\cite[Theorem~4.4]{Stepanov},
since the ring is simple~\cite[Corollary~4.6]{ClarkEdie} and any two of
its elements $p,q$ satisfy $pr+qs=0$ with $(r,s)\ne0$, by a dimension
count on one cylinder. Our
```
Bibitem (Crossref-verified, §4):
```latex
\bibitem{ClarkEdie}
L.~O. Clark and C.~Edie-Michell, \emph{Uniqueness theorems for Steinberg
algebras}, Algebr. Represent. Theory \textbf{18} (2015), 907--916.
\doi{10.1007/s10468-015-9522-2}.
```
- Cost: +1 text line, +4 bibliography lines.
- Trade-off: the alternative proof now has a source for its one outside fact.
- Locator: Cor 4.6 (simplicity over any field for minimal effective Hausdorff ample groupoids) is checked in arXiv v1 by sk-citations (6b259b4463); the journal numbering is unseen.

### B2 (GAP, credit): Mal'cev uncited (l.353–356)
Before:
```latex
Finitely generated linear groups are residually finite by Malcev's
theorem, and up to isomorphism there are countably many groups of either
kind. So their direct sum is a countable residually finite group. Wilson
```
After:
```latex
Finitely generated linear groups are residually finite~\cite{Malcev}. Up
to isomorphism there are countably many groups of either kind, since a
finitely generated linear group lies in $\GL_n$ over a finitely generated
field. So their direct sum is a countable residually finite group. Wilson
```
Bibitem (zbMATH-confirmed title, journal, volume, year; §4):
```latex
\bibitem{Malcev}
A.~I. Mal'cev, \emph{On isomorphic matrix representations of infinite
groups}, Mat. Sb. (N.S.) \textbf{8(50)} (1940), 405--422.
```
- Cost: +1 text line (it also fixes U5), +3 bibliography lines.
- Countability check: a f.g. linear group lies in GL_n(K) with K generated by the entries of its generators; there are countably many f.g. fields up to isomorphism, and countably many f.g. subgroups of GL_n(K) for countable K.

### U1 (UNCLEAR): marked-limit quantifiers (l.173–180)
Marked convergence needs: for every λ, all words of length ≤ λ agree for all large ℓ. The text states it one word at a time. sk-panel-referee-6 §2.2 flagged this in rev2.

Before:
```latex
of those between blocks. A word of length $\lambda$ in the $e_{ij}(\tau)$
has entries of degree at most $\lambda$ in $F$, and
$\varphi_\ell\circ\pi=\rho_\ell$ on these entries for large $\ell$.
Applied to the entries of the word minus $I_3$, the previous paragraph
shows that for large $\ell$ the word is trivial in $G$ if and only if it
is trivial in $\SL_{3N_\ell}(\F_2)$. So these finite simple groups
```
After:
```latex
of those between blocks. A word of length at most $\lambda$ in the
$e_{ij}(\tau)$ has entries of degree at most $\lambda$ in $F$, and
$\varphi_\ell\circ\pi=\rho_\ell$ on the finitely many such entries once
$\ell$ is large. Applied to the entries of a word minus $I_3$, the
previous paragraph shows that for every $\lambda$ and all large $\ell$,
each word of length at most $\lambda$ is trivial in $G$ if and only if
it is trivial in $\SL_{3N_\ell}(\F_2)$. So these finite simple groups
```
+1 line.

### U2 (UNCLEAR): the §2 substitution list (l.307–312)
The list replaces u^t, T^tV, sums of exponents and |t|, but not the index range of ε_ab or the value of d.
- Over L the indices a,b run over the ball B_w, ε_ab = e_{aV}u_{ab^{-1}}, and d = 3|B_w|.
- I re-derived ε_abε_{a′b′} = δ_{ba′}ε_{ab′}, using V∩ξV = ∅ for ξ∈B_{2w}∖{e}.
- I re-derived fu_a e_V f′u_b ∈ {0, ε_{a,b^{-1}}}.
- With this sentence the "word for word" claim is complete.

Before (l.307–312):
```latex
property~\textup{(T)}~\cite[Theorem~1.1]{EJZ}, and it is infinite. Points
with trivial stabilizer in a given ball are dense, so every nonempty
clopen set contains a small one, in the sense of Section~1 with $u_\ell$
for $u^t$, $\ell V$ for $T^tV$, products in $L$ for sums of exponents,
and word length for $|t|$. With these replacements the proof of
simplicity in Section~1 applies word for word, so $G$ is simple.
```
After (includes the §2 renames of U4):
```latex
property~\textup{(T)}~\cite[Theorem~1.1]{EJZ}, and it is infinite. As the
action is topologically free, points with trivial stabilizer in a given
ball are dense, so every nonempty clopen set contains a small one, in the
sense of Section~1 with $u_\xi$ for $u^t$, $\xi V$ for $T^tV$, products in
$L$ for sums of exponents, and word length for $|t|$. The indices of
$\epsilon_{ab}=e_{aV}u_{ab^{-1}}$ then run over the ball of radius $w$,
and $d=3|B_w|$. With these replacements the proof of simplicity in
Section~1 applies word for word, so $G_\Delta$ is simple.
```
+2 lines.

### U3 (UNCLEAR): the Fibonacci example (l.366–367)
The Fibonacci subshift is never defined. It is X_α for α = (3−√5)/2, the frequency of 1's, and §3's proof shows that α computes L(X_α).
- Before: `$L(X)$ is recursive, as for the Fibonacci subshift. Every Turing degree`
- After: `$L(X)$ is recursive, as for the Fibonacci subshift $X_{(3-\sqrt5)/2}$ below. Every Turing degree`
- 0 lines.

### U4 (UNCLEAR): letter clashes in §2
- **R, G:** reused for the lamplighter ring and group (l.304), while §1 and §3 mean G_X. Use R_Δ, G_Δ.
- **Z:** the space F_2^Δ (l.295) against \Z in Δ_0×\Z (l.291). Use Ω.
- **ψ_n** (l.314): clashes with ψ: M_d(F_2)→M_3(R) of §1. Use σ_n.
- **ℓ:** elements of L (l.309, 324, 331, 340) against the window radius ℓ of §1 and φ_ℓ, D_ℓ. Use ξ.
- **P:** the ultraproduct group (l.287) against the shift matrix P (l.149) and the permutation matrices P_ℓ (l.324). Use Π.
- **ω:** an ultrafilter never introduced (l.286, 292, 326), while 𝓡^ω already appears. Add "for a nonprincipal ultrafilter ω on ℕ" at l.285.

### U6 (exposition): the intro sentence on §2 (l.89–91)
The group Δ does not do the acting here; L = F_2≀Δ does.
- Before: `The same proof applies to the lamplighter action of a group $\Delta$ on` / `$\F_2^{\Delta}$. It shows that a finitely generated group is LEF if and`
- After: `The same proof works for the lamplighter group $\F_2\wr\Delta$ acting on` / `$\F_2^{\Delta}$, so a finitely generated group is LEF if and`
- 0 lines.

### D1–D3 (doctrine, 0 lines each)
- **D1, l.208:** "hence everywhere" → "so everywhere".
- **D2, l.259–261.**
  - Before: `that embeds in $\mathcal R^\omega$ and whose unitary group contains $G$.` / `This is Brown's formulation. Kirchberg proved that ...`
  - After: `that embeds in $\mathcal R^\omega$ and whose unitary group contains $G$, as in Brown's question. Kirchberg proved that ...`
- **D3, l.272–274.**
  - Before: `The next corollary` / `adds property~\textup{(T)} and applies to every LEF group. Since LEF` / `passes to subgroups, it characterizes LEF groups.`
  - After: `In the next corollary the host also has property~\textup{(T)}, and the input can be any LEF group. Since LEF passes to subgroups, this characterizes LEF groups.`

## 3. Credit audit, sentence by sentence

| l. | credit | verdict |
|---|---|---|
| 45–53 | Brown 2001 §11 Q7; Ozawa 2003 p. 527; Pestov 9.1; Rădulescu, Gromov, Weiss | OK; lineage wording as decided. p. 527 unseen (C2) |
| 71–72 | Kazhdan 1967; EJZ | OK |
| 72–75 | periodic approximation as in GM Thm 2.6 | OK |
| 75–76 | expanders as in Kassabov | OK |
| 76–79 | Stepanov Thm 4.4 route | B1 |
| 83–85 | Matui Lemma 3.4, Thm 4.9, "in the same way" | acceptable; "by a similar argument" is safer |
| 85–87 | Thom | OK |
| 131 | LEF, Vershik–Gordon | OK |
| 147 | bounded complexity ⇒ finite, Morse–Hedlund 1938 | OK |
| 179–182 | marked groups (Grigorchuk, Champetier); (T) of EL_3(F) (EJZ); expanders (Margulis, Kassabov) | OK |
| 185–186 | LEF ⇒ sofic (Pestov Ex. 4.5); sofic ⇒ hyperlinear (Elek–Szabó Thm 2) | OK |
| 255–265 | Ozawa Prop 7.1; McDuff; Kirchberg Thm 1.1; LLP (Ozawa p. 527) | OK; Prop 7.1 checked in arXiv numbering by sk-verify-6; p. 527 unseen (C2) |
| 269–272 | Gorjuškin, Schupp; Kionke–Schesler Thm 1.2 | OK; KS Thm 1.2 verbatim from arXiv v1 p. 2 (sk-lit-novelty-2) (C3) |
| 289 | Ore Thm 1 | OK |
| 354 | Mal'cev | B2 |
| 357–358 | Wilson Thm A | OK (verbatim from the PDF, sk-strong-3) |
| 384–385 | Morse–Hedlund 1940, Hedlund 1944, Lothaire ch. 2 | OK |
| 401–403 | GMpres Thm 1.1(3) | OK |
| 407 | f.p. LEF ⇒ RF, Vershik–Gordon | acceptable (attributed through Kionke–Schesler and Pestov v8) |
| 409–410 | f.p. infinite simple (T) groups exist, Caprace–Rémy | VERIFIED (C1, §4) |
| 416–419 | GPS99, Bezuglyi–Medynets; GPS95 | OK |

**Credit precision:**
- **C2:** every lane read the arXiv version of Ozawa. Journal page 527 is confirmed only through Thom's citation of that page. Low risk; no change.
- **C3:** Crossref has no journal volume or pages for Kionke–Schesler, so the bibitem with DOI plus arXiv is right.

**Optional background (a reader-merits call for main):**
- **C4 (§3):** Camm 1953, continuum many f.g. simple groups (J. LMS s1-28 (1953) 66–76, doi 10.1112/jlms/s1-28.1.66), and Clapham 1964, word-problem degrees of f.p. groups (Proc. LMS s3-14 (1964) 633–676, doi 10.1112/plms/s3-14.4.633). Both Crossref-verified today; statements recalled by sk-panel-referee-5. +2 text lines, +8 bibliography lines. The reader sees which part of the corollary is classical.
- **C5 (§2):** the Boone–Higman parallel (sk-panel-referee-5 F7). +2 text lines, +4 bibliography lines.
- **C6:** the published Rădulescu volume (Theta Ser. Adv. Math. 9, 2008, 173–185; zbMATH 1199.46137). +1 bibliography line.

## 4. Verification run by this lane
- **Crossref on MSI, 20:21 and 20:40**:
  - Wilson: Math. Z. 174(2) 149–157 (1980)
  - Ore: PAMS 2(2) 307–314 (1951)
  - Bezuglyi–Medynets: Colloq. Math. 110(2) 409–429 (2008)
  - GPS99: Israel J. Math. 111(1) 285–320 (1999)
  - Champetier: Topology 39(4) 657–680 (2000)
  - Grigorchuk: Math. USSR-Izv. 25(2) 259–300 (1985)
  - Elek–Szabó: Math. Ann. 332(2) 421–441 (2005)
  - Kazhdan: Funct. Anal. Appl. 1(1) 63–65 (1967)
  - Gromov: JEMS 1(2) 109–197 (1999)
  - Kionke–Schesler: J. Comb. Algebra (2024), no volume or pages
  - Caprace–Rémy: Invent. Math. 176(1) 169–221; online 2008, printed volume 2009
  - Morse–Hedlund 1938 and Hedlund 1944: first pages 815 and 605 only
  - Clark–Edie-Michell: Algebr. Represent. Theory 18(4) 907–916 (2015), doi 10.1007/s10468-015-9522-2, authors Clark, Edie-Michell
  - Dymara–Januszkiewicz: Invent. Math. 150 (2002) 579–627, doi 10.1007/s00222-002-0242-y
- **C1, Caprace–Rémy, VERIFIED** from the arXiv e-print source `SimplSuperrigid.tex` (math/0607664), extracted on MSI:
  - Abstract (l.57–58): "In fact, many of them are finitely presented and enjoy property (T)."
  - l.153–154: "As pointed out to us by Y.~Shalom, we obtain the first infinite {\it finitely presented} discrete groups to be both simple and Kazhdan."
  - l.1813–1815, the corollary on property (T): "If $q_{\rm min} > 1764^{|S|}$, then $\Lambda$ has Kazhdan's property (T). In particular there exist infinitely many isomorphism classes of finitely presented infinite simple groups with Kazhdan's property (T)."
  - l.1806–1807 and l.1820 say its proof uses Dymara–Januszkiewicz and Abramenko–Mühlherr.
  - So rev3's "Finitely presented infinite simple groups with property (T) exist [CapraceRemy]" is correctly credited. Optionally add Dymara–Januszkiewicz as the source of (T).
- **Mal'cev:** no Crossref record. zbMATH has "On isomorphic matrix representations of infinite groups", Rec. Math. Moscou, n. Ser. (Mat. Sb. N.S.) 8 (1940), Zbl 0025.00804, JFM 66.0088.03. The page range 405–422 is recalled: the zbMATH API returned no pages, and the zbMATH web page returned 403 to WebFetch. Check the pages before print.

## 5. Length and exposition (non-blocking)
- **Length:** 7 pages against rev2's 5. The growth is §2 (about 80 lines) and 12 new bibitems. Every fix above is at most +2 lines except the optional C4 and C5.
- **The intro paragraph at l.71–87** holds eight credit sentences in 17 lines. Optionally split it after "an elementary matrix." (l.82–83).
- **Hard-coded "Section~1" at l.309 and l.312:** optionally `\label{sec:proof}` with `\ref`.
