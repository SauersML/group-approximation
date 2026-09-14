# sk-rev3-referee-b: referee report on revision 3 (credit, exposition, claims proved)

Lane sk-rev3-referee-b (ROSTER-G), 2026-09-13 ~20:40 CDT. Referee (b): credit, exposition, and whether every claim in the abstract and theorem is proved in the text. Referee (a) owns correctness in depth.

- **Subject:** `sk/drafts/rev3.tex`, assembled 20:24, 614 lines, md5 2a0264d7ec918ea5b8ad7fc198a97c3d, identical to partA+partB+partC. Line numbers below refer to it.
- **My compile:** MSI texlive/2025, pdflatex 3 passes: 0 errors, 0 overfull, 0 undefined, 3 underfull (bibitems), 7 pages.
- **Mechanical checks:** every `\cite` key has a bibitem and every bibitem is cited (35 keys); labels `thm:main`, `cor:lef`, `eq:elementary` resolve; no Codex, OpenAI or Astra anywhere.
- **Read for context:** rev3-changelog.md; sk-panel-referee-4/5/6 part1; sk-lit-credit-audit proposal; sk-lit-novelty-2; sk-lit-background part1.

## 0. Verdict
- **No ERROR in scope.** Every claim of the abstract and of Theorem 1 has a proof or a correct citation in the text (§1).
- **Two credit GAPs, each a one-line fix:**
  - B1: the introduction asserts "the ring is simple" (l.76) with no proof and no citation. Rev1 removed the ring-simplicity proof and its citations, because the direct proof no longer needs it; the Stepanov sentence still does.
  - B2: Mal'cev's theorem is used by name (l.352) with no citation.
- **UNCLEAR, short fixes:**
  - U1: quantifiers in the marked-limit step (l.171–178).
  - U2: §2's "word for word" replacement list omits the index set and d (l.305–310).
  - U3: "as for the Fibonacci subshift" (l.365) refers to an object never defined.
  - U4: letter clashes in §2 (R, G, Z, ψ, ℓ, P, ω).
  - U5: the countability of f.g. linear groups is asserted without its one-clause reason (l.353).
- **Credit items outside the text, low risk:** C1 Caprace–Rémy existence sentence; C2 Ozawa's journal page; C3 Kionke–Schesler numbering; optional background C4–C6.
- **Doctrine:** D1 "hence" (l.206); D2 "This is Brown's formulation." (l.259); D3 "The next corollary adds" (l.270).
- **Recommendation:** land rev3 after B1, B2, U1–U3 and D1–D3, about +5 text lines and +7 bibliography lines, once referee (a) has also reported. U4 is strongly recommended but can go to rev4.

## 1. Claims of the abstract and of Theorem 1, and where they are proved

| claim | location | verdict |
|---|---|---|
| G_X infinite | l.125–126 | proved |
| finitely generated | l.109–122 | proved |
| property (T) | l.122–125 | cited, EJZ Thm 1.1 |
| simple | l.186–250 | proved |
| marked limit of finite simple SL_{3N}(F_2) | l.160–178 | proved; U1 quantifiers |
| expanders with respect to the images of a fixed generating set | l.178–183 | proved. (T) of EL_3(F) plus Margulis/Kassabov, then the transfer through e_ij(1)=∏_a e_ij(τ_a) in both quotients. N_ℓ→∞ at l.142–145 |
| LEF | l.178 | proved, as a marked limit of finite groups |
| sofic, hyperlinear | l.183–184 | cited (Pestov Ex. 4.5; Elek–Szabó Thm 2) |
| the same for EL_n, n≥3, with SL_{nN} | l.95–96 | substitution stated; every n-dependent step checked (see below) |
| answers Brown, Ozawa, Pestov | l.43–51, l.252–263 | proved; Brown's printed form through L(G)⊗̄𝓡 |
| LEF iff subgroup of an infinite f.g. simple Kazhdan LEF group | §2, l.274–343 | proved; U2, U4 |
| one such group contains every f.g. linear group | l.345–358 | proved; B2, U5 |
| every Turing degree is the word-problem degree of some G_X | §3, l.362–397 | proved |
| solvable WP iff L(X) recursive, "as for the Fibonacci subshift" | l.364–365 | the iff is proved; the example needs U3 |
| G_X not finitely presented (Questions) | l.405–407 | cited (Vershik–Gordon) |

**n-dependent steps for "EL_n, n≥3":**
- EJZ holds for n≥3.
- The generation identities (1) need three distinct indices.
- EL_n(M_N(F_2)) = SL_{nN}(F_2).
- The criterion for commuting with e_ij(r) holds for every n.
- d = n(2w+1).
- The in-block transvection uses p′≠p, and the level ideal uses l∉{p,q}.

All survive the substitution.

## 2. Findings with verbatim fixes

### B1 (GAP, credit): "the ring is simple" is unsupported (l.74–77)
Rev3 keeps main's decision 44, that simplicity also follows from Stepanov's Theorem 4.4. For a simple ring that theorem applies at level I=0, so the sentence needs R simple. The note no longer proves this: rev1 deleted the ring-simplicity paragraph, and with it the Clark–Edie-Michell, Steinberg and BCFS citations. So the intro states an unsupported fact.

Before (l.74–77):
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
Bibitem (VERIFY-PENDING, see §4):
```latex
\bibitem{ClarkEdie}
L.~O. Clark and C.~Edie-Michell, \emph{Uniqueness theorems for Steinberg
algebras}, Algebr. Represent. Theory \textbf{18} (2015), 907--916.
\doi{10.1007/s10468-015-9522-2}.
```
- Cost: +1 text line, +4 bibliography lines.
- Trade-off: the alternative proof gets a source for its one outside fact.
- Status: sk-citations (6b259b4463) checked Cor 4.6 against arXiv v1 (simple over any field for minimal effective Hausdorff ample groupoids); the journal numbering was not opened. The metadata came from the disk version's bibitem (arXiv:1403.4684), which sk-citations verified, plus the DOI from its P8.
- Alternative with 0 net lines: delete "since the ring is simple and" and keep only the dimension count. Then the Stepanov route is a sketch with a hidden input, which is worse for the reader.

### B2 (GAP, credit): Mal'cev's theorem uncited (l.351–354)
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
Bibitem (VERIFY-PENDING, see §4):
```latex
\bibitem{Malcev}
A.~I. Mal'cev, \emph{On isomorphic matrix representations of infinite
groups}, Mat. Sb. \textbf{8(50)} (1940), 405--422.
```
- Cost: +1 text line (it also fixes U5), +3 bibliography lines.
- Trade-off: every theorem the proof uses gets a source; countability gets its reason.
- Checked: a f.g. linear group lies in GL_n(K) with K generated by the entries of its generators. There are countably many f.g. fields up to isomorphism, and countably many f.g. subgroups of GL_n(K) for countable K.

### U1 (UNCLEAR): quantifiers in the marked limit (l.171–178)
Marked convergence needs, for every λ, agreement on all words of length ≤ λ for all large ℓ. The text states it one word at a time. sk-panel-referee-6 §2.2 flagged the same wording in rev2.

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
Cost: +1 line. Trade-off: the definition of marked convergence is visibly met.

### U2 (UNCLEAR): the "word for word" replacement list (l.305–310)
The list replaces u^t, T^tV, sums of exponents and |t|, but not the index range of ε_ab or the value of d. Over L the indices a,b run over the ball B_w, ε_ab = e_{aV}u_{ab^{-1}}, and d = 3|B_w|. I re-derived the product rule ε_abε_{a′b′} = δ_{ba′}ε_{ab′}, which uses V ∩ ξV = ∅ for ξ ∈ B_{2w}∖{e}, and the product formula fu_a e_V f′u_b ∈ {0, ε_{a,b^{-1}}}. The sk-rev3-referee-a/sk-editor-3 flag that this LaTeX has never been reviewed is correct; with this sentence the substitution is complete.

Before (l.305–310):
```latex
property~\textup{(T)}~\cite[Theorem~1.1]{EJZ}, and it is infinite. Points
with trivial stabilizer in a given ball are dense, so every nonempty
clopen set contains a small one, in the sense of Section~1 with $u_\ell$
for $u^t$, $\ell V$ for $T^tV$, products in $L$ for sums of exponents,
and word length for $|t|$. With these replacements the proof of
simplicity in Section~1 applies word for word, so $G$ is simple.
```
After (it also takes the §2 renames of U4):
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
Cost: +2 lines.

### U3 (UNCLEAR): the Fibonacci example (l.364–365)
The Fibonacci subshift is never defined. §3's proof defines X_α; the Fibonacci subshift is X_α with α = (3−√5)/2 (the frequency of 1's), and α computes L(X_α) by that proof.

Before: `$L(X)$ is recursive, as for the Fibonacci subshift. Every Turing degree`
After: `$L(X)$ is recursive, as for the Fibonacci subshift $X_{(3-\sqrt5)/2}$ below. Every Turing degree`

Cost: 0 lines. Trade-off: the example is checked by the proof that follows.

### U4 (UNCLEAR): letter clashes in §2 (recommended, can wait for rev4)
- **R, G** reused for the lamplighter ring and group (l.302), while §1 and §3 mean G_X. Use R_Δ, G_Δ.
- **Z** for the space F_2^Δ (l.293) against \Z in Δ_0×\Z (l.289). Use Ω.
- **ψ_n** (l.312) against ψ: M_d(F_2)→M_3(R) in §1. Use σ_n.
- **ℓ** for elements of L (l.307, 322, 329, 338) against the window radius ℓ in §1 and φ_ℓ, D_ℓ. Use ξ.
- **P** for the ultraproduct group (l.285) against the shift matrix P (l.147) and the permutation matrices P_ℓ (l.322). Use Π.
- **ω** used as an index set of ultraproducts (l.284, 290, 324) but never introduced, while 𝓡^ω already appears. Add "for a nonprincipal ultrafilter ω on ℕ" at l.283.

### D1–D3 (doctrine, 0 lines each)
- D1, l.206: `everywhere, since every nonempty clopen set contains a small one.` — change "hence everywhere" (l.206) to "so everywhere".
- D2, l.257–259. Before: `that embeds in $\mathcal R^\omega$ and whose unitary group contains $G$.` / `This is Brown's formulation. Kirchberg proved that ...`. After: `that embeds in $\mathcal R^\omega$ and whose unitary group contains $G$, as in Brown's question. Kirchberg proved that ...`
- D3, l.270–272. Before: `The next corollary` / `adds property~\textup{(T)} and applies to every LEF group. Since LEF` / `passes to subgroups, it characterizes LEF groups.` After: `In the next corollary the host also has property~\textup{(T)}, and the input can be any LEF group. Since LEF passes to subgroups, this characterizes LEF groups.`

### U6 (exposition, 0 lines): the intro sentence on §2 (l.87–91)
"the lamplighter action of a group Δ" is imprecise: Δ does not act; L = F_2≀Δ does.
Before: `The same proof applies to the lamplighter action of a group $\Delta$ on` / `$\F_2^{\Delta}$. It shows that a finitely generated group is LEF if and`
After: `The same proof works for the lamplighter group $\F_2\wr\Delta$ acting on` / `$\F_2^{\Delta}$, so a finitely generated group is LEF if and`

## 3. Credit audit of rev3, sentence by sentence (my verdicts)

| l. | credit sentence | verdict |
|---|---|---|
| 43–51 | Brown 2001 §11 Q7; Ozawa 2003 p. 527; Pestov 9.1; Rădulescu, Gromov, Weiss | OK. Lineage wording follows the user's decisions. Ozawa's journal p. 527 is unseen (C2) |
| 69–70 | Kazhdan 1967; EJZ | OK |
| 70–73 | periodic approximation as in GM Thm 2.6 | OK (sk-citations P1 wording) |
| 73–74 | expanders as in Kassabov | OK |
| 74–77 | Stepanov Thm 4.4 route | needs B1 |
| 81–83 | Matui Lemma 3.4, Thm 4.9 "in the same way" | acceptable. "by a similar argument" would be safer; sk-draft-minimal flagged "in the same way" as possibly overstating |
| 83–85 | Thom | OK |
| 129 | LEF, Vershik–Gordon | OK |
| 145 | bounded complexity ⇒ finite, Morse–Hedlund 1938 | OK |
| 177–180 | marked groups (Grigorchuk, Champetier); (T) of EL_3(F) (EJZ); expanders (Margulis, Kassabov) | OK |
| 183–184 | LEF ⇒ sofic (Pestov Ex. 4.5); sofic ⇒ hyperlinear (Elek–Szabó Thm 2) | OK |
| 253–263 | Ozawa Prop 7.1; McDuff; Kirchberg Thm 1.1; LLP (Ozawa p. 527) | OK. Prop 7.1 checked in arXiv numbering by sk-verify-6; p. 527 unseen (C2) |
| 267–270 | Gorjuškin, Schupp; Kionke–Schesler Thm 1.2 | OK. KS Thm 1.2 verbatim from arXiv v1 p. 2 (sk-lit-novelty-2); journal numbering unseen (C3) |
| 287 | Ore Thm 1 | OK |
| 352 | Mal'cev | B2 |
| 355–356 | Wilson Thm A | OK (verbatim from the PDF, sk-strong-3) |
| 382–383 | Morse–Hedlund 1940, Hedlund 1944, Lothaire ch. 2 | OK |
| 399–401 | GMpres Thm 1.1(3) | OK |
| 405 | f.p. LEF ⇒ RF, Vershik–Gordon | acceptable; attributed through Kionke–Schesler and Pestov v8, VG itself not opened |
| 407–408 | f.p. infinite simple (T) groups exist, Caprace–Rémy | C1 |
| 414–417 | GPS99, Bezuglyi–Medynets; GPS95 | OK (sk-panel-referee-4 B3) |

**C1 (Caprace–Rémy).** One citation carries finite presentation, simplicity and property (T). Caprace–Rémy prove simplicity of twin building lattices. Whether their paper itself states that some of these lattices are finitely presented with property (T), or cites that to others, is VERIFY-PENDING (§4). If it cites others, the fix is to add that source, not to drop the sentence.

**C2 (Ozawa p. 527).** Every lane read the arXiv version only; the journal page is confirmed only indirectly, through Thom's citation of that page. Low risk. A version-independent locator is `\cite[\S7]{Ozawa}`, but the journal's section numbering is unseen too, so I recommend no change.

**C3 (Kionke–Schesler Theorem 1.2).** The arXiv v1 numbering is verified. Crossref has no volume or pages for the journal version, so the bibitem with DOI plus arXiv is right.

**Optional background (C4–C6), a reader-merits call for main:**
- C4, §3: continuum many f.g. simple groups (Camm 1953) and word-problem degrees of f.p. groups (Clapham 1964). Bibitems are Crossref-verified in sk-panel-referee-5 §3 F5; the statements there are recalled. +2 text lines, +8 bibliography lines. It tells the reader which part of the corollary is classical.
- C5, §2: the Boone–Higman parallel (sk-panel-referee-5 F7), +2 text lines, +4 bibliography lines. It makes Corollary 2 memorable.
- C6: the published Rădulescu volume (Theta Ser. Adv. Math. 9, 2008, 173–185; zbMATH 1199.46137), +1 bibliography line.

## 4. Verification this lane ran, and pending checks
- **Crossref on MSI, ~20:21 (13 DOIs).** All agree with rev3's bibitems:
  - Wilson (Math. Z. 174(2) 149–157, 1980);
  - Ore (PAMS 2(2) 307–314, 1951);
  - Bezuglyi–Medynets (Colloq. Math. 110(2) 409–429, 2008);
  - GPS99 (Israel J. Math. 111(1) 285–320, 1999);
  - Champetier (Topology 39(4) 657–680, 2000);
  - Grigorchuk (Math. USSR-Izv. 25(2) 259–300, 1985);
  - Elek–Szabó (Math. Ann. 332(2) 421–441, 2005);
  - Kazhdan (Funct. Anal. Appl. 1(1) 63–65, 1967);
  - Gromov (JEMS 1(2) 109–197, 1999);
  - Kionke–Schesler (J. Comb. Algebra, 2024, no volume or pages);
  - Morse–Hedlund 1938 and Hedlund 1944: first pages 815 and 605 only.
- **Caprace–Rémy.** Crossref gives 176(1) 169–221 with online year 2008; rev3 prints 2009, the print year of volume 176. OK.
- **Mal'cev.** No Crossref record (query 20:21).
- **Pending (MSI master down at ~20:38):** the C1 wording in the Caprace–Rémy source; the Clark–Edie-Michell DOI and Cor 4.6; Mal'cev's pages. Results are appended below when checked.

## 5. Length and exposition (non-blocking)
- **Length.** Rev3 is 7 pages against rev2's 5. The growth is §2 (about 80 lines) and 12 new bibitems. Every addition in this report is ≤1 line except C4 and C5.
- **The intro paragraph at l.69–85** is 17 lines holding eight credit sentences. Optional split into two paragraphs, after "a clopen tower, so it contains this group and with it an elementary matrix." (l.80–81).
- **Hard-coded "Section~1" (l.307, 310).** Optional: `\label{sec:proof}` with `\ref`.
