# sk-panel-referee-5, part 1: computability and group theory (hostile top-journal referee)

Lane sk-panel-referee-5, 2026-09-13 ~19:55 CDT.
- **Object:** main's `simple_kazhdan_sofic_group.tex` at tip 230e0f262b. This is revision 2 (landed e80dcf20ad), md5 4ad49212…, 386 lines. Line numbers below refer to that blob.
- **Scope:** computability (§2 Word problems) and group theory (finite models, marked limits, expanders, simplicity, §3 Questions), including credit in both areas. Operator algebras and exposition belong to sk-panel-referee-2/3, and correctness overall to -1.
- **Method:** every step in scope re-derived by hand. Candidate references checked through Crossref on MSI; results in §5.
- **Rev3:** not yet on main (sk-editor-3 is assembling it). Its §2 (LEF iff) needs a separate review once it lands.

## 0. Verdict
- **No mathematical error in scope.** The degree formula, the Sturmian computations, the continued-fraction step, marked convergence, LEF, the simplicity argument, and the not-finitely-presented deduction all check.
- **One GAP in the finite-models/expanders paragraph** (B1): the generators named do not generate EL_3(F), so the "(T) ⇒ expanders" deduction is unsupported as written. The conclusion is true, and the fix is 2 lines.
- **Credit gaps** that a group-theory or computability referee will flag (B2–B5):
  - Margulis for expanders from (T);
  - Morse–Hedlund 1938 for bounded complexity;
  - the classical background for "continuum many" and word-problem degrees;
  - the existence of finitely presented simple Kazhdan groups in Question 1.
- **Free strengthening:** "G_X has solvable word problem iff L(X) is recursive" (F4). It costs one line and answers the reader's first computability question.

## 1. Blocking or near-blocking

### B1. GAP: the generators of EL_3(F) (l.147–164)
- **The claim:** l.153–155 say that G and SL_{3N_ℓ}(F_2) "are quotients of EL_3(F) with compatible generators", and l.163–164 conclude "Since EL_3(F) has property (T), their Cayley graphs form a family of expanders".
- **The problem:** the compatible generators are the e_ij(t) with t ∈ {t_±, t_a}. They do NOT generate EL_3(F), because F is the free unital algebra and 1 is not a sum of products of the t's.
- **Proof:** the augmentation ε: F → F_2 (all t ↦ 0) induces EL_3(F) → SL_3(F_2). It kills every e_ij(t), but sends e_ij(1) to a nontrivial transvection.
- **Why it matters:** a Kazhdan constant for EL_3(F) refers to a generating set of EL_3(F). The images of {e_ij(t)} generate each quotient only because in both quotients e_ij(1) is a bounded product of them:
  - in G, e_ij(1) = Π_a e_ij(e_a), since 1 = Σ e_a (l.109–110);
  - in M_N(F_2), ρ_ℓ(Σ_a t_a) = Σ_a D_ℓ(e_a) = I.
- **What is still true:** the uniform Kazhdan constant for S′ = {e_ij(1), e_ij(t)} descends to the images of {e_ij(t)} with a loss bounded by |A|. So the theorem's expander clause holds, but the proof must say this.
- **Credit in the same sentence:** property (T) of EL_3(F) is EJZ (F is a finitely generated associative unital ring), and "(T) ⇒ finite quotients are expanders" is Margulis (B2).
- **Fix:** F1 in §3, +2 lines.

### B2. Credit: expanders from (T) are Margulis's (l.163–164)
- The text credits only [Kassabov] for "Since EL_3(F) has property (T), their Cayley graphs form a family of expanders".
- The implication is Margulis 1973.
- Kassabov's contribution is to realize SL_{3k}(F_p) as quotients of the Kazhdan groups EL_3(Z⟨x_1,…,x_m⟩). The note uses the same mechanism, so [Kassabov] stays, with the attribution in F1.

### B3. Credit: bounded complexity ⇒ finite (l.130–132)
- The text reads "which tends to infinity with ℓ, since a subshift with boundedly many words of each length is finite". This is the Morse–Hedlund complexity theorem (Amer. J. Math. 60 (1938)).
- The bibliography has only their 1940 Sturmian paper, cited at l.264 for Sturmian subshifts.
- **Fix:** F2, a citation plus a bibitem.

### B4. Computability: two missing clauses in the Sturmian step (l.261–268)
- **(a)** "the words of length n of X_α are the constant values of c(θ)_{[0,n)} on the arcs". This needs that passing to the closure adds no words. It holds because windows of a limit point are windows of approximating codings, but the text never says so.
- **(b)** "So α computes L(X_α)". This needs the points −jα mod 1 (0 ≤ j ≤ n) to be distinct, which follows from irrationality. Then their cyclic order, and a rational point in each arc, are computable from α by strict comparisons that never tie. The distinctness is used and never stated.
- **Fix:** F3, +0 to +1 lines.

### B5. Credit context for §2 and Question 1
- **"Continuum many pairwise nonisomorphic G_X" and "every Turing degree occurs":**
  - continuum many 2-generator simple groups is classical: Camm 1953;
  - realizing word-problem degrees is classical: Clapham 1964 realizes every recursively enumerable degree by a finitely presented group (Boone and Fridman had related results).
  - The new content is realization inside infinite simple Kazhdan LEF groups. A referee will ask for one background clause (F5).
- **Question 1 (l.283–284)** asks for a finitely presented infinite simple Kazhdan sofic group, but never says such groups exist. Caprace–Rémy 2009 (twin building lattices) provides them. Without the clause a reader may think the question is about existence. **Fix:** F6.

## 2. What would make it astonishing (from this chair)
1. **The characterization from rev3**: a f.g. group is LEF iff it is a subgroup of an infinite f.g. simple Kazhdan LEF group. It should be framed next to the Boone–Higman theorem, where a f.g. group has solvable word problem iff it embeds in a simple subgroup of a finitely presented group (J. Austral. Math. Soc. 18 (1974) 41–53).
   - The parallel is exact in shape: "property of Γ ⟺ Γ embeds in a simple group of a special kind".
   - Group theorists will remember the note for this. One sentence (F7) once §2 lands.
2. **Universal host paragraph** (Wilson 1980): one simple Kazhdan LEF group containing every f.g. linear group.
   - The classical analogue is P. Hall's universal 2-generator simple hosts (J. Austral. Math. Soc. 17 (1974) 434–495).
   - Credit in one clause.
3. **Word-problem control of the envelope** (sk-wp-embedding, unreviewed): perfect, effectively residually finite Γ with solvable word problem embed in hosts with solvable word problem.
   - If a verifier passes it, a one-clause remark after F7 would make the Boone–Higman parallel quantitative.
   - Do NOT state the full iff: sk-wp-embedding shows it is false as first posed, and the coherent Ore step is open.
4. **Not recommended:**
   - tt- or m-degree realization: L(X_α) ≤_tt α is not established;
   - the conjugacy problem;
   - Kuznetsov's theorem: redundant once F4 is in.

## 3. Line-level fixes (verbatim LaTeX)

### F1 (B1, B2): the generators and the expander deduction. +2 text lines, +4 bibliography lines
Before, l.153–155:
```latex
with $P$ every matrix unit. So $G$ and
$\EL_3(M_{N_\ell}(\F_2))=\SL_{3N_\ell}(\F_2)$ are quotients of $\EL_3(F)$
with compatible generators. The equality holds since transvections
```
After:
```latex
with $P$ every matrix unit. So $G$ and
$\EL_3(M_{N_\ell}(\F_2))=\SL_{3N_\ell}(\F_2)$ are quotients of $\EL_3(F)$,
which is generated by the matrices $e_{ij}(1)$ and $e_{ij}(t)$ with
$t\in\{t_\pm,t_a\}$. The equality holds since transvections
```
Before, l.163–164:
```latex
groups, and $G$ is LEF. Since $\EL_3(F)$ has property~\textup{(T)}, their
Cayley graphs form a family of expanders~\cite{Kassabov}. LEF groups are
```
After:
```latex
groups, and $G$ is LEF. Since $\EL_3(F)$ has property~\textup{(T)}~\cite{EJZ},
its finite quotients form a family of expanders~\cite{Margulis}, as in
Kassabov's construction~\cite{Kassabov}. In both quotients $e_{ij}(1)$ is
the image of $\prod_ae_{ij}(t_a)$, so this holds for the images of the
$e_{ij}(t)$. LEF groups are
```
Bibitem. The metadata is recalled, not Crossref-verified (this journal has no DOI); sk-lit-locators should confirm it:
```latex
\bibitem{Margulis}
G.~A. Margulis, \emph{Explicit constructions of expanders},
Problemy Peredachi Informatsii \textbf{9} (1973), no.~4, 71--80;
English transl., Problems Inform. Transmission \textbf{9} (1973), 325--332.
```
Check behind it: the uniform Kazhdan constant for S′ = {e_ij(1), e_ij(t)} gives uniform spectral gaps for the images of S′. Each image of e_ij(1) is a product of |A| images of the e_ij(t_a), so the gap for the images of {e_ij(t)} degrades by at most a factor depending on |A|. N_ℓ → ∞ (l.130–131), so the orders are unbounded.

### F2 (B3): Morse–Hedlund 1938. +0 text lines, +4 bibliography lines
Before, l.131–132:
```latex
these words, which tends to infinity with $\ell$, since a subshift with
boundedly many words of each length is finite.
```
After:
```latex
these words, which tends to infinity with $\ell$, since a subshift with
boundedly many words of each length is finite~\cite{MorseHedlund38}.
```
Bibitem, metadata Crossref-verified (§5):
```latex
\bibitem{MorseHedlund38}
M.~Morse and G.~A. Hedlund, \emph{Symbolic dynamics},
Amer. J. Math. \textbf{60} (1938), 815--866.
\doi{10.2307/2371264}.
```
The end page 866 is recalled; Crossref gives the start page 815. No theorem number is given, because I did not open the paper.

### F3 (B4): the Sturmian step. +1 text line
Before, l.265–268:
```latex
if and only if $\theta$ lies in the arc $[-(t+1)\alpha,-t\alpha)$ modulo
$1$, and the words of length $n$ of $X_\alpha$ are the constant values of
$c(\theta)_{[0,n)}$ on the arcs between the points $-j\alpha\bmod1$,
$0\le j\le n$. So $\alpha$ computes $L(X_\alpha)$. Since
```
After:
```latex
if and only if $\theta$ lies in the arc $[-(t+1)\alpha,-t\alpha)$ modulo
$1$. Passing to the closure adds no words, so the words of length $n$ of
$X_\alpha$ are the constant values of $c(\theta)_{[0,n)}$ on the arcs
between the points $-j\alpha\bmod1$, $0\le j\le n$, which are distinct as
$\alpha$ is irrational. So $\alpha$ computes $L(X_\alpha)$. Since
```

### F4 (free strengthening): solvable word problem. +1 text line
Before, l.242–244:
```latex
The word problem of $G_X$ has the Turing degree of the language $L(X)$
of $X$. Every Turing degree occurs, so there are continuum many pairwise
nonisomorphic groups $G_X$.
```
After:
```latex
The word problem of $G_X$ has the Turing degree of the language $L(X)$
of $X$. In particular $G_X$ has solvable word problem if and only if $L(X)$
is recursive, as for the Fibonacci subshift. Every Turing degree occurs, so
there are continuum many pairwise nonisomorphic groups $G_X$.
```
- **Check:** immediate from the degree formula. The Fibonacci language is recursive because it is the coding of a rotation by a computable α.
- **Optional, same length:** "truth-table degree" in place of "Turing degree" in the first sentence. The upper bound queries finitely many words fixed in advance; the lower bound is a many-one reduction of the complement of L(X). The realization sentence must stay with Turing degrees.

### F5 (B5): background for §2. +2 text lines, +8 bibliography lines
Insert after the corollary's statement, before the Grigorchuk–Medynets sentence (l.246–247):
```latex
Camm found continuum many finitely generated simple groups~\cite{Camm},
and Clapham realized every recursively enumerable degree as the degree of
the word problem of a finitely presented group~\cite{Clapham}.
```
Bibitems, metadata Crossref-verified (§5):
```latex
\bibitem{Camm}
R.~Camm, \emph{Simple free products},
J. London Math. Soc. \textbf{28} (1953), 66--76.
\doi{10.1112/jlms/s1-28.1.66}.

\bibitem{Clapham}
C.~R.~J. Clapham, \emph{Finitely presented groups with word problems of
arbitrary degrees of insolubility}, Proc. London Math. Soc. (3)
\textbf{14} (1964), 633--676.
\doi{10.1112/plms/s3-14.4.633}.
```
- **Status:** the statements are recalled from standard references (Lyndon–Schupp, Ch. IV), not read from the papers. sk-lit-credit-audit or sk-lit-locators should confirm them before landing.
- **Reader-facing trade-off:** the reader learns which parts of the corollary are classical, at the cost of two sentences.

### F6 (B5): existence in Question 1. +1 text line, +4 bibliography lines
Before, l.283–284:
```latex
presented. Is there a finitely presented infinite simple group with
property~\textup{(T)} that is sofic, or at least hyperlinear? A positive
```
After:
```latex
presented. Finitely presented infinite simple groups with
property~\textup{(T)} exist~\cite{CapraceRemy}. Is there one that is sofic,
or at least hyperlinear? A positive
```
Bibitem. sk-fp-sofic-a verified it through Crossref; the theorem number is not needed:
```latex
\bibitem{CapraceRemy}
P.-E. Caprace and B.~R\'emy, \emph{Simplicity and superrigidity of twin
building lattices}, Invent. Math. \textbf{176} (2009), 169--221.
\doi{10.1007/s00222-008-0162-6}.
```

### F7 (for rev3's §2, once it lands): the Boone–Higman parallel. +2 text lines, +4 bibliography lines
Put this after the statement of the LEF characterization:
```latex
This is an analogue of the theorem of Boone and Higman that a finitely
generated group has solvable word problem if and only if it embeds in a
simple subgroup of a finitely presented group~\cite{BooneHigman}.
```
Bibitem, metadata Crossref-verified (§5). The statement is recalled; confirm against p. 41 before landing:
```latex
\bibitem{BooneHigman}
W.~W. Boone and G.~Higman, \emph{An algebraic characterization of groups
with soluble word problem}, J. Austral. Math. Soc. \textbf{18} (1974), 41--53.
\doi{10.1017/S1446788700019108}.
```
For the universal-host paragraph, the classical context is P.~Hall, *On the embedding of a group in a join of given groups*, J. Austral. Math. Soc. 17 (1974) 434–495, doi:10.1017/S1446788700018073 (Crossref-verified). Use one clause only if the paragraph is adopted.

### F8 (optional, +1 line): why the degree is an invariant (l.275–276)
Before: `earlier digits. There are continuum many degrees, and the degree of the` / `word problem is an isomorphism invariant.`
After: `earlier digits. There are continuum many degrees, and the degree of the word problem does not depend on the finite generating set, so it is an isomorphism invariant.`

## 4. Checked and correct (no change)
- **Upper bound (l.252–257):** entries Σ_j f_j u^j with tables computed in LC(A^Z,F_2)⋊Z. The restriction to X is a ring homomorphism onto R (l.252–253). Triviality ⟺ the tables vanish on the finitely many words of L(X) of the computed lengths. Generators are their own inverses over F_2, so words need no inverse letters.
- **Lower bound (l.257–259):** Π_{t<n} u^{-t}e_{v_t}u^t = e_{[v]} at positions 0..n−1, using ue_Uu^{-1} = e_{TU} and (Tx)_t = x_{t+1}. Recursive commutators give a computable word, with length exponential in n, which is harmless. It is trivial iff [v] = ∅ iff v ∉ L(X).
- **Sturmian coding:**
  - c(θ)_t = 1 ⟺ θ ∈ [−(t+1)α, −tα) mod 1, because θ + tα ∈ [1−α, 1) mod 1.
  - The telescoping count ⌊θ+nα⌋ − ⌊θ⌋ = ⌊θ+nα⌋ holds for θ ∈ [0,1), and nα−1 < ⌊θ+nα⌋ < nα+1.
  - Any word of length n gives α to within 1/n. α is irrational, so its binary digits are computable from such approximations.
- **Continued fraction:** each digit lies in {1,2}. The digit is 1 iff the tail value exceeds 1/2, decided by one strict comparison with a rational built from the earlier digits, and there are no ties because the number is irrational.
- **Marked convergence (l.157–163):** for a fixed L there are finitely many words of length L, so a single ℓ works for all of them. Marked convergence and LEF follow.
- **Simplicity (l.180–237):** in scope for group theory, all steps re-derived:
  - the unit step over F_2;
  - ε_{ab}ε_{a′b′} = δ_{ba′}ε_{ab′} using no returns up to 2w;
  - the transvection commutators inside blocks;
  - k ∈ H through (I_d+A)(I_d+B) = I_d;
  - the level ideal and covering.
- **Not finitely presented (l.281–283):** f.p. LEF ⇒ RF, and an infinite simple group is not RF.
- **Question 3 (l.289–291):** the easy direction is correct, since a flip conjugacy gives the ring isomorphism fu^j ↦ (f∘ψ^{-1})u^{±j}.

## 5. Crossref results (MSI, 2026-09-13 ~19:50), first hit for each query
- Morse–Hedlund, *Symbolic Dynamics*, Amer. J. Math. 60 (1938), p. 815, doi 10.2307/2371264. The 1940 Sturmian paper is 10.2307/2371431, as already in the bibliography.
- Clapham, *Finitely Presented Groups with Word Problems of Arbitrary Degrees of Insolubility*, Proc. LMS s3-14 (1964) 633–676, doi 10.1112/plms/s3-14.4.633.
- B. H. Neumann, *Some Remarks on Infinite Groups*, J. LMS s1-12 (1937) 120–127, doi 10.1112/jlms/s1-12.46.120. Not proposed.
- Camm, *Simple Free Products*, J. LMS s1-28 (1953) 66–76, doi 10.1112/jlms/s1-28.1.66.
- Boone–Higman, *An algebraic characterization of groups with soluble word problem*, J. Austral. Math. Soc. 18 (1974) 41–53, doi 10.1017/s1446788700019108.
- P. Hall, *On the embedding of a group in a join of given groups*, J. Austral. Math. Soc. 17 (1974) 434–495, doi 10.1017/s1446788700018073.
- Champetier, *L'espace des groupes de type fini*, Topology 39 (2000) 657–680, doi 10.1016/s0040-9383(98)00063-9. It is the reference for the space of marked groups, which the text uses at l.56 and l.162 without citing. Optional credit, 0 text lines.
- Not found or failed: Margulis 1973 (no Crossref record expected); the Grigorchuk 1984 query returned a malformed response.

## 6. Summary of costs (all optional except F1)

| fix | text lines | bibliography lines | status |
|---|---|---|---|
| F1 generators and Margulis (GAP) | +2 | +4 | required; Margulis metadata recalled |
| F2 Morse–Hedlund 1938 | 0 | +4 | Crossref verified |
| F3 Sturmian clauses | +1 | 0 | recommended |
| F4 solvable word problem | +1 | 0 | recommended |
| F5 Camm, Clapham background | +2 | +8 | recommended; statements recalled |
| F6 Caprace–Rémy existence | +1 | +4 | recommended |
| F7 Boone–Higman parallel (rev3) | +2 | +4 | after §2 lands; statement recalled |
| F8 generating-set clause | +1 | 0 | optional |
