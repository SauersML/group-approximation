# sk-operator-algebras: which operator-algebra corollaries belong in the note (2026-09-13)

Lane `sk-operator-algebras`, SK swarm. The note is `$SK/manuscript-disk-1646.tex` (340 lines, md5 7b3dc4ec…); line numbers refer to it.
G = G_X = EL_3(LC(X,F_2) ⋊_T Z) for an infinite minimal subshift X. The same statements hold for S_X = EL_3(LC(X,F_q) ⋊ Z)/Z.

## 0. Verdicts in one table

| # | Candidate corollary | True? | In the note? |
|---|---|---|---|
| 1 | G lies in U(L(G)⊗̄R), a separable McDuff factor that embeds in R^ω (Brown's question as printed) | TRUE, §2.1 | YES: one to two sentences. The note claims to answer Brown's form and gives no bridge. |
| 2 | G embeds in U(R) for no faithful representation (Kirchberg Cor. 1.2) | TRUE, §2.2 | OPTIONAL clause: the McDuff factor cannot be hyperfinite. It answers Brown's parenthetical comparison with Robertson. |
| 3 | G lacks the factorization property, and C*(G) fails the LLP | TRUE (main node PASS, conditional on imports) | YES: one sentence. This is Ozawa's own reason for asking. |
| 4 | L(G) is a property (T) II_1 factor inside R^ω | TRUE (Connes–Jones) | NO. (T) factors in R^ω already exist, e.g. L(SL_3(Z)). |
| 5 | G is an MF group and not weakly quasidiagonal, contrary to Dadarlat's introduction | TRUE | NO. It corrects a slip in a paper the note does not otherwise need, and Dadarlat's own Prop. 3.19 lead-in already says infinite simple (T) groups are not weakly QD. |
| 6 | The canonical trace on C*(G) is an MF trace but not amenable or QD | TRUE (main PASS (ii)–(iv)) | NO. It needs two definitions, and at the trace level it is the same fact as #3: an amenable canonical trace is equivalent to the factorization property. |
| 7 | C*_r(G) has a unique trace | TRUE, routine (BKKO: simple nonamenable gives trivial amenable radical) | NO. |
| 8 | G is minimally almost periodic, so C*(G) is not RFD | TRUE, routine (Malcev; node `fg-infinite-simple-groups-are-minimally-almost-periodic`) | NO. |
| 9 | C*_r(G) is MF | OPEN (`directly-finite-subshift-el-n-reduced-cstar-is-mf`; root `infinite-kazhdan-group-with-mf-reduced-cstar`) | Only as a closing question, if the note has one. |
| 10 | G is C*-simple | UNKNOWN to this lane. The BKKO linear criterion does not apply, since f.g. linear groups are RF. | NO. |

## 1. Sources, verbatim

pdftotext on MSI fails (poppler libstdc++ mismatch). Quotes come from the arXiv e-print LaTeX sources, and Kirchberg's from the Springer PDF, read as page images.

- **Brown**, arXiv:math/0111286v1, §11, source text of Question 7:
  "Can an infinite, simple, discrete group with Kazdan's property T be embed into the unitary group of an $R^{\omega}$-embeddable McDuff factor? (Compare with \cite{robertson} where it is shown that no such embedding exists into the unitary group of $L({\mathbb F}_n)\bar{\otimes} R$ or, more generally, $L(\Gamma)$ for any a-T-amenable discrete group $\Gamma$.)"
- **Ozawa**, arXiv:math/0306067v1, §7 "Groups with the Factorization Property". The numbering is checked: `\newtheorem{prop}[thm]` shares the section counter, and §7 opens with prop, defn, prop\label{rf}, thm, which are 7.1–7.4.
  - Prop. 7.1: "A group $\G$ is hyperlinear if and only if $L\G$ is $*$-isomorphic to a von Neumann subalgebra of $R^\omega$."
  - Thm. 7.4: "Let $\tau$ be a trace on the full $C^*$-algebra $C^*\G$ of a group $\G$ with Kazhdan's property $\mathrm{(T)}$. Then, $\tau$ is liftable if and only if there is a sequence of $*$-homomorphisms $\pi_n\colon C^*\G\to\M_{k(n)}$ such that $\tau(a)=\lim_n\tr_{k(n)}\pi_n(a)$. In particular, a group $\G$ with the properties $\mathrm{(F)}$ and $\mathrm{(T)}$ is residually finite." Ozawa's text before it: "The following proof is close to that of Kirchberg \cite{kf}, but uses an idea of Bekka."
  - Right after the proof of Thm. 7.4: "It is unknown whether there exists a simple property $\mathrm{(T)}$ group $\G$ which is hyperlinear. By the above theorem, the full $C^*$-algebra $C^*\G$ of such a group $\G$ cannot have the LLP." Earlier lanes verified this passage as p. 527 of the journal version, which the note already cites.
- **Kirchberg**, Math. Ann. 299 (1994), 551–563. The page header is read from the PDF; Crossref gives DOI 10.1007/BF01459798, vol. 299, pp. 551–563. Quotes from p. 552:
  - "Theorem 1.1 A discrete group with property (F) and property T is residually finite."
  - "Corollary 1.2 For a discrete group G with property T, the following properties are equivalent: (i) G has property (F). (ii) There exists a faithful unitary representation from G into the hyperfinite II$_1$-factor. (iii) … nuclear universal group C*-algebra C*(H). (iv) G is residually finite. (v) … almost connected locally compact group."
  - "The implications (iv)⇒(v)⇒(iii)⇒(i) and (iv)⇒(ii)⇒(i) are true in full generality."
  - Thom, arXiv:0810.2180, points out an error only in (v)⇒(i). Items #2 and #3 use only (ii)⇒(i) and Thm. 1.1.
- **Pestov**, arXiv:0804.3968v8, theorem `th:iff`: "[Kirchberg; Radulescu, Prop. 2.5; Ozawa, Prop. 7.1] Let $G$ be a countable group. Then $VN(G)$ embeds into $R^\omega$ if and only if $G$ is hyperlinear."
- **Thom**, arXiv:0810.2180, Introduction: "As a consequence, the maximal group $C^*$-algebra of such a group cannot have the local lifting property. To the best knowledge of the author, … no such group had been constructed before." So #3 is not new as a phenomenon (Thom, 2008). It is new only for a simple group, which is exactly Ozawa's wording.
- **Dadarlat**, arXiv:2007.12655v2, source of the introduction: "It is clear from definitions that MF $\Rightarrow$ weak quasidiagonality …". Before Prop. 3.19 (Ozawa–Thom), the text reads: "It shows that an infinite simple property (T) group $G$ is not weakly quasidiagonal." Prop. 3.19 itself: "If an infinite property $\mathrm{(T)}$ group $G$ is weakly quasidiagonal, then $G$ has an infinite residually finite quotient." The implication that follows from the definitions is the converse.

## 2. Proofs of the items proposed for the note

**2.1 Brown's form.**
- G is infinite and simple, so it is ICC (`infinite-simple-groups-are-icc`), and L(G) is a separable II_1 factor.
- G is hyperlinear (the note, l.150-152), so L(G) embeds in R^ω by Ozawa's Prop. 7.1.
- Put M = L(G)⊗̄R. It is a separable II_1 factor, and M⊗̄R ≅ L(G)⊗̄(R⊗̄R) ≅ M, so M is McDuff (McDuff's theorem: a separable II_1 factor N is McDuff iff N ≅ N⊗̄R).
- M embeds in R^ω. Compose L(G)⊗̄R → R^ω⊗̄R → (R⊗̄R)^ω ≅ R^ω, where the middle map sends (x_n)_ω ⊗ y to (x_n⊗y)_ω on the algebraic tensor product. That map is well defined because ‖x_n⊗y‖_2 = ‖x_n‖_2‖y‖_2. It is multiplicative and trace preserving, so it extends to the von Neumann tensor product.
- g ↦ λ_g⊗1 embeds G in U(M).

The earlier graph justification ("R^ω is McDuff") used the non-separable R^ω. Brown's McDuff factors are separable, and McDuff's theorem is a statement about separable factors. That text is repaired in this landing.

**2.2 The hyperfinite factor does not work.** Suppose ρ: G → U(R) were injective. By Kirchberg Cor. 1.2, (ii)⇒(i) holds in full generality, so G would have property (F). By Thm. 1.1, G would then be residually finite. An infinite simple group is not, so no such ρ exists (graph node `kazhdan-groups-in-hyperfinite-unitary-group-are-rf`). Robertson (as Brown recalls) excluded L(F_n)⊗̄R; by (ii)⇒(i), U(R) is excluded for every non-RF Kazhdan group. A witness for Brown's question must therefore be a non-hyperfinite McDuff factor such as L(G)⊗̄R.

**2.3 Factorization property and LLP.** G has (T) and is not residually finite, so by Kirchberg's Thm. 1.1 it lacks (F). By Ozawa's remark after Thm. 7.4, C*(G) does not have the LLP. Graph: `simple-kazhdan-lef-group-c-star-fails-llp`, PASS conditional on imports (`ex-review-groups-2026-09-12-part11.md` §11.3). This lane now verifies both imports from the sources above.

## 3. Manuscript proposal (RULES §6)

**(a) Current text, l.150-152:**
```latex
The regular permutation actions of these finite groups give sofic
models; their permutation matrices give hyperlinear models
\cite{Pestov}.
```

**Replacement, Option B (recommended):**
```latex
The regular permutation actions of these finite groups give sofic
models; their permutation matrices give hyperlinear models
\cite{Pestov}. So $L(G)$ embeds in $R^\omega$~\cite[Proposition~7.1]{Ozawa}.
Since $G$ is infinite and simple, its nontrivial conjugacy classes are
infinite, so $L(G)\mathbin{\bar\otimes}R$ is a McDuff factor. It embeds
in $R^\omega$, and its unitary group contains $G$. This is Brown's
formulation. Kirchberg proved that a Kazhdan group with the
factorization property is residually finite~\cite[Theorem~1.1]{Kirchberg}.
So $G$ does not have the factorization property, and $C^*(G)$ does not
have the local lifting property~\cite[p.~527]{Ozawa}.
```

**New bibitem**, placed alphabetically between `GM` and `MorseHedlund`:
```latex
\bibitem{Kirchberg}
E.~Kirchberg, \emph{Discrete groups with Kazhdan's property~$T$ and
factorization property are residually finite},
Math. Ann. \textbf{299} (1994), 551--563.
\doi{10.1007/BF01459798}.
```

**Option A (minimal: Brown only, no new citation):**
```latex
The regular permutation actions of these finite groups give sofic
models; their permutation matrices give hyperlinear models
\cite{Pestov}. So $L(G)$ embeds in $R^\omega$~\cite[Proposition~7.1]{Ozawa},
and $G$ lies in the unitary group of the McDuff factor
$L(G)\mathbin{\bar\otimes}R$ ($G$ is ICC), which also embeds in
$R^\omega$. This is Brown's formulation.
```

**Option C** is Option B plus one clause after "This is Brown's formulation.":
```latex
By Kirchberg's theorem $G$ embeds in the unitary group of $R$ itself
for no faithful representation~\cite[Corollary~1.2]{Kirchberg}.
```
This one needs the Kirchberg bibitem in any case.

**(b) Proof text.** The replacement above is the complete text. Each step is a standard fact: ICC gives a factor; L(G)⊗̄R is McDuff because R⊗̄R ≅ R; M ↪ R^ω gives M⊗̄R ↪ R^ω; and there are two cited theorems. None of it adds a lemma to the proof of Theorem 1.

**(c) Length change in the note:**
- Option A: +3 lines of text, no bibliography change.
- Option B: +8 lines of text, +5 lines of bibliography.
- Option C: +10 lines of text, +5 lines of bibliography.

**(d) Reader-facing trade-off:**
- Option A lets the reader check the claim that the note answers Brown's printed question, using one proposition from a paper the note already cites, with no new machinery.
- Option B also gives Ozawa's own reason for the question: an infinite simple Kazhdan hyperlinear group has a full C*-algebra without the local lifting property. It costs one new classical citation and changes nothing in the proof.
- Option C's clause tells the reader why Brown asked for a McDuff factor, but it is not needed for the answer.

My recommendation is B. Items #4–#8 give the reader facts that are routine or that need definitions the note does not carry. #9 belongs only in a closing questions paragraph.

**(e) Status:**
- NEW `brown-mcduff-witness-for-simple-kazhdan-lef-group` (established, unreviewed; queued for sk-referee-2), with route `brown-mcduff-witness-for-simple-kazhdan-lef-group-proof`.
- REPAIRED `simple-kazhdan-group-gives-property-t-factor-in-r-omega` and its route: the non-separable "R^ω is McDuff" justification is replaced by a pointer to the separable witness.
- REPAIRED `kirchberg-property-t-fp-implies-rf-citation`: DOI confirmed via Crossref, pages 551–563 from the PDF header, Thm. 1.1 and Cor. 1.2 quoted verbatim.
- EXISTING `simple-kazhdan-lef-group-c-star-fails-llp`: PASS conditional on imports; imports verified here.
- OPEN, unchanged: `directly-finite-subshift-el-n-reduced-cstar-is-mf`, `infinite-kazhdan-group-with-mf-reduced-cstar`.

## 4. What is left open

- **C*_r(G) MF.** Magee–de la Salle say the MF question is not known even for C*_r(SL_3(Z)). The firewalls on main: regular and permutation modules of the LEF models have norm-one outliers, and G has no nontrivial finite-dimensional unitary representation. An affirmative answer would be the first infinite Kazhdan group with an MF reduced algebra. It is famous-level, not for this note.
- **C*-simplicity of G.** Not settled here. Trivial amenable radical gives a unique trace, not simplicity, by Le Boudec's examples.
