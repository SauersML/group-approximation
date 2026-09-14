# sk-referee-significance: hostile senior referee report on significance, framing and length (2026-09-13)

Lane sk-referee-significance (wave 10, ROSTER-H). I refereed as for the Annals, Inventiones or JAMS.
- **Subject:** `simple_kazhdan_sofic_group.tex` rev3 on main (9047d0d3c9, md5 274f19367f7f706b05c017af721c3884, 618 lines, 7 pp), plus main's rev4 plan (decision log items 71, 79 and 83 in `wip/simple-kazhdan-note/decisions.md`). Line numbers are those of the landed rev3.
- **Read for context:**
  - rev3 referee reports a and b;
  - sk-panel-referee-1/2/3 part 1;
  - sk-novelty-prior-art part 1 and sk-lit-novelty-2;
  - sk-lit-background part 2;
  - the proposals of sk-intro-writer, sk-strong-8, sk-sl3z-bandwidth, sk-characters-rigidity-b, sk-el2 and sk-el2-fq;
  - the nodes `countable-group-embeds-in-fg-simple-kazhdan-group`, `topological-full-group-embeds-in-subshift-elementary-group`, `subshift-elementary-groups-are-character-rigid`, `lef-elementary-groups-force-lef-rings` and `simple-ring-with-matrix-units-el-lef-iff-matricial`.
- **No mathematics claimed; no Cairn claim nodes touched.** Proposed text obeys RULES §6: key point first, "so/then", normal word order.
- **The lineage is left as is:** Brown 2001 → Ozawa 2003 → Pestov 2008, and the credit paragraph is user-decided. Items below only move lineage sentences or add sourced facts around them.

## 0. Verdict
- **Correctness.** Both rev3 referees re-derived everything and found no error; this report does not redo that.
- **Significance.** The note answers a well-known printed question.
  - Ozawa (math/0306067): "It is unknown whether there exists a simple property (T) group Γ which is hyperlinear."
  - Pestov, Open question 9.1: "Let G be an infinite simple group with Kazhdan's property (T). Can it be hyperlinear (sofic)?"
  - Pestov–Kwiatkowska (arXiv v4 p. 28): "it remains in particular unknown whether finitely generated simple Kazhdan groups can be hyperlinear/sofic."

  The answer comes from one idea that three known theorems then carry. That is exactly what a top journal accepts as a short paper, provided the paper says the idea on page 1 and stays short.
- **What a hostile referee attacks in rev3 and the rev4 plan:**
  1. **Page 1 never states the idea.** The method paragraph (l.71–87) is a list of credits. A reader cannot tell, before §1, why EL_3 of this ring should be both Kazhdan and LEF (S1).
  2. **The most memorable fact about these groups is absent.** The amenable simple group of the same Cantor system sits inside G_X (S2).
  3. **The plan grows by accretion.** rev3 is 7 pp. Adding everything in item 71, P1, characters, n = 2 and all F_q gives about 9 pp. Every secondary theorem then dilutes the answer. Priorities and cuts are in S3 and §2.
  4. **Wording risks in the new material** (S4).
- **Strongest honest framing.** For every infinite minimal subshift X, EL_3 of the F_2 crossed product ring is an infinite simple Kazhdan group and a limit of the finite simple groups SL_{3N}(F_2). So infinite simple Kazhdan groups can be sofic, even LEF. These groups arise from the same dynamical systems whose topological full groups gave the first finitely generated infinite simple amenable groups. Conversely, the subgroups of such groups are exactly the LEF groups.
  - Do NOT attach novelty to simplicity (Stepanov Thm 4.4 covers it) or to simple Kazhdan hosts without LEF. `countable-group-embeds-in-fg-simple-kazhdan-group` on main gets these from Schupp plus small cancellation over hyperbolic Kazhdan groups and claims no novelty.
  - The novelty is the combination with LEF. rev3 l.269–274 ("The next corollary adds property (T) …") is correct as written; keep it.

## 1. Ranked items

### S1 (MUST, framing, +2 lines): state the idea on page 1
Replace rev3 l.71–76, from "Property~\textup{(T)}, introduced by" through "construction~\cite{Kassabov}.", with:
```latex
The ring $\LC(X,\F_2)\rtimes_T\Z$ is finitely generated, so $G_X$ has
property~\textup{(T)}, introduced by Kazhdan~\cite{Kazhdan}, by the theorem
of Ershov and Jaikin-Zapirain~\cite{EJZ}. Periodic points give the ring
exact finite models in the matrix algebras $M_N(\F_2)$, as in the proof by
Grigorchuk and Medynets that topological full groups of minimal Cantor
systems are LEF~\cite[Theorem~2.6]{GM}. So $G_X$ is a limit of the groups
$\SL_{3N}(\F_2)$, which form expanders as in Kassabov's
construction~\cite{Kassabov}.
```
- **Reason:** a reader outside the field gets the whole mechanism in the first screen (finitely generated ring ⇒ (T); matrix models ⇒ finite simple limits). Every credit of the old sentences survives.
- **Check:** "exact finite models" is what φ_ℓ gives in §1 (additive and multiplicative on fixed elements for large ℓ, nonzero on nonzero elements, rev3 l.153–160). No new claim.
- **In rev4:** apply the same change to sk-intro-writer's method paragraph, which keeps rev3's credit sentences verbatim.

### S2 (HIGH, framing, +1 clause and +2 proof lines; gated on a PASS): the amenable twin inside G_X
sk-intro-writer's sentence reads: "The derived subgroups of these topological full groups are infinite, finitely generated and simple for minimal subshifts~\cite{Matui}, but they are amenable~\cite{JuschenkoMonod}, so they do not have property~\textup{(T)}." Replace it with:
```latex
The derived subgroup of the topological full group of $X$ is infinite,
finitely generated and simple~\cite{Matui}, and it is
amenable~\cite{JuschenkoMonod}. It is also a subgroup of $G_X$.
```
Append to the proof paragraph that carries the Whitehead identities (rev3 l.332–345):
```latex
For $g$ in the topological full group of $X$ put
$w_g=\sum_nu^ne_{\{x:\,gx=T^nx\}}$. Then $w_ge_Vw_g^{-1}=e_{gV}$ and
$g\mapsto w_g$ is an injective homomorphism into $\GL_1(R)$, so
$g\mapsto\operatorname{diag}(w_g,1,1)$ embeds the derived subgroup in $G_X$.
```
- **Reason:** the reader sees one Cantor system giving an amenable simple group and, inside a matrix group over its ring, a Kazhdan simple group. That picture is what people will remember and quote.
- **Check done here:**
  - w_g e_V = Σ_n u^n e_{U_n∩V} = Σ_n e_{T^n(U_n∩V)} u^n and e_{gV} w_g = Σ_n e_{gV∩T^nU_n} u^n, with T^n(U_n∩V) = gV ∩ T^nU_n. The conventions are rev3 l.103–109.
  - Multiplicativity follows from gh x = T^{n+m}x when hx = T^m x ∈ U_n(g). Injectivity: w_g = 1 forces U_0 = X.
  - The char-2 identity diag(a,a^{-1},1)diag(b,b^{-1},1)diag((ba)^{-1},ba,1) = diag([a,b],1,1) is referee (a)'s checked l.338–341.
- **Status:** the node `topological-full-group-embeds-in-subshift-elementary-group` (A) is unreviewed. It is queued with sk-verify-13 by this lane.

### S3 (HIGH, structure and budget): what goes in rev4, in order
The target is 7 pp and at most 8, measured in typeset pages after the typesetting patch. Estimates are in source lines against rev3's 618.

| tier | item | cost | verdict and reader-merit reason |
|---|---|---|---|
| 1 | intro (sk-intro-writer + S1 + S2 + referee fixes) | +30 text, +45 bibliography | IN. Why the question matters, and the idea, on page 1. |
| 1 | Theorem 2, the engine (item 71a) | about +9, replacing the §2 substitution list | IN. One proof for both families, and it removes the "word for word" claim a referee attacks. |
| 1 | LEF iff subgroup of a simple Kazhdan limit of finite simple expanders (71c) | about +5 over rev3 §2 | IN after PASS. It is the title's theorem in general. |
| 1 | one host for every recursively presented f.g. LEF group, plus no decidable host (71d) | ≤ 8 | IN after PASS. It subsumes rev3's "every f.g. linear group" corollary (f.g. linear groups are RF with solvable word problem, so recursively presented), so the abstract states the stronger form. |
| 1 | Brown's formulation, Questions + sofic-host question | as rev3 + 2 | IN. |
| 2 | P1, separable factors (item 83) | +10, +4 bibliography | IN after sk-verify-10 PASS. Put it in §3 replacing "so there are continuum many pairwise nonisomorphic groups $G_X$": countably many X per factor class subsumes countably many per group class. Answers Ozawa's printed wish inside the Connes-embeddable world. |
| 2 | SL_3(Z) no-distortion obstruction | ≤ 6 (the trimmed LaTeX in its proposal is 17 source lines; cut the CFKP sentence and compress) | IN after PASS. It answers the reader's first question about Corollary 2: why not use G_X itself? |
| 2 | rank-3 converse sentence (`simple-ring-with-matrix-units-el-lef-iff-matricial`, sk-verify-8 PASS with N4) | +2 | OPTIONAL. It says the matricial ring is necessary, not a trick. Print only the PASSed statement, with simplicity and 2×2 matrix units. |
| 3 | character rigidity (two PASSes: sk-characters-rigidity-a, sk-verify-8 part2) | +45, +3 bibliography | OUT of this note; write it as a separate short paper. It is a new theorem with its own audience (Bekka, Peterson–Thom, Dudko–Medynets), and it deserves a statement for the whole Theorem 2 family with its IRS and trace corollaries. In this note it would be the longest section and would not strengthen the answer to the question. |
| 3 | EL_2 (n ≥ 2) | +33, +5 bibliography | OUT. Theorem 1 with n ≥ 3 already answers every question. The rank-2 case asks the reader to trust a different (T) criterion (EJZK strong grading). Keep it in Cairn. |
| 3 | every F_q (R3) | +12 | OUT. F_2 is the natural case, and the remark imports quasisimplicity and a different root choice (decision 23's firewall) for generality nobody uses here. |

Rough total, tiers 1 and 2: about +110 source lines, including about 50 of bibliography, so about 8 pp. Cut K1 and the tier-3 exclusions keep it there. Tier 3 in would push it to about 9.5 pp.

### S4 (HIGH, wording guards for rev4's new material)
- **P1.** Print only the counting statement: each separable II_1 factor contains G_X in its unitary group for only countably many X, so the factors L(G_X) fall into continuum many isomorphism classes.
  - Never print "Connes's rigidity conjecture holds for this family modulo countable sets" (sk-strong-7's report). The conjecture is about isomorphism of group factors versus groups, and "modulo countable sets" is not a statement a reader can check.
  - Credit Nicoara–Popa–Sasyk for "no separable universal R^ω-embeddable factor" in the form sk-verify-10 confirms at source. Credit Ozawa 2004 Thm 2 for the argument.
- **71(d).** Print exactly the PASSed statement of sk-universal-lef-host-b Theorem C, with "recursively presented" kept. The no-decidable-host clause must name what is decidable: host word problem versus containing all f.g. LEF groups with solvable word problem. Wait for sk-verify-11.
- **71(c).** Say "limit of finite simple groups $\SL_N(\F_2)$ in the space of marked groups" only if the models on F_2^{Q_n} generate the full matrix algebra, so that EL_3 of it is SL_{3·2^{|Q_n|}}(F_2), on a FIXED generating set of the host. That is sk-verify-9's item 2.
- **Theorem 2.** "Matricial" must be defined in the statement: exact finite models in matrix algebras over F_2, in the sense of S1. Do not use "matricial" without that definition (RULES F1).
- **Novelty.** Never write "the first simple Kazhdan host" or "the first infinite simple Kazhdan group containing a given group". Write "adds property (T)" to Kionke–Schesler's LEF host, as rev3 does.
- **Title.** Keep it (decision 41, Variant B). It states the strongest property; "sofic" and "hyperlinear" are in the abstract and keywords.

### S5 (MEDIUM, what an expert expects and does not find in rev3)
- **E1. Known simple Kazhdan groups, and why they did not answer.** rev3 names Caprace–Rémy only in Questions.
  - sk-intro-writer adds Gromov's quotients of hyperbolic Kazhdan groups and Caprace–Rémy "first finitely presented". ADOPT.
  - Carry sk-lit-background V1's caveat: "non-elementary" is implicit; do not add an Ol'shanskii credit unchecked.
- **E2. Alekseev–Thom's list** (+1 line, VERIFY-PENDING at source, queued with sk-verify-6). Their §5 names Thom's group among the known sofic Kazhdan groups that are not residually finite (sk-novelty part 1, R: P). At the end of the Q1 paragraph:
```latex
The groups $G_X$ are sofic Kazhdan groups that are not residually finite,
as is Thom's group, but they are also simple.
```
  Reason: it situates G_X in the most recent printed discussion of exactly this class, and shows why "finitely presented" is what 6.1 still asks. If the §5 check fails, drop E2.
- **E3. Why the question matters.** Ozawa's LLP remark and Pestov–Kwiatkowska's open-status sentence are both in sk-intro-writer. ADOPT. Do not add an unsourced "natural candidates for non-hyperlinear groups" sentence (panel-referee-3 B5).

### S6 (MEDIUM, opening, 0 net lines): question, answer, then background
With sk-intro-writer's introduction, move "The groups below answer all three forms positively." up. The opening paragraph ends there, and the theorem follows within the first 10 lines of page 1:
```latex
Can an infinite simple group with property~\textup{(T)} be hyperlinear?
Brown asked this in 2001 as a question about embeddings into unitary
groups of McDuff factors that embed in an ultrapower $\mathcal R^\omega$
of the hyperfinite $\mathrm{II}_1$ factor~\cite[\S11, Question~7]{Brown}.
Ozawa stated the hyperlinear form in 2003, noting that the full
$C^*$-algebra of such a group cannot have the local lifting
property~\cite[p.~527]{Ozawa}, and Pestov's Open question~9.1 adds the
sofic form~\cite{Pestov}. The groups below answer all three forms
positively.
```
- The theorem follows immediately.
- The background sentences (Rădulescu; Gromov/Weiss; known simple Kazhdan groups; Thom; Pestov–Kwiatkowska) form the first paragraph after the theorem, unchanged apart from their position.
- Reason: the reader sees question and answer before background. The lineage wording is unchanged.

### S7 (LOW, abstract for rev4; the lineage sentence verbatim)
Variant with 71(c) and 71(d) PASSed:
```latex
\begin{abstract}
For every infinite minimal subshift $X$, the group
$G_X=\EL_3(\LC(X,\F_2)\rtimes\Z)$ is an infinite, finitely generated,
simple group with property~\textup{(T)}. It is a limit of finite simple
groups $\SL_{3N}(\F_2)$ in the space of marked groups, and their Cayley
graphs form a family of expanders. So $G_X$ is locally embeddable into
finite groups, sofic and hyperlinear. This answers the question of Brown
and Ozawa whether an infinite simple Kazhdan group can be hyperlinear,
and Pestov's sofic version of it. A finitely generated group is locally
embeddable into finite groups if and only if it is a subgroup of an
infinite finitely generated simple Kazhdan group that is a limit of
finite simple groups, and one such group contains every recursively
presented finitely generated group with this property.
\end{abstract}
```
- **Changes against rev3 l.29–42:**
  - the host is "a limit of finite simple groups" (71c);
  - "every finitely generated linear group" becomes "every recursively presented finitely generated group with this property" (71d);
  - the Turing-degree sentence moves to the body (K2).
- **Reason:** the abstract carries the answer and the characterization. The Turing statement is a corollary readers find in the text.
- **Fallback without 71(c)/(d):** keep rev3's last two sentences.

## 2. Cut list
- **K1 (−5 lines), §3 Sturmian paragraph, rev3 l.382–399 → 13 lines.** Same steps, and every inference referee (a) checked survives:
```latex
For irrational $\alpha\in(0,1)$ let $X_\alpha$ be the infinite minimal
Sturmian subshift, the closure of the codings $c(\theta)$,
$\theta\in[0,1)$, with
$c(\theta)_t=\lfloor\theta+(t+1)\alpha\rfloor-\lfloor\theta+t\alpha\rfloor$,
which is $1$ exactly for $\theta$ in the arc $[-(t+1)\alpha,-t\alpha)$
modulo $1$~\cite{MorseHedlund,Hedlund44},~\cite[Chapter~2]{Lothaire}.
Passing to the closure adds no words, so the words of length $m$ of
$X_\alpha$ are the constant values of $c(\theta)_{[0,m)}$ on the arcs
between the distinct points $-j\alpha\bmod1$, $0\le j\le m$, and $\alpha$
computes $L(X_\alpha)$. Such a word has $\lfloor\theta+m\alpha\rfloor$
ones, within $1$ of $m\alpha$, so $L(X_\alpha)$ computes $\alpha$. Every
set $S\subseteq\mathbb N$ has the degree of
$[0;1+\chi_S(0),1+\chi_S(1),\dots]$, since each digit is decided by one
strict comparison with a rational computed from the earlier digits. There
are continuum many degrees, and the degree of the word problem is an
isomorphism invariant.
```
- **K2 (−1 line):** the Turing-degree sentence leaves the abstract (S7).
- **K3 (−45, −33, −12, avoided):** the tier-3 exclusions of S3.
- **K4 (≈ −9, by replacement):** Theorem 2 replaces the §2 substitution paragraph (rev3 l.307–313) and the separate §2 simplicity claim.
- **Not cut, and why:**
  - Brown's formulation (decision 17; the claim "answers Brown" needs it);
  - the Stepanov sentence with Clark–Edie-Michell (a credit obligation, panel-referee-1 blocker);
  - the GM word-problem remark (credit);
  - the credit batch (user order).

## 3. Explicitly not recommended
- Any MF, weak quasidiagonality or strong-convergence remark about C*(G_X) or C*_r(G_X). sk-novelty part 1 §3 records a printed-arrow tension with Dadarlat's "MF ⇒ weak quasidiagonality", and LEF does not give norm convergence (sk-cstar-mf firewall). Decision 18 keeps MF out.
- "Connes's rigidity conjecture … modulo countable sets" (S4).
- A novelty claim on simplicity, or on simple Kazhdan hosts without LEF (§0).
- Characters, n = 2 and F_q in this note (S3).
- The items panel-referee-3 §6 already rejected: explicit Kazhdan constant, K-theory, centre formula, torsion generators, LEF growth, hypothesis sharpness, subsystem sandwich, Z² SFT question.

## 4. Status
- No claims. Two queue lines appended:
  - `$SK/queue/sk-verify-13.txt`: `topological-full-group-embeds-in-subshift-elementary-group` (S2's dependency);
  - `$SK/queue/sk-verify-6.txt`: the Alekseev–Thom §5 quote (E2).
- The verbatim LaTeX blocks above were not compiled. They use only macros and bibitems present in rev3 or sk-intro-writer; S2 needs `JuschenkoMonod`, which sk-intro-writer already adds.
