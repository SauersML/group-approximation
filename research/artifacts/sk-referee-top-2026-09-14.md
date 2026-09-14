# sk-referee-top: hostile top-journal referee report on rev4.5

Lane sk-referee-top, 2026-09-14. Subject: `simple_kazhdan_sofic_group.tex` rev4.5 (8b36733d78, md5 29d63f7944bccccbf9a91b0b2714c0b4, 775 lines, 8 pp). The harness refused the lane's own report file, so main lands the report from the lane's final message, unchanged in content.

Earlier reports read first: sk-referee-significance, sk-rev44-referee, sk-perfect-a/b/c/d, sk-prior-art-2/3, sk-verify-10, sk-answered-questions part 2. Items marked NEW appear in none of them.

## Verdict: MAJOR REVISION, presentation only. No mathematical error or gap.

**Correctness.** Re-derived by hand, independently of the earlier audits:
- **Theorem 2:** both directions of convergence (l.211–235). One step is used without being stated: φ_k(0) = 0.
- **Simplicity:** the small clopen sets, the matrix units ε_ab, H_V ≤ G, and the ideal J.
- **Periodic models** (l.249–271).
- **Neumann–Neumann level isolation:** distinct powers of 2 have distinct differences, all below a quarter of the modulus.
- **Half-line models** κ, θ, ζ (l.423–438).
- **Whitehead product** (l.400–402).

**Overclaiming: none.** Each claim checked against the printed question:
- **Brown**, arXiv:math/0111286v1 §11 Q7, p. 33: "Can an infinite, simple, discrete group with Kazdan's property T be embed into the unitary group of an R^ω-embeddable McDuff factor?" Lines 275–284 answer it.
- **Ozawa**, math/0306067v2 p. 26: "It is unknown whether there exists a simple property (T) group Γ which is hyperlinear." The paper answers it as an existence statement.
- **Pestov**, Open question 9.1 (v8 p. 21): "Let G be an infinite simple group with Kazhdan's property (T). Can it be hyperlinear (sofic)?" Answered.
- **The abstract.** For countable groups Brown's form is equivalent to hyperlinearity, so "the question of Brown and Ozawa whether … can be hyperlinear" is fair.
- **Pestov–Kwiatkowska.** The "hope" sentence at l.99–102 matches v4 p. 28: "…is a bit diminished now, but surely not gone, as it remains in particular unknown…".

**Novelty.** Within sk-prior-art-2's search bound, no earlier group is simple, Kazhdan and LEF at once. Each property separately is already credited: Coulon–Fournier-Facio, Kionke–Schesler, Thom, Grigorchuk–Medynets, Matui, Stepanov.

**Editorial risk.** The first objection will be that this combines known theorems (Ershov–Jaikin-Zapirain, periodic models, Kassabov, Matui/Stepanov). The answer is the unification: one ring gives property (T) because it is finitely generated, and LEF because it has matrix models. Corollary 3 is also a genuine "if and only if". Page 1 already shows the mechanism; what remains is R1, R2 and S1.

## REQUIRED

**R1 (NEW), abstract ambiguity, 0 lines.** At l.42–43 the phrase "with this property" follows the solvable-word-problem sentence, so it can be read as "solvable word problem". That reading makes a false claim about LEF hosts.
- OLD: `One such group contains every recursively presented finitely generated group with this property.`
- NEW: `One such group contains every recursively presented finitely generated group that is locally embeddable into finite groups.`

**R2 (NEW), answer the opening question on page 1, +3 lines.** Lines 54–55 claim "all three forms", but Brown's form is only verified in §2 (l.274–284).
- Insert after l.71: `In Brown's form: $G_X$ is infinite and simple, so $L(G_X)$ is a $\mathrm{II}_1$ factor, and $G_X$ lies in the unitary group of the McDuff factor $L(G_X)\mathbin{\bar\otimes}\mathcal R$, which embeds in $\mathcal R^\omega$ (Section~\ref{sec:main}).`
- At l.283, after "embeds in $\mathcal R^\omega$", add: `, as $\mathcal R^\omega\mathbin{\bar\otimes}\mathcal R$ embeds in $(\mathcal R\mathbin{\bar\otimes}\mathcal R)^\omega\cong\mathcal R^\omega$,`

**R3 (NEW), before submission, 0 lines.** The novelty check behind "answers" rests on web searches, arXiv e-prints and Alekseev–Thom §5. MathSciNet, zbMATH and Russian sources were never searched. Before submitting:
- search MathSciNet and zbMATH for simple AND "property (T)" AND (sofic OR hyperlinear OR LEF);
- scan the papers citing Ershov–Jaikin-Zapirain 2010 and Grigorchuk–Medynets 2014.

## SUGGESTED (ranked)

**S1 (NEW), lead the abstract with the finding, +1 line.** At l.30, before "For every infinite minimal subshift $X$, the group", add: `Infinite simple groups with property~\textup{(T)} can be limits of finite simple groups.`

**S2 (NEW), definitions for a general reader, +5 lines.** The paper uses marked-group convergence, expanders, sofic and hyperlinear without defining them; only LEF is defined. After l.75 add:
`Groups marked by $k$ generators converge if every word is eventually trivial or eventually nontrivial, and a family of expanders is a sequence of finite graphs of bounded degree, with sizes tending to infinity and Cheeger constants bounded below. Sofic and hyperlinear groups are defined by approximately multiplicative maps into finite symmetric groups with the normalized Hamming distance, and into unitary groups with the normalized Hilbert--Schmidt distance, that keep nontrivial elements uniformly far from~$1$~\cite{Pestov}.`

**S3 (NEW), roadmap for the 58-line simplicity proof, +2 lines.** At l.151 add: `We show that $K$ contains $e_{pq}(e_V)$ for some nonempty clopen set $V$, and then that the ideal $J$ of those $r$ with $e_{pq}(r)\in K$ for all $p\ne q$ is $R$.`

**S4 (NEW), the corollaries are impact, not clutter.** Corollary 3 is the "if and only if", Corollary 4 the universal host, and Corollary 5 gives continuum many G_X, none embedding in another. The most expensive passage is the solvable-word-problem proof (l.412–458, about 47 lines). Keep it, but put `\subsection*{Solvable word problem}` before l.412 so readers can skip it.

**S5 (NEW), 0 net lines.** Move the Stepanov/ClarkEdie sentence (l.89–92) to after l.208, so page 1 carries one mechanism per property.

**S6 (NEW), −2 lines.** Cut the n ≥ 3 sentence at l.69–71 from Theorem 1; Theorem 2 already covers it (l.116–117).

**S7 (NEW), 0 lines.** At l.223, "for large $k$" → `for large $k$, where $\varphi_k(0)=0$ by additivity`.

## Already settled elsewhere, not repeated
- page-1 mechanism;
- question → answer → background order;
- Coulon–Fournier-Facio, Neumann–Neumann and Darbinyan credits;
- notation renames;
- Stepanov wording;
- sk-rev44-referee U1–U4.

## Main's disposition (decision 167)
- R1, R2, S1–S7 ADOPTED for the rev5 editor.
- R3 launched as sk-novelty-db.
