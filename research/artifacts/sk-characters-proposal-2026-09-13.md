# sk-characters: manuscript proposal (RULES §6)

2026-09-13, lane sk-characters. Line numbers refer to `sk/manuscript-disk-1646.tex` (md5 7b3dc4ec…).

## Findings
- **Proved, unreviewed.** Theorem A (`subshift-elementary-root-continuous-characters-are-trivial`): a character of `G_X` that tends to 1 on the root elements `e_12(e_P)`, as `sup_μ μ(P) → 0`, is constant. The proof is one page (`research/artifacts/sk-characters-root-continuity-2026-09-13.md` §2) and rests on Carderi–Thom Lemma 1.4 and Gluck's character bound.
  - So `G_X` has no measure-type characters.
  - This contrasts with the derived topological full group of the same system, whose characters `γ ↦ ∏ μ_i(Fix γ)` are classified by Dudko–Medynets (arXiv:2602.16885).
- **Open.** Full character rigidity (every extreme character is `1` or `δ_e`), and with it IRS rigidity (`subshift-elementary-groups-are-character-rigid`). It is equivalent to automatic continuity of non-regular extreme characters, which no route has reached yet.

## Proposal A (recommended): no change to the note
- (a) Current text: l.1–340 unchanged.
- (b) Proof text: none.
- (c) Length change: 0 lines.
- (d) Trade-off: the note's theorem and corollary need nothing about characters. Theorem A is a partial result with a one-page proof built on imported character bounds, so it would add length and machinery without strengthening the headline.
- (e) Status: the nodes above; Theorem A is queued for sk-verify-3.

## Proposal B (only if the note gains a closing paragraph of questions)
- (a) Insert after l.262 (end of the corollary's proof), as its own short paragraph. The replacement LaTeX, verbatim:

```latex
\subsection*{A question}
Are $1$ and the regular character the only extreme characters of $G_X$?
For the commutator subgroup of the topological full group of $X$,
Dudko and Medynets found the further characters
$\gamma\mapsto\prod_{i=1}^k\mu_i(\operatorname{Fix}\gamma)$, one for each
finite list of ergodic invariant measures~\cite{DudkoMedynets}.
```

  plus a bibitem:

```latex
\bibitem{DudkoMedynets}
A.~Dudko and C.~Medynets, \emph{Characters and $\mathrm{II}_1$-factor
representations of full groups of Cantor minimal systems},
\href{https://arxiv.org/abs/2602.16885}{arXiv:2602.16885} (2026).
```

- (b) Proof text: none. It is a question, and the cited statement is Dudko–Medynets Theorem 1.1, read from the arXiv PDF on 2026-09-13. Theorem A is deliberately not stated: stating it would need the one-page proof.
- (c) Length change: +6 lines of text and +4 lines of bibliography.
- (d) Trade-off: the reader gets a sharp question contrasting the amenable simple group and the Kazhdan simple group of the same subshift. It costs about 10 lines in a note whose value is its shortness, and adds no theorem.
- (e) Status: the Dudko–Medynets title, authors and theorem were checked against the arXiv v1 PDF (18 Feb 2026). No journal version was found.

## Recommendation
Proposal A. Keep Proposal B available for sk-open-5 / main if a questions paragraph is adopted. If full character rigidity is later proved, the corollary "L(G_X) is the unique II_1 factor representation, and G_X has no nontrivial invariant random subgroups" would earn one sentence.
