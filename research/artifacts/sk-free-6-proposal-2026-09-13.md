# sk-free-6 proposal: G_X is boundedly but not uniformly simple (2026-09-13)

Lane sk-free-6 (free lane). Base text: main tip 0d44c399cf, `simple_kazhdan_sofic_group.tex` (rev4, c8b6021ca; md5 9144d8536cdca9073d50ffb64b826c00). Line numbers below refer to that file.

## (a) Current text and replacement
Current, l.293–299 (end of §2, the proof of Theorem 1):
```latex
$\prod_ae_{ij}(\tau_a)$, as $\sum_ae_a=1$ and $\sum_aD_\ell(e_a)=I$, so the
$e_{ij}(s)$ with $s\ne1$ also give expanders.\qed

% rev4.1 SLOT (gated on sk-verify-13 PASS of the LaTeX): every finite field,
% n>=3 variant of sk-general-statement (d7ef2a68fd).

\section{LEF groups}\label{sec:lef}
```
Proposed: insert after l.294 (after `\qed`), before the rev4.1 slot comment:
```latex
\begin{remark}
Every element of $G_X$ is a product of at most $78$ elementary matrices:
cut orbits into long Kakutani--Rokhlin towers, compress to each tower, and
correct at both ends, which is possible because half-line compressions of
elements of $G_X$ have Fredholm index $0$. So every conjugation-invariant
norm on $G_X$ is bounded. Still $G_X$ is not uniformly simple. Each
$T$-invariant probability measure $\mu$ gives a rank function
$\operatorname{rk}_\mu$ on $R$ with $\operatorname{rk}_\mu(e_V)=\mu(V)$~\cite{AraClaramunt},
and $g\mapsto\operatorname{rk}_\mu(g-I_3)$ is a conjugation-invariant length.
So writing $e_{12}(1)$ as a product of conjugates of $e_{12}(e_V)^{\pm1}$
takes at least $1/\inf_\mu\mu(V)$ factors, and towers show that
$2/\inf_\mu\mu(V)+2$ factors suffice.
\end{remark}
```
Bibitem (arXiv numbering verified on main by `cantor-z-crossed-product-embeds-in-continuous-factor`; journal data to be checked by sk-verify-6):
```latex
\bibitem{AraClaramunt}
P.~Ara and J.~Claramunt, \emph{Sylvester matrix rank functions on crossed
products}, Ergodic Theory Dynam. Systems \textbf{40} (2020), 2913--2946.
\arxiv{1902.06476}.
```
The document needs a `remark` environment. If it has none, use `\begin{theorem}`-style `\newtheorem{remark}[theorem]{Remark}`, or write the paragraph without an environment.

## (b) Proof text
The remark carries a one-sentence sketch of each direction. The full proofs are on main:
- `research/artifacts/sk-free-6-normal-generation-2026-09-13-part3.md`: bounded elementary generation, 78 elementary matrices.
- `research/artifacts/sk-free-6-normal-generation-2026-09-13-part1.md` §§1–2: rank lengths, and between 1/inf μ(V) and 2⌊1/inf μ(V)⌋ + 2 factors.
- The note keeps only the statement plus the one-line mechanism, per the SHORT rule.

## (c) Length
+12 text lines and +4 bibliography lines. A compressed alternative (+4 lines) keeps only the last two sentences: the rank lengths and non-uniform simplicity, with the lower bound only.

## (d) Trade-off (reader merit)
It says something new about the note's group at small cost: G_X is as bounded as SL_3(Z) (every conjugation-invariant norm bounded), yet not uniformly simple. The measures of X, invisible to the characters of G_X, control normal generation. The reader must trust two unreviewed proofs, gated below.

## (e) Status
| node | status |
|---|---|
| `subshift-el-groups-boundedly-elementary-generated` (+ `-proof`) | established, UNREVIEWED, queued with sk-verify-13 (priority) |
| `subshift-el-groups-have-bounded-conjugation-invariant-norms` (+ `subshift-el-groups-bounded-norms-proof`) | established, UNREVIEWED |
| `subshift-el-rank-lengths-force-non-uniform-simplicity` (+ `-proof`) | established, UNREVIEWED |
| `transvection-normal-generation-recovers-invariant-measures` (+ `-proof`) | established, UNREVIEWED |
| `subshift-el-root-elements-boundedly-normally-generated` (+ `-proof`) | established, UNREVIEWED |
| `finite-models-transvection-covering-converges-to-measure` (+ `-proof`) | established, UNREVIEWED |

Gate: include only after sk-verify-13 PASSes the bounded elementary generation theorem and the rank-length claim. If only the rank-length claim passes, use the compressed alternative.
