# sk-free-8 proposal: non-uniform exponential growth of G_X (2026-09-13)

Status of the mathematics: established by sk-free-8, UNREVIEWED (queued with sk-verify-13). Adopt only after a PASS.
- Nodes: `simple-kazhdan-lef-group-of-non-uniform-exponential-growth`, `substitution-subshift-elementary-groups-non-uniform-growth`, `self-similar-ring-elementary-groups-non-uniform-growth`, `el-small-ball-generating-sets-from-grigorchuk-levels`, `constant-length-substitution-tower-partition`, `mosse-bilateral-recognizability`.
- Artifacts: `research/artifacts/sk-free-8-nonuniform-growth-2026-09-13-part1.md` and `-part2.md`.

## (a) Current text (landed rev3, main 9047d0d3c9, md5 274f1936…, l.406–415)
```latex
\section{Questions}

A finitely presented LEF group is residually finite~\cite{VershikGordon},
and the infinite simple group $G_X$ is not, so $G_X$ is not finitely
presented. Finitely presented infinite simple groups with
property~\textup{(T)} exist~\cite{CapraceRemy}. Is there one that is
sofic, or at least hyperlinear? A positive answer would also answer Open
problem~6.1 of Alekseev and Thom~\cite{AlekseevThom}, which asks for
finitely presented sofic groups with property~\textup{(T)} that are not
residually finite.
```

## Replacement: insert a remark before `\section{Questions}` (after l.404)
```latex
\begin{remark}
If $X$ is the Thue--Morse subshift, then $X=V\sqcup TV$ for the clopen
image $V$ of the substitution, and $(V,T^2)\cong(X,T)$~\cite{Mosse96}, so
$R_X\cong M_2(R_X)$ and $G_X\cong\EL_{3\cdot2^n}(R_X)$ for every $n$.
Sauer and Schesler's generating sets built from the Grigorchuk group act on
$3\cdot2^n$ coordinates~\cite{SauerSchesler}. With transvections carrying
the ring generators, their ball of radius $\ell\le2^{n/2}/3$ has at most
$\exp(C\ell^\beta)$ elements, $\beta<1$, so $G_X$ has non-uniform
exponential growth. It is thus a simple Kazhdan LEF group of non-uniform
exponential growth, cf.\ de la Harpe's question~\cite[\S7]{dlHarpeUEG}.
\end{remark}
```
Bibliography (+10 lines):
```latex
\bibitem{Mosse96}
B.~Moss\'e, \emph{Reconnaissabilit\'e des substitutions et complexit\'e des
suites automatiques}, Bull. Soc. Math. France \textbf{124} (1996), 329--346.
\bibitem{SauerSchesler}
R.~Sauer and E.~Schesler, \emph{An acylindrically hyperbolic group of
non-uniform exponential growth}, arXiv:2606.15945, 2026.
\bibitem{dlHarpeUEG}
P.~de la Harpe, \emph{Uniform growth in groups of exponential growth},
Geom. Dedicata \textbf{95} (2002), 1--17.
```
(The de la Harpe page range is recalled; verify through Crossref before adopting.)

## (b) Proof text
The remark carries the whole proof by citation. The two in-house steps are routine for the reader:
1. **Matrix units.** e_V, e_{TV}, ue_V, e_Vu^{−1}, with corner LC(V)⋊_{T²}Z.
2. **Transfer of Sauer–Schesler's counting.** Types 2 and 4 of their generating sets become Sym(3) and the ring-coefficient transvections. The commuting-supports lemma holds verbatim, and at each point of an inverted orbit the type-4 factor is e_{(x,2),(x,3)}(r) with r in the F_2-span of the ring generators.

A referee may ask for step 2 in print. That is 20 lines, too many for the note; Cairn holds it.

## (c) Length
+10 text lines, +10 bibliography lines (about +0.3 pages).

## (d) Reader-facing trade-off
Stronger: it adds a striking and checkable property of one explicit G_X. But the reader must trust a transfer of a 2026 preprint's counting argument that the note does not print. So it is a remark, not a theorem.

## (e) Recommendation
Adopt only after the verifier (sk-verify-13/14) PASSes both `el-small-ball-generating-sets-from-grigorchuk-levels` and `substitution-subshift-elementary-groups-non-uniform-growth`.

Novelty caution: Hull (arXiv:1308.4345, Theorem 8.6, quoted via a web search) gives infinite quotients of acylindrically hyperbolic groups in which elements are conjugate iff they have the same order. Such a quotient of Sauer–Schesler's group may already be a simple Kazhdan group of non-uniform exponential growth. So the last sentence of the remark should stress LEF: "so $G_X$ is a simple Kazhdan group of non-uniform exponential growth that is LEF, cf. …". Main's budget call.
