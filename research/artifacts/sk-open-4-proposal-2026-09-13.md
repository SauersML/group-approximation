# sk-open-4 proposal: what the dynamics lens gives the note

Lane sk-open-4, 2026-09-13. Line numbers refer to `sk/manuscript-disk-1646.tex`. The mathematics is in
`sk-open-4-dictionary-2026-09-13-part1.md` and `-part2.md`.

## Verdict
**No change to the main text (0 lines).** The note proves existence. None of the dictionary rows below strengthens Theorem 1 (l.44-53) or the corollary (l.231-235), and none answers a published question. Each would add length or citations the reader does not need. There is one optional candidate for a closing "Questions" paragraph, if the note gets one (sk-open-5's lane).

## What was found (Cairn, unreviewed unless marked)
| row | statement | node |
|---|---|---|
| K | For minimal (X,T): `K_n(LC(X,F_q)⋊Z) ≅ (K^0(X,T)⊗K_n(F_q)) ⊕ K_{n−1}(F_q)`, n ≥ 1. Over F_2: K_1 = Z, K_2 = 0, K_3 = K^0/3 | `minimal-cantor-crossed-product-k-theory-formula` |
| I | Over F_2 the half-orbit Fredholm index is K_1(R_X) ≅ Z; on [[T]] it is minus the GPS index, so diag(u,1,1) ∉ G_X | `binary-subshift-ring-k1-is-half-orbit-index` |
| S | Over F_2, K_2(R_X) = 0 for any Cantor homeomorphism. So E(R_X) = St(R_X) is centrally closed, and H_3(E(R_X)) = K^0/3 | `binary-cantor-ring-stable-steinberg-group-centrally-closed` |
| E | e^{2πi/p} is an eigenvalue ⟺ [1] ∈ pK^0 ⟺ R_X ≅ M_p(S). Then G_X ≅ EL_{3p}(LC(U,F_2)⋊_{T^p}Z) ⊇ SL_{3p}(F_2[t^{±1}]); factor maps give subgroups | `rational-eigenvalue-iff-subshift-ring-is-matrix-ring` |
| M | The note's periodic-word models converge in normalized rank to the Ara–Claramunt rank functions. Every invariant measure arises, and each gives a faithful bi-invariant length on G_X | `measure-rank-functions-are-limits-of-periodic-word-models` |
| open | EL_n(R_X) ≅ St_n(R_X) in finite rank? This needs a stable-rank bound (sk-stable-rank-a/b) | `subshift-elementary-groups-are-steinberg-groups-in-finite-rank` |
| firewall | K, I and S depend only on the abstract group K^0: all Sturmians give the same K-groups, while GPS needs order and unit | in node K |

The citations were imported verbatim from Weibel's K-book: Quillen's K_*(F_q), Kervaire–Steinberg, and Gersten.

Normal subgroups ↔ subsystems for non-minimal X is already on main (non-MF tex `thm:core-mf-radical`; artifacts
`pestov91-directed-seams-and-normal-lattices`, `pestov91-cycle-core-exact-mf-reflection`). The lens does not re-prove it.

## (a) Optional O1: a question sentence, only if the note ends with a "Questions" paragraph
Current text: none. The note has no such paragraph (it ends at l.262 before the credit paragraph l.264).
Proposed LaTeX, verbatim:

```latex
Which dynamical properties of $X$ are isomorphism invariants of $G_X$? The word
problem sees the language of $X$. The algebraic $K$-theory of the ring sees only
the abstract dimension group: for $n\ge1$,
\[
 K_n\bigl(\LC(X,\F_2)\rtimes_T\Z\bigr)\cong
 \bigl(K^0(X,T)\otimes K_n(\F_2)\bigr)\oplus K_{n-1}(\F_2),
\]
by the algebraic Pimsner--Voiculescu sequence~\cite{ABC} and Quillen's computation
of $K_*(\F_2)$~\cite{Quillen}. So all Sturmian subshifts give isomorphic $K$-groups.
```

Bibliography additions:

```latex
\bibitem{ABC}
P.~Ara, M.~Brustenga, and G.~Corti\~nas,
\emph{$K$-theory of Leavitt path algebras},
M\"unster J. Math. \textbf{2} (2009), 5--33.
\href{https://arxiv.org/abs/0903.0056}{arXiv:0903.0056}.

\bibitem{Quillen}
D.~Quillen, \emph{On the cohomology and $K$-theory of the general linear groups over a finite field},
Ann. of Math. (2) \textbf{96} (1972), 552--586.
```

- (b) There is no proof text beyond the displayed formula; the two citations carry it. The full derivation is in node K.
- (c) Length: +9 lines of text, +9 lines of bibliography.
- (d) Trade-off: the reader gets a sharp question with a partial answer. In exchange there are two citations the note otherwise does not carry, and a fact the reader must trust through them. Include it only if a Questions paragraph exists, and only if sk-rigidity-* has not settled isomorphism invariants more strongly. (The ABC journal pages 5–33 are recalled and unverified; sk-citations should check them if O1 is adopted.)
- (e) Status: node K is unreviewed and queued with sk-referee-2. Its inputs are the established ABC import and the Quillen import.

## Optional O2, not recommended: rational eigenvalues change the rank
Proposed LaTeX, after l.227 (a paragraph, since the note has no remark environment):

```latex
If $X$ has a continuous eigenvalue $e^{2\pi i/p}$ with $p\ge2$, choose a clopen set $U$ with
$X=U\sqcup TU\sqcup\dots\sqcup T^{p-1}U$. The elements $e_{T^aU}u^{a-b}$, $0\le a,b<p$,
are matrix units with sum $1$, so $R\cong M_p(\LC(U,\F_2)\rtimes_{T^p}\Z)$ and
$G_X\cong\EL_{3p}(\LC(U,\F_2)\rtimes_{T^p}\Z)$.
```

- (c) +4 lines.
- (d) Trade-off: it tells the reader that the rank 3 is not an invariant of the family, but it adds no property of G_X, and the note's Fibonacci-type examples have no rational eigenvalues. Not stronger and not shorter, so not recommended.

## Note for the rigidity lanes
If "continuum many" is re-derived through invariants of R_X, K-theory will not do it: the Sturmian K-groups coincide. The order on K_0 (GPS) or the language (the note's Turing argument) is needed.
