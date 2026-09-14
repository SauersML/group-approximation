# sk-fp-sofic-b: manuscript proposal (optional closing remark on Z^2)

Lane `sk-fp-sofic-b`, 2026-09-13. Line numbers refer to `sk/manuscript-disk-1646.tex` (340 lines, md5 7b3dc4ec…).

## Verdict for the note

- The lane question is whether `EL_3(LC(X,F_2) ⋊ Z^2)` is sofic for an aperiodic minimal SFT `X`. It is
  undecided, and nothing proved here strengthens the headline theorem.
- The mathematics lives on main in `subshift-algebra-groups-embed-in-marked-groups` and
  `research/artifacts/sk-fp-sofic-b-z2-soficity-map-2026-09-13.md` (unreviewed). It explains the note's
  finite models in one line: they are approximations of `X` by finite subshifts with the same small words.
  Those exist for every minimal `Z`-subshift, and for no infinite minimal subshift of finite type.
- **Recommendation: omit, unless the note gets a short closing section of questions.** In that case add the
  paragraph below, and coordinate with sk-open-5 and sk-general-actions-a so that there is one paragraph on
  higher rank, not several.

## (a) The change

**Current text** (l.260-264):
```latex
of a finitely generated group is an isomorphism invariant.
\end{proof}

\subsection*{Origin and authorship}
```

**Proposed**, inserted between l.262 and l.264. Variant A:
```latex
\subsection*{Subshifts of $\Z^2$}
The proofs of property~\textup{(T)} and simplicity apply to free minimal
subshifts of $\Z^d$. The finite models use periodic points with the same
patterns as $X$. An infinite minimal subshift of finite type over $\Z^2$
has no such points, and Labb\'e's nineteen Wang tiles give one~\cite{Labbe}.
For such $X$ we do not know whether $\EL_3(\LC(X,\F_2)\rtimes\Z^2)$ is sofic.
```

Variant B, the shortest, which rests on nothing unreviewed:
```latex
\subsection*{Subshifts of $\Z^2$}
The finite models use periodic points with the same patterns as $X$. An
infinite minimal subshift of finite type over $\Z^2$, such as Labb\'e's
Wang shift~\cite{Labbe}, has none, and we do not know whether
$\EL_3(\LC(X,\F_2)\rtimes\Z^2)$ is sofic.
```

**Bibliography, both variants** (alphabetical position after `GM`):
```latex
\bibitem{Labbe}
S.~Labb\'e, \emph{A self-similar aperiodic set of 19 Wang tiles},
\href{https://arxiv.org/abs/1802.03265}{arXiv:1802.03265} (2018).
```
**Citation flag for sk-citations.** Main's import node `minimal-aperiodic-wang-shift-exists` prints the author
as "J. Labbé". I believe the author is Sébastien Labbé, and that a journal version exists (Geom. Dedicata,
2019), but I have verified neither. The arXiv number and Theorem 1 ("The Wang shift Ω_U is self-similar,
aperiodic and minimal") were read from the TeX source by that node's lane.

## (b) Proof text

- **Variant A, first sentence.** It rests on `free-minimal-subshift-elementary-groups-are-simple-kazhdan`
  (established, unreviewed): box towers replace intervals, and (T) needs only finite generation.
- **"No such points."** A periodic configuration all of whose windows of the forbidden-pattern size are
  allowed is a point of `X` with a finite orbit. An infinite minimal subshift has no finite orbit.
- **"We do not know."** This is a statement of ignorance, with no claim that the question is open in the
  literature. The graph check is bounded to main's nodes: `free-minimal-subshift-elementary-groups-are-sofic`
  is OPEN there.

## (c) Length

- Variant A: +6 text lines, +3 bibliography lines.
- Variant B: +5 text lines, +3 bibliography lines.

## (d) Reader-facing trade-off

The paragraph tells the reader exactly where dimension one is used, and it poses the natural next question.
It costs a paragraph and a citation. It does not strengthen the headline, and variant A adds one fact the
reader must trust.

## (e) Status

- `subshift-algebra-groups-embed-in-marked-groups` and its route: established, unreviewed (queued with
  sk-verify-3).
- `free-minimal-subshift-elementary-groups-are-simple-kazhdan`: established, unreviewed (peer node).
- `free-minimal-subshift-elementary-groups-are-sofic`: open.
