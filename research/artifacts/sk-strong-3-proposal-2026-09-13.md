# sk-strong-3 proposal: one simple Kazhdan LEF group containing every finitely generated linear group

Lane sk-strong-3, 2026-09-13.
- Base: main's note at rev1 (5b1890ce6c). It has no embedding corollary yet; main's decision log
  `sk/drafts/rev2-decisions.md` item 22 plans the RF embedding corollary.
- Status: Theorem U (`simple-kazhdan-lef-host-for-countably-many-rf-groups`) is UNREVIEWED. Its inputs are reviewed
  (Theorem E, sk-verify-3 PASS) or verified from the source (Wilson, Theorem A).

## (a, b) Text

### Option 1 (recommended): extend the RF embedding corollary of item 22
Current rev1 text: none. The corollary would follow the RF embedding corollary as `\label{cor:rf}`:
```latex
\begin{corollary}\label{cor:universal}
There is one infinite, finitely generated, simple group with
property~\textup{(T)} that is LEF and contains every finitely presented
residually finite group and every finitely generated linear group.
\end{corollary}

\begin{proof}
There are countably many such groups up to isomorphism, so their direct
sum $P$ is a countable residually finite group. By
Wilson~\cite[Theorem~A]{Wilson}, $P$ embeds in a $2$-generator residually
finite group, and Corollary~\ref{cor:rf} embeds that group in an infinite
finitely generated simple Kazhdan LEF group.
\end{proof}
```
Bibliography:
```latex
\bibitem{Wilson}
J.~S. Wilson, \emph{Embedding theorems for residually finite groups},
Math. Z. \textbf{174} (1980), 149--157.
\doi{10.1007/BF01293535}.
```

### Option 2, if item 22 is not adopted
State Corollary U′ directly, with a proof of at most 18 lines: Wilson, the Ore overgroup, the Toeplitz envelope, and
`diag(u,1,1)`. This is item 22's budget plus 2 lines.

### Optional abstract sentence (+2 lines)
```latex
One simple Kazhdan LEF group contains every finitely generated linear group.
```

## (c) Length
- Option 1: +10 source lines of text and +4 of bibliography.
- The optional sharpness clause ("no finitely generated group contains every finitely generated residually finite
  group") costs +2 lines and 1 bibitem (Chong–Wise). Recommended against: the reader does not need it.

## (d) Reader-facing trade-off
- Much stronger and memorable, and for a non-specialist the most striking statement in the note: one simple Kazhdan
  approximable group holds every finitely generated matrix group and every finitely presented residually finite group.
- No new machinery. The reader must trust one more classical theorem (Wilson 1980, Theorem A).
- The proof is three lines given Corollary cor:rf.

## (e) Status
- Nodes: `simple-kazhdan-lef-host-for-countably-many-rf-groups` + `-proof` (unreviewed), and
  `wilson-countable-rf-embeds-in-2-generator-rf` + `-citation` (verified from the PDF, p. 149).
- Review requested in `sk/queue/sk-verify-4.txt`.
