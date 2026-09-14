# sk-strong-1: manuscript proposal (2026-09-13)

- Target: `simple_kazhdan_sofic_group.tex` on main, rev1 5b1890ce6c.
- Status: unreviewed. It depends on `rf-groups-embed-in-simple-kazhdan-lef-groups` passing review.
- Recommendation: add this ONLY if the note adopts the RF embedding corollary (rev2-decisions item 22). Then extend
  that corollary by one short paragraph.

## (a) Addition, right after the RF embedding corollary and its proof (no current text is replaced)
```latex
By a theorem of Wilson~\cite[Theorem~A]{Wilson}, every countable residually
finite group embeds in a $2$-generator residually finite group. The restricted
direct sum of the countably many recursively presented finitely generated
residually finite groups is countable and residually finite, so one infinite
simple Kazhdan LEF group contains all of them, in particular every finitely
generated linear group.
```
Bibliography:
```latex
\bibitem{Wilson}
J.~S. Wilson, \emph{Embedding theorems for residually finite groups},
Math. Z. \textbf{174} (1980), 149--157. \doi{10.1007/BF01293535}.
```

## (b) Proof as it would appear
The paragraph is its own proof, given the corollary. Its facts:
- the direct sum is residually finite (coordinatewise);
- recursively presented groups are countable;
- f.g. linear groups are residually finite (Malcev) and recursively presented.

A reader who wants the last point spelled out can have one clause: "linear groups over finitely generated rings have
solvable word problem".

## (c) Length
+6 text lines, +3 bibliography lines.

## (d) Reader-facing trade-off
The note gets strictly stronger: from "each f.g. RF group embeds" to "one group contains every recursively presented
f.g. RF group". The reader trusts one classical theorem (Wilson 1980, Theorem A, verified from the primary PDF) and
Malcev's theorem.

Optional sharpness clause, not recommended for a short note (+2 text, +3 bibliography lines): "No finitely generated
group contains every finitely generated residually finite group, since there are uncountably many of
them~\cite{ChongWise}."

## (e) Status
- Nodes: `wilson-countable-rf-into-two-generator-rf-groups` (import), `countable-rf-groups-embed-in-simple-kazhdan-lef-groups`,
  `universal-simple-kazhdan-lef-groups-exist`, `no-finitely-generated-group-contains-all-fg-rf-groups`,
  `chong-wise-uncountably-many-fg-residually-finite-groups` (import).
- All unreviewed, queued with sk-verify-4.
- Full write-up: `research/artifacts/sk-strong-1-universal-kazhdan-group-2026-09-13.md`.
