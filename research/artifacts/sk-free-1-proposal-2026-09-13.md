# sk-free-1 proposal: one sentence on exactness of the hosts (2026-09-13)

Lane sk-free-1. Line numbers refer to main's rev3 `simple_kazhdan_sofic_group.tex` (md5 274f19367f7f706b05c017af721c3884). The sentence goes after the universal host corollary. In rev4 it goes after the recursive-host corollary of decision item 71(d).

## (a) Current text (rev3 l.354–362), verbatim
```latex
\begin{proof}
Finitely generated linear groups are residually finite by Malcev's
theorem, and up to isomorphism there are countably many groups of either
kind. So their direct sum is a countable residually finite group. Wilson
proved that every countable residually finite group embeds in a
$2$-generator residually finite group~\cite[Theorem~A]{Wilson}. Such a
group is LEF, and Corollary~\ref{cor:lef} applies.
\end{proof}
```

## Replacement: append after `\end{proof}`
**Version R (rev4, host for every recursively presented f.g. LEF group; established, unreviewed):**
```latex
This host is not exact. Osajda constructed finitely generated residually
finite groups that are not exact~\cite{OsajdaRF}, and his construction
yields a recursively presented one. Property~A passes to subgroups, so
$C^*_r$ of the host is not exact, while its group von Neumann algebra
embeds in $\mathcal R^\omega$.
```

**Version S (for rev3's Wilson host, which is not known to contain Osajda's group):**
```latex
Applied to the residually finite non-exact groups of Osajda~\cite{OsajdaRF},
Corollary~\ref{cor:lef} gives infinite simple Kazhdan LEF groups that are
not exact.
```

Bibitem:
```latex
\bibitem{OsajdaRF}
D.~Osajda, \emph{Residually finite non-exact groups}, Geom. Funct. Anal.
\textbf{28} (2018), 509--517. \doi{10.1007/s00039-018-0432-4}.
```

## (b) Proof text
It is the paragraph itself. Version R also rests on the effectivity check in `research/artifacts/sk-free-1-exactness-2026-09-13-part2.md` §2, which the note does not print. If main prefers not to import it, use Version S, which needs only Osajda's published theorem.

## (c) Cost
- Version R: +5 text lines, +3 bibliography lines.
- Version S: +3 text lines, +3 bibliography lines.

## (d) Trade-off
A new fact the reader must trust: Osajda's theorem, plus for R the effectivity of his construction. It shows that the note's LEF hosts can be non-exact on the C*-side while L(G) ⊂ R^ω, which is the contrast a reader of Brown's question looks for.

## (e) Status
- `residually-finite-non-exact-groups-exist` (literature, verbatim at source).
- `some-simple-kazhdan-lef-groups-are-not-exact`: established, unreviewed; version S.
- `recursive-residually-finite-non-exact-groups-exist`: established, unreviewed.
- `universal-recursive-lef-host-is-not-exact`: established, unreviewed; version R.
- Open companion: `subshift-elementary-groups-are-exact` (is G_X exact?).
