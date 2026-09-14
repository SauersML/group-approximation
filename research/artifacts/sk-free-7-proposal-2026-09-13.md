# sk-free-7 proposal: "pairwise nonisomorphic" becomes "pairwise non-embeddable" (2026-09-13)

Lane sk-free-7. Line numbers refer to the landed note on main (rev3, md5 274f19367f7f706b05c017af721c3884).

## (a) Current text and replacement

**Corollary statement, l.368–369.** Current:
```latex
$L(X)$ is recursive, as for the Fibonacci subshift. Every Turing degree
occurs, so there are continuum many pairwise nonisomorphic groups $G_X$.
```
Replacement:
```latex
$L(X)$ is recursive, as for the Fibonacci subshift. Every Turing degree
occurs, so there are continuum many groups $G_X$, none of which is
isomorphic to a subgroup of another.
```

**End of the proof, l.398–399.** Current:
```latex
earlier digits. There are continuum many degrees, and the degree of the
word problem is an isomorphism invariant.
```
Replacement:
```latex
earlier digits. If a finitely generated group $H$ embeds in $G$, a word
for $H$ becomes a word for $G$ by substituting for its generators, so
the word problem of $H$ reduces to that of $G$. The Turing degrees
contain an antichain of size continuum~\cite[p.~462]{Odifreddi}, and
the groups $G_{X_\alpha}$ with $\alpha$ of these degrees are as claimed.
```

**Bibliography**, alphabetical between Lothaire and Ore:
```latex
\bibitem{Odifreddi}
P.~Odifreddi, \emph{Classical Recursion Theory}, North-Holland,
Amsterdam, 1989.
```

## (b) Complete proof text
The replacement above is the complete proof text. The realization "every set S has the degree of [0;1+χ_S(0),…]" is already in the note (l.394–398). It supplies a slope α ≡_T S for each S in the antichain.

## (c) Length
- Statement: +1 line.
- Proof: +3 lines.
- Bibliography: +3 lines.

## (d) Trade-off
Stronger, at the cost of one textbook fact the reader must trust: the Turing degrees contain an antichain of size continuum (Sacks' construction). A finite-extension proof of it is in Cairn.

## (e) Status
- `continuum-many-subshift-el-groups-pairwise-non-embeddable` (+ `-proof`): established, unreviewed, queued with sk-verify-13.
- `turing-degrees-contain-continuum-antichains` (+ `-proof`, complete direct proof): established, unreviewed.
- **Locator.** VERIFY-PENDING: Odifreddi p. 462 is taken from Terwijn, arXiv:math/0606529 (source l.459, `\cite[p462]{Odifreddi}`); the book was not opened. Fallback wording without a page: "…contain an antichain of size continuum, by a construction of Sacks".
- `positive-entropy-el-groups-avoid-low-complexity-hosts`: Cairn only; no note change proposed.
