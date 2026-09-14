# sk-free-2 proposal for the note (2026-09-13)

Lane sk-free-2 (free structure lane). Line numbers below refer to the note on main at tip 0d44c399cf (blob md5 9144d8536cdca9073d50ffb64b826c00), not rev3.

## P1: the generic limit of the finite models is simple (optional, +3 text lines, +3 bibliography lines)

**(a) Current text, l.127–131:**
```latex
(Corollaries~\ref{cor:lef} and~\ref{cor:host}). The word problems of the
groups $G_X$ realize every Turing degree, and the factors $L(G_X)$ fall
into continuum many isomorphism classes (Section~\ref{sec:wp}).
```
**Replacement:**
```latex
(Corollaries~\ref{cor:lef} and~\ref{cor:host}). The word problems of the
groups $G_X$ realize every Turing degree, and the factors $L(G_X)$ fall
into continuum many isomorphism classes (Section~\ref{sec:wp}). The
infinite limits of the finite models of Theorem~\ref{thm:main} are the
groups $\EL_3(\LC(Y,\F_2)\rtimes\Z)$ over infinite chain transitive
subshifts $Y$. Such a group is simple exactly when $Y$ is minimal, which
is the generic case~\cite[Theorem~1.3]{PavlovSchmieding}.
```
**Bibitem** (journal locator VERIFY-PENDING through Crossref; the arXiv numbering was read from the PDF):
```latex
\bibitem{PavlovSchmieding}
R.~Pavlov and S.~Schmieding, \emph{On the structure of generic subshifts},
Nonlinearity \textbf{36} (2023). \arxiv{2203.15159}.
```

**(b) Proof as it would stand.** Nothing new in the text: the sentence is a citation plus two facts proved in Cairn.
- *Identification of the limits.* Relations of length ≤ λ depend only on the (2λ+1)-words. Limits of periodic orbits of unbounded period are exactly the infinite chain transitive subshifts (edge shifts of word graphs).
- *Simple iff minimal.* The if direction is Theorem 1. For the only-if direction, an invariant closed proper subset gives a nonzero proper ideal, and so a proper noncentral normal subgroup (`subshift-elementary-group-simple-iff-infinite-minimal`).
- *Generic.* Pavlov–Schmieding Theorem 1.3 (a generic subshift in the closure of the infinite transitive subshifts is regular Toeplitz, hence minimal). The closure is the set of infinite chain transitive subshifts (artifact Lemma 1).

**(c) Length:** +3 text lines, +3 bibliography lines.

**(d) Reader-facing trade-off.** The sentence says that the simple limits form the typical case among all infinite limits of these finite simple expanders, which matches the title. The reader must trust one imported genericity theorem, and two routine facts are left to the reader.

**(e) Status.**
- `generic-limit-of-subshift-sl-models-is-simple-kazhdan` (626720669d): established, unreviewed, queued with sk-verify-13.
- Built on the reviewed `subshift-algebra-groups-embed-in-marked-groups` and the citation `generic-transitive-subshift-is-regular-toeplitz`, queued for source check.

## Not proposed for the note
The maximal-subgroup results are Cairn-only; main may weigh a Questions sentence:
- `subshift-el3-acts-two-transitively-on-orbit-modules`;
- `subshift-el3-has-continuum-many-maximal-subgroup-classes`;
- `subshift-el3-orbit-stabilizers-conjugate-iff-same-orbit`;
- `subshift-el3-parabolic-subgroups-are-maximal`.

They are structure theory off the note's line (Brown/Ozawa/Pestov, LEF, word problems).
