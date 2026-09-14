# sk-rigidity-ring: manuscript proposal (RULES §6)

Lane `sk-rigidity-ring`, 2026-09-13. Line numbers refer to the frozen disk copy of `simple_kazhdan_sofic_group.tex`
(340 lines, md5 7b3dc4ec…).

## Verdict: no change to the note (recommended)

The lane's established result is about RINGS: `cantor-crossed-product-matrix-ring-iso-forces-soe`, unreviewed. It
states that `M_m(LC(X,k)⋊Z) ≅ M_m(LC(Y,k')⋊Z)` (or its opposite) forces strong orbit equivalence. The group statement
the note would want is "`G_X ≅ G_Y` implies X and Y are strongly orbit equivalent", and it needs every isomorphism of
the groups `EL_3(LC(X,F_2)⋊Z)` to be standard. That is `subshift-el3-isomorphisms-are-standard-over-f2`, which is OPEN:
- all located isomorphism theorems assume `1/2`, or `n ≥ 4` with `GL_n`;
- Petechuk shows `n = 3` is exceptional in characteristic 2.

So nothing about `G_X` beyond the current corollary is established. The current corollary (l.229–262, continuum many
through Turing degrees) stays the right source of "continuum many".

## (a) Optional sentence, NOT recommended

Place: after the corollary's proof (after l.262, before l.264 "Origin and authorship").

Current text (l.261–262):
```
of a finitely generated group is an isomorphism invariant.
\end{proof}
```
Replacement:
```
of a finitely generated group is an isomorphism invariant.
\end{proof}

It is not known whether $G_X\cong G_Y$ forces $X$ and $Y$ to be strongly
orbit equivalent. For the rings $M_3(\LC(X,\F_2)\rtimes\Z)$ the corresponding
statement holds, by the theorem of Giordano, Putnam and Skau.
```

## (b) Proof text

None in the note. The ring statement would need, in the reader's hands:
- `K_0` of the algebraic crossed product (Ara–Brustenga–Cortiñas);
- the order cone (Ara–Claramunt measure rank functions; Herman–Putnam–Skau; Effros);
- torsion-freeness of `K^0`;
- Giordano–Putnam–Skau.
The complete argument is artifact `research/artifacts/sk-rigidity-ring-2026-09-13-part1.md` §1 (six steps, about 40
lines).

## (c) Length change

+3 lines of text and +3 bibliography entries (Giordano–Putnam–Skau; Ara–Claramunt; Ara–Brustenga–Cortiñas), or 0 if
declined.

## (d) Reader-facing trade-off

The sentence gives the reader a sharp open question and a true ring-level answer. But its second half is a new fact
the reader must trust from four outside sources with no proof in the note, and it does not strengthen any theorem about
`G_X`. So it is neither stronger nor shorter. Decline, unless `subshift-el3-isomorphisms-are-standard-over-f2` is
settled.

## (e) Status

- Established, UNREVIEWED:
  - `cantor-crossed-product-matrix-ring-iso-forces-soe` (+ `-proof`);
  - `subshift-gl3-iso-forces-strong-orbit-equivalence-odd-q` (+ `-proof`).
- Established by citation (verbatim from the Durand–Perrin TeX, primary papers not opened):
  - `gps-strong-orbit-equivalence-iff-unital-ordered-k0`;
  - `minimal-cantor-k0-positive-iff-positive-on-all-measures`.
- OPEN: `subshift-el3-isomorphisms-are-standard-over-f2`.
- Complementary peer result (lane sk-rigidity-intrinsic, unreviewed):
  `subshift-elementary-group-diagonal-iso-gives-flip-conjugacy`. A diagonal-preserving isomorphism `G_X → G_Y` exists
  iff `X` and `Y` are flip conjugate.

If both open steps close, the natural statement for the note is "`G_X ≅ G_Y` iff `X` and `Y` are flip conjugate". The
two steps are (i)–(ii) of the intrinsic route, for flip conjugacy, or the standardness claim here, for strong orbit
equivalence. That statement could then replace the Turing corollary as the source of continuum many, with a
dynamical classification. Neither step is close.
