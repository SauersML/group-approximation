# sk-rigidity-intrinsic: manuscript proposal (RULES §6)

Lane sk-rigidity-intrinsic, 2026-09-13. Line numbers refer to `manuscript-disk-1646.tex` (340 lines, md5 7b3dc4ec…).

## Verdict

Rigidity does not enter the note at note length.
- The group-theoretic reconstruction proves diagonal-preserving rigidity (Theorem A below): an isomorphism
  `G_X ≅ G_Y` carrying `GL_3(LC(X,F_2))` onto `GL_3(LC(Y,F_2))` exists iff `X` and `Y` are flip conjugate.
- The classification of the groups `G_X` up to arbitrary isomorphism is OPEN. Any proof of flip rigidity must also
  prove that the algebraic crossed product ring, with no diagonal given, determines the subshift up to flip conjugacy.
  The C*-analogue of that is false (it gives only strong orbit equivalence), and no algebraic theorem of this kind was
  located.
- So "continuum many isomorphism classes" should keep coming from Turing degrees (l.231–262), which is unconditional
  and short.

## Proposal 1 (recommended): no change

Trade-off: the note stays as short as it is, and nothing unverified is added.

## Proposal 2 (optional, +2 lines): state the easy direction and the question

(a) Current text, l.259–262:
```latex
degree. There are continuum many degrees, and the word-problem degree
of a finitely generated group is an isomorphism invariant.
\end{proof}
```
Replacement:
```latex
degree. There are continuum many degrees, and the word-problem degree
of a finitely generated group is an isomorphism invariant.
\end{proof}

A flip conjugacy $\psi$ with $\psi T=S^{\pm1}\psi$ induces the ring isomorphism
$fu^j\mapsto(f\circ\psi^{-1})u^{\pm j}$, so flip conjugate subshifts give
isomorphic groups. Whether $G_X\cong G_Y$ forces $X$ and $Y$ to be flip
conjugate is open.
```

(b) Proof text: the first sentence is the complete proof of the easy direction. Check:
`u^{±1}(f∘ψ^{-1})u^{∓1} = (f∘T^{-1})∘ψ^{-1}` when `ψT = S^{±1}ψ`.

(c) Length: +4 source lines, about +3 typeset lines.

(d) Reader trade-off: it gives the natural classification problem with its easy half and needs no new machinery. The
one fact the reader must trust is "open", resting on a bounded literature check (three web searches plus the
reconstruction abstracts; see the reconstruction artifact, §5).

(e) Status: the easy direction is elementary and verified here. "Open" is the status of
`subshift-elementary-group-isomorphism-forces-orbit-equivalence` on main.

## Not proposed for the note: Theorem A

Statement: for infinite minimal subshifts `X, Y`, an isomorphism `EL_3(R_X) → EL_3(R_Y)` carrying `GL_3(LC(X,F_2))`
onto `GL_3(LC(Y,F_2))` exists iff `X` and `Y` are flip conjugate.

Proof ingredients:
- normal subgroups of `LC(X, GL_3(F_2))` recover `X`;
- the normalizer of the diagonal acts through a group between `[[T]]'` and `[[T]]`, and a 3-cycle argument gives
  piecewise closure `[[T]]`;
- Giordano–Putnam–Skau / Bezuglyi–Medynets.

About a page. Trade-off: the hypothesis "carries the diagonal onto the diagonal" is not intrinsic, so a reader gains
little over the obvious converse. It belongs in Cairn.

Nodes landed with this proposal (all unreviewed):
- `subshift-elementary-group-diagonal-iso-gives-flip-conjugacy`, route `subshift-el3-diagonal-iso-flip-conjugacy-proof`;
- `subshift-elementary-group-rigid-supports-are-mutual-centralizers`, route `subshift-el3-rigid-supports-proof`;
- `locally-constant-simple-group-normal-subgroups-are-open-sets`, route `locally-constant-simple-group-normal-subgroups-proof`;
- `topological-full-groups-determine-flip-conjugacy`, route `topological-full-groups-determine-flip-conjugacy-citation`;
- Attempts added to `subshift-elementary-group-isomorphism-forces-orbit-equivalence`.

## For main and peers

- sk-rigidity-ring's route through isomorphism theorems meets, beyond characteristic 2 and the F-PE firewalls,
  the same diagonal obstruction.
  - Zel'manov-type theorems give at best `M_3(R_X) ≅ M_3(R_Y)`.
  - Turning that into flip conjugacy needs Cartan uniqueness in `M_3(R_Y)`.
  - Turning it into strong orbit equivalence needs only `K_0` with order and unit, so strong orbit equivalence is the
    realistic ring-side target; flip conjugacy is not.
- Heights: the constant height-3 Kakutani tower over `X` is flip conjugate to that over `Y` iff `X` and `Y` are flip
  conjugate, since a clopen set with constant return time 3 is unique up to `T^j`. So flip conjugacy loses nothing to
  the unit `3[1]`, whereas strong orbit equivalence can (open for unit scaling).
