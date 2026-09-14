# sk-iso-rigidity: manuscript proposal (RULES §6)

Lane sk-iso-rigidity, 2026-09-13. Line numbers refer to rev3 as landed on main (9047d0d3c9, md5 274f1936…).

## Verdict: no change to the note (recommended)

The lane's results concern the rigidity question in §4 (l.417–420):
- `peirce-root-homomorphisms-of-e3-are-standard`;
- `peirce-root-preserving-subshift-el3-isos-force-orbit-equivalence`;
- `diagonal-recognition-makes-subshift-el3-isos-standard`.

They sharpen the frontier: an isomorphism `G_X → G_Y` is standard, and forces strong orbit equivalence, as soon as it
carries `GL_3(LC(X,F_2))` onto a conjugate of `GL_3(B)` for a Cartan-type `B`. They do not answer the question. The
proofs of the consequences use the ordered `K_0` machinery (Ara–Claramunt, Herman–Putnam–Skau, Giordano–Putnam–Skau),
which the note should not carry. So the question stays as it is, and the frontier stays in Cairn.

## (a) Optional variant, NOT recommended before review

Current text (l.417–420):
```latex
If $(X,T)$ is topologically conjugate to $(Y,S)$ or to $(Y,S^{-1})$, then
$G_X\cong G_Y$. For topological full groups the converse
holds~\cite{GPS99,BezuglyiMedynets}. Does $G_X\cong G_Y$ imply that $X$ and
$Y$ are flip conjugate, or at least strongly orbit equivalent~\cite{GPS}?
```
Replacement:
```latex
If $(X,T)$ is topologically conjugate to $(Y,S)$ or to $(Y,S^{-1})$, then
$G_X\cong G_Y$. For topological full groups the converse
holds~\cite{GPS99,BezuglyiMedynets}. Does $G_X\cong G_Y$ imply that $X$ and
$Y$ are flip conjugate, or at least strongly orbit equivalent~\cite{GPS}? It
would suffice to show that every isomorphism maps $\GL_3(\LC(X,\F_2))$ onto a
conjugate of $\GL_3(\LC(Y,\F_2))$.
```

## (b) Proof text

The added sentence needs the diagonal-preserving theorem (Theorem A of sk-rigidity-intrinsic, PASS), which is
about 25 lines (Lemma B, normalizers, Bezuglyi–Medynets). The note would have to cite it or leave the sentence out.
That is why this variant is not recommended.

## (c) Length

+2 source lines for the variant; 0 for the recommendation.

## (d) Reader trade-off

The variant tells the reader where the difficulty sits (recognizing the locally constant diagonal), but it asks them
to trust an unpublished reduction. The recommendation adds nothing to trust.

## (e) Status

- `peirce-root-homomorphisms-of-e3-are-standard`, `peirce-root-preserving-subshift-el3-isos-force-orbit-equivalence`,
  `diagonal-recognition-makes-subshift-el3-isos-standard`: established, unreviewed, queued with sk-verify-13.
- `subshift-el3-isomorphisms-recognize-diagonal-subgroups`: OPEN.
- `subshift-elementary-group-diagonal-iso-gives-flip-conjugacy`: PASS (sk-verify-3).
