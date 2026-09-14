# sk-rigidity-cartan proposal for the note (2026-09-13)

Frozen copy `sk/manuscript-disk-1646.tex`; revision 1 on main (5b1890ce6c).

## (a) Proposed change
**None.** Nothing this lane proved strengthens Theorem 1 or the word-problem corollary, and none of it answers a
question the note poses.

If the questions paragraph (main's decision 18, Q3) is written, one clause may be added to Q3.
- Main's current wording of Q3 is not landed, so there is no verbatim text to quote. Proposed wording:
  ```latex
  Flip conjugacy of $X$ and $Y$ gives $G_X\cong G_Y$. We do not know the converse, even for isomorphisms
  $\LC(X,\F_2)\rtimes\Z\cong\LC(Y,\F_2)\rtimes\Z$ of the rings.
  ```
- Recommendation: add this clause only if Q3 is kept. It costs one line and needs no new citation.

## (b) Proof text
None needed: the clause states an open question.
- The easy direction, flip conjugacy ⇒ isomorphism, comes from `u ↦ u^{±1}` and composition with the conjugacy.

## (c) Length
+0 lines, or +1 line inside Q3.

## (d) Reader trade-off
The clause tells the reader that the classification is open already at ring level. That is sharper than "open for
groups", and asks the reader to trust no new fact.

## (e) Status
Landed on main, all established and unreviewed (review requested from sk-verify-5):
- `algebraic-cartan-pairs-are-effective-groupoid-steinberg-algebras` (+`-citation`), import;
- `diagonal-preserving-isomorphisms-reconstruct-effective-groupoids` (+`-citation`), import;
- `subshift-crossed-product-growth-is-n-times-complexity` (+`-citation`), import;
- `subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity` (+`-reduction-proof`): Theorem C;
- `subshift-ring-isomorphism-preserves-soe-class-and-growth` (+`-soe-and-growth-proof`): Theorem G.

Still OPEN: `subshift-crossed-product-algebraic-cartans-are-conjugate`.
