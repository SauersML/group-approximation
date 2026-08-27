---
rg: 2
id: finite-magic-square-selector-no-freezing-proof
kind: route
title: Derive the diagonal magic-square commutator and pin it by a Z-aligned Pauli selector
target: finite-magic-square-selector-has-no-frozen-branch
requires: []
---

Write the magic-square generators as

```text
a b c
d e f
g h i.
```

The row relations give `c=ab`, `f=de`, and `i=gh`; the first two column
relations give `g=ad` and `h=be`.  The corresponding row and column pairs
commute.  The last column relation is therefore

```text
J=cfi=(ab)(de)(ad)(be).                                  (MSP1)
```

Now `a` commutes with `b,d`, while `e` commutes with `b,d`.  Put `s=bd`.
Then `s` commutes with both `a` and `e`, and direct cancellation in `(MSP1)`
gives

```text
(ab)(de)(ad)(be)
 =a (bd) e a (db) e
 =a s e a s^(-1)e
 =a e a e
 =[a,e].                                                  (MSP2)
```

Thus `[a,e]=J`, which is `(MSS1)` with `a=x_11` and `e=x_22`.

For completeness, use the standard real Pauli table

```text
a=X tensor I,      b=I tensor X,      c=X tensor X,
d=I tensor Z,      e=Z tensor I,      f=Z tensor Z,
g=X tensor Z,      h=Z tensor X,      i=Y tensor Y.
```

Every displayed matrix is a real signed permutation (the two imaginary
factors in `Y tensor Y` cancel), the row products and first two column
products are `I`, and the final column product is `-I`.  Replace the signed
four-dimensional space by its eight-point signed-set action: a monomial
matrix sends `(q,t)` to `(q',t+sigma)`, and `J` flips `t`.  Uniform measure
makes this a finite IRS strategy.

Let the readable variable be the same signed permutation as `e=Z tensor I`.
It fixes or sign-flips each two-point `J`-orbit, so it is Z-aligned.  On its
`epsilon` atom, `e=J^epsilon`, proving the controlled equation `(MSS2)`.
No edge requiring the readable variable to commute with `a` is added; the
only new context contains the readable selector and `e`, which commute.

Finally, freezing either value gives `e=J^epsilon`.  Since `J` is central,
`[a,e]=1`; comparison with `[a,e]=J` gives `J=1`.  The magic-square game
criterion then excludes a perfect commuting-operator strategy in both frozen
branches.
