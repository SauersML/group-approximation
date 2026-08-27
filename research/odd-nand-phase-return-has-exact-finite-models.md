---
rg: 2
id: odd-nand-phase-return-has-exact-finite-models
kind: claim
title: The odd NAND phase return has exact finite models and cannot itself supply soundness
distinct_from:
  odd-nand-cycle-cancels-separators-to-central-phase: that computes the returned word W_C equals J; this audits the logical direction and gives an exact finite model of the whole odd-cycle phase packet.
  perfect-lcs-gap-implies-nonhyperlinear: that turns an independently proved tracial/non-RU LCS gap into a group; this proves the odd NAND return does not create that gap without the missing global BCS decoder.
  exact-fd-invisibility-has-no-general-hs-robustification: that gives a general counterexample to promoting exact finite-dimensional invisibility; this supplies exact finite representations with the mark visible for the specific NAND-cycle proposal.
---

The local relations of an odd NAND swap cycle do not force its returned phase
word to approach the identity in finite dimensions.  Already for a triangle
there is an exact three-dimensional signed-permutation model with

```text
W_C=J=-I_3.                                              (ONF1)
```

Take the orthonormal basis labelled by the three assignments

```text
100, 010, 001.                                           (ONF2)
```

Let `X_i` be the sign which is `-1` exactly on the assignment whose `i`-th
bit is one, and `+1` on the other two.  Every adjacent pair
`(X_i,X_(i+1))` has precisely the three NAND atoms, all of rank one.  Let
`H_i` fix the `X_i=-1` basis vector and swap the other two.  With indices
modulo three,

```text
H_i X_(i+1) H_i^*=J X_i X_(i+1).                       (ONF3)
```

All these matrices lie in the finite signed permutation group
`(C_2)^3 semidirect S_3`.  The odd-cycle return theorem gives `(ONF1)`.
Taking arbitrary direct sums gives exact finite models of unbounded
dimension with the marked phase fully visible.

This leaves exactly three logical possibilities for using the word `W_C`.

1. If `W_C=1` is added as a defining group relator, then the already-derived
   identity `W_C=J` forces `J=1` in **every** representation, including the
   intended commuting/non-CE model.  Perfect completeness is destroyed.
2. If only the local NAND and swap relations are imposed, `(ONF1)--(ONF3)`
   give exact finite-dimensional models with `J=-I`; matrix soundness is
   false even before approximation.
3. Additional global relations may preserve a commuting model with `J=-1`
   while forcing `W_C -> 1` in every finite-dimensional approximate model.
   But, because `W_C=J`, this is precisely a robust tracial-versus-`R^U`
   central-mark gap.  For LCS syntax it is exactly the
   `lcs-tracial-ru-gap-equiv-nonhyperlinear` endpoint; for the fixed non-CE
   BCS it requires the still-open common-corner/approximate decoder.

Therefore the positive odd-cycle phase return completes mark **routing** but
does not reduce the decisive soundness gate.  No relation-level shortcut can
make the word trivial only in matrices: such a distinction must come from
global non-CE compatibility, not from the finite NAND/Schur packet.

