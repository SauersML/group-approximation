---
rg: 2
id: universal-residual-wordization-collapses-carrier
kind: claim
title: A representation-universal relator bound collapses every nonzero algebraic residual carrier
distinct_from:
  algebraic-selector-mixing-frame-collapses-forbidden-sector: that proves the collapse from a selector-mixing operator frame; this isolates the faithful-regular-trace obstruction for any proposed ordinary-word lower bound.
  canonical-root-coordinate-is-binary-not-an-l2-authenticator: that concerns one canonical microstate coordinate; this rules out a universal exact lower bound already in the group itself.
---

**ESTABLISHED.**  Let `Gamma=<S|R>` be a group, let `A` be a faithfully
canonically traced group-algebra corner, and let `X in A`.  Suppose finitely
many ordinary words `w_1,...,w_k`, equal to `1` in `Gamma`, and a constant
`kappa>0` satisfied the representation-universal estimate

```text
kappa ||X||_2^2
 <=sum_j ||pi(w_j)-1||_2^2                              (URW1)
```

in every tracial unitary representation containing the decoded corner.
Then `X=0`.

Indeed apply `(URW1)` to the canonical regular representation.  Every
`w_j` is exactly `1`, so the right side vanishes.  Faithfulness of the
canonical corner trace gives `X=0`.

In particular, if `(K_i)` is any algebraic tight frame with

```text
sum_i K_i^*K_i=1,
```

then

```text
sum_i||K_iX||_2^2=||X||_2^2.                           (URW2)
```

No finite menu of defining word defects can universally lower-bound the
left side of `(URW2)` while retaining a phase-safe nonzero algebraic `X`.
This applies directly to the Fano Naimark carrier `(FNC6)`.

The local ghost wordizer does not contradict this theorem.  Imposing its
dihedral commutator deletes the ghost representation type, so the ghost
projection is zero in the quotient packet rather than a phase-safe nonzero
element.  For a global compiler that must retain a marked source carrier,
the frame-to-word lower bound must therefore be genuinely
finite-matrix/canonical-type-only.  It cannot follow solely from exact
finite Hecke/Morita identities valid in the regular representation.
