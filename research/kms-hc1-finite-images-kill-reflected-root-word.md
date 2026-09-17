---
rg: 2
id: kms-hc1-finite-images-kill-reflected-root-word
kind: claim
title: Some HC1 reflected root word is killed in every finite group image
artifacts:
  - research/artifacts/kms-hc1-marked-root-kernel-candidate-2026-09-12.md
---

There exists a prime `p>=7` such that, for every finite group `F` and every
triple `A,B,C in F` satisfying

```text
A^p=B^p=C^p=1,
[A,B,A]=[A,B,B]=[B,C,B]=[B,C,C]=1,
[A,C,A]=[A,C,C,A]=[A,C,C,C]=1,
```

one has `([B,A][B,C])^p=1`. Commutators use
`[X,Y]=X^-1 Y^-1 X Y` and left association.

Equivalently, for this `p`, the explicit word `w_p` from
`kms-hc1-reflected-root-word-is-nontrivial` belongs to the finite residual
of `Gamma_p`. The first concrete parameter to investigate is `p=7`.

## Attempts

- **Positive Kac--Moody images.** The canonical map kills `w_p`, so all
  finite maps factoring through it kill the word. No factorization of
  arbitrary finite images through that map has been proved.
- **Block matrices of arbitrary size.** For any field of characteristic
  `p` and any square matrices `X,Y,Z` of equal size, the triple
  `I+E_12(X), I+E_23(Y), I+E_31(Z)` satisfies the relators and kills the
  word. The product of the two relevant commutators is `I+N` with
  `N^3=0`. This is a complete calculation for that family, not a
  classification of finite representations.
- **Rational nilpotent residual.** The Caprace--Marquis result identifying
  a root kernel with a nilpotent residual over the rationals does not
  establish the displayed universal finite-group assertion over `F_p`.
- **Local torsion.** Known finite quotients inject on every local vertex
  group. Thus a local torsion element cannot be substituted for the
  infinite-order word `w_p` as a finite-residual witness.
- **Regularity gate (obstruction, one invariant for the dead approaches).**
  `kms-hc1-reflected-root-word-regularity-gate` shows that `R=[B,A]` and
  `S=[B,C]` have order dividing `p` and commute with `B`. It then proves
  `w=1` in every image where one of these holds:
  - `<R,S>` is nilpotent of class `<p`;
  - `(R,S)` satisfies the `B_2` vertex relators;
  - the image is nilpotent of class `<=2p-1`;
  - `a,b,c` go to root elements of a Chevalley group in characteristic `p>=7`.

  The exact failing step in the last case is that the pair `theta=-phi` is
  forced to break `[b,c,b]=1`. Both earlier dead families are instances of
  this: positive Kac--Moody images and block matrices with `N^3=0`. Also:
  - metabelian images and `p`-images with `[A,C]=1` kill `w`;
  - abelian layers detect `w` only through `N^ab`;
  - computations: 5-class `<=12` and 7-class `<=14` kill `w`.

  What remains open: a detecting finite image needs `<R,S>` that is neither a
  `Delta_p`-quotient nor of class `<p`. In a `p`-group this means class
  `>=2p`, and it would need a reflected `B_2` relator to survive in the pro-`p`
  completion. Cross-characteristic images are not ruled out.
