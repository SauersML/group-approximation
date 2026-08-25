---
rg: 2
id: ordinary-leavitt-parabolic-atomic-spectrum-proof
kind: route
title: Permute the root-column atoms and exclude every nontrivial finite character orbit
target: ordinary-leavitt-parabolic-atomic-spectrum-is-trivial
requires:
  - affine-whitehead-has-leavitt-quotient-character-face
  - steinberg-cover-fd-triviality
---

The proof uses the full non-semisimple coefficient vertex, rather than the
finite `C_4` Whitehead edge.

First note the following odd-characteristic form of the usual root-kernel
argument.  Every homomorphism from `H=EL_4(R)` to a finite group is trivial.
Indeed, on each additive root subgroup the image is finite, so its additive
kernel is nonzero.  Weyl conjugacy identifies the root kernels, and the spare
index commutator relations make their common kernel a two-sided ideal of
`R`.  The ring `R=M_3(L_2(k))` is simple, so that ideal is all of `R` and all
elementary roots die.  Since they generate `H`, the homomorphism is trivial.
This is the same proof as `steinberg-cover-fd-triviality`, with the exponent
of the root groups changed from two to `char(k)` and with Morita simplicity.

Now let `e` be a minimal projection of the atomic part of `B=pi(N)''`.
Because `B` is abelian, there is a character `chi_e:N->S^1` such that

```text
pi(n)e=chi_e(n)e.                                      (OPA7)
```

The group `H` normalizes `N`, hence `pi(H)` normalizes `B` and permutes its
minimal projections.  Conjugate atoms have the same trace.  The orbit of `e`
must therefore be finite: an infinite orbit would contain infinitely many
pairwise orthogonal projections of the same positive trace in a finite
algebra.  The corresponding action homomorphism from `H` to the finite
permutation group of the orbit is trivial by the preceding paragraph.
Consequently `e` is fixed by `H`, and `chi_e` is `H`-invariant.

There is no nontrivial `H`-invariant character of `N=(R,+)^4`.  For distinct
`i,j<=4`, the elementary transvection `x_ij(r)` sends a column vector `v` to

```text
v+r v_j e_i.                                           (OPA8)
```

Take `v_j=1` and all other coordinates zero.  Invariance of `chi_e` under
`x_ij(r)` gives `chi_e(r e_i)=1`.  Varying `r`, and then `i`, proves that
`chi_e` is trivial.  Equation `(OPA7)` therefore reads `pi(n)e=e` for every
`n in N`.

Summing over all atomic projections proves `(OPA3)`.  Since
`pi(x_15(a_0))-1` vanishes on `z_at`, it is supported on `z_diff`; its operator
norm is at most two, giving `(OPA4)`.

If `B` is atomic, all of `N` dies.  Weyl words in `Q` carry the last-column
roots to every other root, so every elementary root dies and `pi` is trivial.
Finally, the regular root-column algebra is

```text
L(N)=L^infinity(dual(N), Haar),                         (OPA9)
```

which is diffuse because `N` is an infinite elementary-abelian
`char(k)`-group.  This verifies the sharpness statement and prevents any
upgrade that forgets the finite matrix coordinates before controlling their
atom escape.
