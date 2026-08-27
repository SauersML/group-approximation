---
rg: 2
id: evaluate-the-tree-fourier-defect-on-the-trivial-source-block
kind: route
title: Evaluate the subgroup Fourier defect on the trivial source block and pull it back to augmentation
target: positive-tree-choi-gap-does-not-force-ideal-support
requires:
  - positive-tree-separator-has-fd-low-ideal-moment-packets
---

For subgroups `L<=H<=Lambda`, the subgroup Fourier expectation satisfies

```text
M_L(u_h)=u_h if h in L,       M_L(u_h)=0 otherwise.        (1)
```

Because `H intersect P_13=L`, restricting `M_(P_13)` to `C^*(H)` gives
`M_L`, proving `(ATF1)`.

The projection `p_H` is the identity of the one-dimensional trivial summand
in the Wedderburn decomposition of `C^*(H)`.  Its image under the expectation
is

```text
M_L(p_H)=|H|^(-1) sum_(l in L)u_l
         =(|L|/|H|)p_L.                                   (2)
```

The Choi algebra of a direct sum contains one output copy of `Q` for this
one-dimensional source block.  Define `Omega_aug` to be zero on all other
blocks and to equal `epsilon` on this copy of `Q`.  It is a positive state.
Using `epsilon(p_H)=epsilon(p_L)=1`, equation `(2)` gives

```text
Omega_aug(C_(D_H))
 =epsilon(p_H-(|L|/|H|)p_L)
 =1-|L|/|H|,                                               (3)
```

which is `(ATF2)`.

The augmentation of `Q=C^*(Lambda)` composed with
`q:C^*(G_0)->>Q` is the augmentation of `C^*(G_0)`.  Hence the pullback of
`Omega_aug` is already a finite-dimensional vector state: the trivial
one-dimensional representation.  It vanishes on `ker q`, so its ideal
support is zero.

Finally `E_epsilon` is ucp, fixes the unit, and
`epsilon((id-E_epsilon)(x))=0` for every `x`.  Therefore `(ATF3)` is both
unital-zero and augmentation-zero and its `Omega_aug` value is zero, proving
`(ATF4)`.  Since the original value `(3)` is positive, no estimate depending
only on positivity and that value can survive universal post-centering.

In the positivization theorem one adds a functional of the form
`lambda(psi(1))`.  Since `D_H(1)=0`, that addition has zero value on `D_H` and
cannot distinguish whether `(3)` came from augmentation or from a nontrivial
quotient representation.  This proves the stated firewall for that
conversion as well.
