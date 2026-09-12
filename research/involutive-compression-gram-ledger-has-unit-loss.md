---
rg: 2
id: involutive-compression-gram-ledger-has-unit-loss
kind: claim
title: The positive involutive compression ledger is sharp at unit recurrence loss
distinct_from:
  toeplitz-child-section-loses-square-or-exit: that gives the general not-necessarily-positive cross term for a unitary loop; this uses an involution to make the leakage positive and computes the resulting branch coefficient.
  central-square-orients-transverse-ledger: that gives a sharp half-loss for a raw unitary holonomy; this proves that its hypothesis and positive proper-corner leakage are mutually exclusive except at zero leakage.
  transverse-companion-defects-pay-one-kill-completeness: that gives a positive aggregate defect from two transverse returns; this tests the single involutive Toeplitz compression against the binary branch-mass identity.
---

# The positive involutive compression ledger is sharp at unit recurrence loss

ESTABLISHED. Let `h=h^*=h^-1`, let `p` be the selected Toeplitz child cut,
and put `W=php`. Then `W=W^*` and the compression identity becomes the
positive Gram decomposition

```text
p=W^2+L,       L=p h(1-p)h p=((1-p)hp)^*((1-p)hp)>=0.   (ICG1)
```

Thus

```text
tau(L)=||(1-p)hp||_2^2=tau(p)-||W||_2^2.                (ICG2)
```

This is the strongest positivity obtainable from the ordinary square word.
It does **not** charge the unused Toeplitz child. If `e` is the complementary
child projection, the binary head gives equal branch multiplicities, but
there is no inequality

```text
tau(e) <= C tau(L)+C E_rel                                (ICG3)
```

from the head, involution, and square relations, where `E_rel` is their group
relator energy. Indeed take the stationary finite packet type vector, let the
closed multiplicity return be the identity on the selected child, and retain
the other child as an independent reducing summand. Then

```text
h=I,       W=p,       L=0,       E_rel=0,       tau(e)>0. (ICG4)
```

At the local operator level this is already the block model
`P=Q=1`, `Q=p+e`, `t=1`, `h=1`, with `tau(p)=tau(e)=1/2`; the regular
stationary type-flow theorem supplies the corresponding simultaneous finite
packet multiplicities. Direct sums and amplifications preserve `(ICG4)`.

The coefficient ledger explains the failure. Restricting one full Schur
input to two children contributes a factor `1/2` to the selected branch, but
returning that child as the next full input restores the factor `2`. On the
stationary multiplicity ray the product is

```text
(1/2)*2=1.                                                (ICG5)
```

Since `(ICG4)` makes the new positive Gram term vanish, every inequality
deduced from these data of the form

```text
a <= c a + C E_rel                                      (ICG6)
```

must have `c>=1`. There is no hidden strict contraction.

The sharp half-loss in `central-square-orients-transverse-ledger` cannot be
added to improve `(ICG5)`. That theorem assumes the raw corner holonomy is
unitary. Here corner unitarity is equivalent, by `(ICG1)` and its range
analogue, to `L=0` and reduction of `p` by `h`; it is exactly the spectator
case `(ICG4)`. If `L>0`, the compression is not unitary and the real/skew
unitary conservation law used by the central-square theorem is unavailable.
Applying its constant `1/2` to such a compression would count an assumption
which has already discarded the positive leakage.

Conversely, forcing `h` to exchange the selected and complementary children
makes `L=p` and detects all branch mass, but then `p,e,hp` are full matrix
units. This is the established branch-flip Morita cancellation and again
does not give a one-sided recurrence compatible with the marked model.

Therefore positivity of the involutive leakage is not the missing
finite-matrix correction. A successful correction must correlate the
Toeplitz complement with `L` by an additional mixed, finite-dimensional-only
support test. The current branch identity and central square stop sharply at
coefficient one.
