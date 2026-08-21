---
rg: 2
id: first-leavitt-weyl-cell-rectangular-proof
kind: route
title: Put the source Weyl pair on one tensor factor and swap it to the second child
target: first-leavitt-weyl-cell-has-exact-rectangular-model
requires: []
---

The identities `(FWC3)` follow immediately from the Weyl relation and from

```text
SWAP (T tensor 1) SWAP^* = 1 tensor T.
```

The Pauli trace statement follows because every nonidentity Weyl monomial
has trace zero.  The first pair acts irreducibly on the first tensor factor
and trivially on the second, whereas the two commuting pairs generate the
two tensor factors and hence all of `M_(p^2)`.

For `(FWC4)`, Amitsur--Levitzki says that `s_(2p)` is an identity of `M_p`
but not of `M_(p^2)`.  Choose a tuple in `M_(p^2)` with nonzero evaluation
and expand every entry in the two-qudit Pauli basis.  Multilinearity implies
that at least one tuple of Pauli basis words has nonzero evaluation.

Finally, the alternating polynomial has `(2p)!` monomials.  Telescoping a
product of `2p` contractions shows that changing every input by at most
`delta` in normalized Hilbert--Schmidt norm changes the polynomial by at
most

```text
2p (2p)! delta.
```

If the approximating tuple lies in `M_p tensor 1`, its polynomial is zero,
which proves `(FWC5)`.
