---
rg: 2
id: projective-label-pullbacks-have-conjugate-stationary-absorbers
kind: claim
title: Every projective label pullback has a conjugate stationary absorber
distinct_from:
  finite-clifford-cocycles-cancel-on-conjugate-multiplicity: that is the order-32 Pauli/Clifford instance; this is the packet-independent theorem.
  inner-pauli-occurrence-labels-are-tietze-removable: that uses an inner group-valued gauge; this applies to arbitrary finite-dimensional projective label systems.
---

# Every projective label pullback has a conjugate stationary absorber

ESTABLISHED. Let `Lambda` be a group, let

```text
C: Lambda -> U(V),
C_g C_h = c(g,h) C_(gh)                                  (PA1)
```

be any finite-dimensional unitary projective representation, and let
`P=<x_i | w in R>` be any group presentation. Suppose labels
`ell_i in Lambda` satisfy every defining word:

```text
w(ell_1,...,ell_n)=1       for every w in R.              (PA2)
```

Then

```text
T_g=C_g tensor conjugate(C_g)                             (PA3)
```

is an honest representation of `Lambda`, because the cocycles `c` and
`conjugate(c)=c^{-1}` cancel. Consequently, for every unitary representation
`x_i -> Y_i` of `P`,

```text
x_i -> T_(ell_i) tensor Y_i                               (PA4)
```

is another exact representation of `P`. Its dimension overhead is the fixed
factor `(dim V)^2`, independent of the presentation size.

The same statement holds for a finite packet represented irreducibly on `V`
when the `C_g` normalize the packet: `(PA4)` implements the prescribed label
action on the first copy of `V`, while the conjugate copy lies in the
multiplicity space and cancels every projective phase.

Thus any single-occurrence finite-packet construction in which each logical
occurrence receives one projective label and every relator is pulled back
from a locally satisfied label relation has a stationary tensor escape. It
cannot improve the soundness, dimension requirement, or same-Hilbert
roundability of the original presentation.

The minimal way to leave hypothesis `(PA2)` is a closed relator whose label
word has nontrivial scalar holonomy. Such a relator survives `(PA3)` only as
an affine scalar equation on the multiplicity word. This does not yet evade
the stronger normalizer scalar-reduction theorem below.

