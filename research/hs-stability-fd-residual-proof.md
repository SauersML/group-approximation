---
rg: 2
id: hs-stability-fd-residual-proof
kind: route
title: Exactify canonical microstates and contradict finite-dimensional invisibility of the mark
target: hs-stability-plus-fd-residual-forces-nonhyperlinearity
requires: []
---

Assume for contradiction that `Gamma` is hyperlinear.  Canonical-trace
microstates give tuples `U_n` with relator defect tending to zero and

```text
tr(w(U_n))->tau_Gamma(w)=0,
||w(U_n)-I||_2->sqrt(2),                              (1)
```

because `w!=1`.

Uniform flexible HS stability supplies genuine finite-dimensional
representations `pi_n` after adding or removing `o(dim U_n)` dimensions, with
the generator tuples asymptotically close.  A fixed word is Lipschitz in its
letters, and changing `o(dim U_n)` dimensions changes normalized HS norm by
`o(1)`.  Hence

```text
||pi_n(w)-I||_2->sqrt(2).                              (2)
```

But `(SFR2)` gives `pi_n(w)=I` for every `n`, contradicting `(2)`.

For the final assertion, let `w` lie in the intersection of all finite-index
normal subgroups.  The image of any finite-dimensional unitary representation
of a finitely generated group is finitely generated and linear, hence
residually finite by Mal'cev.  If the image of `w` were nontrivial, a finite
quotient of that image would separate it, contradicting the definition of the
finite residual.  Therefore `(SFR2)` holds.
