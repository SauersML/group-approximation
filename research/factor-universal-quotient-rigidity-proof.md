---
rg: 2
id: factor-universal-quotient-rigidity-proof
kind: route
title: Pull a universal non-CE factor character back across the quotient
target: factor-universal-quotient-of-character-rigid-group-is-faithful
requires:
  - mipstar-equals-re
---

Choose a separable non-Connes-embeddable tracial von Neumann algebra `M`.
Factor universality of `K` gives a trace-preserving embedding

```text
M subset Q=pi(K)'',
```

where `Q` is a finite factor.  Set `rho=pi after q`.  Surjectivity of `q`
gives `rho(G)''=Q`, so this construction for arbitrary `M` first proves that
factor universality pulls back from `K` to `G`.

The character

```text
chi(g)=tau_Q(rho(g))
```

is extremal because its GNS algebra is `Q`.  It cannot come from a
finite-dimensional factor representation: that would make `Q` finite
dimensional, while `Q` contains the non-CE algebra `M`.  Character rigidity
of `G` therefore gives `chi=delta_e^G`.

For every `n in ker(q)` one has `rho(n)=1`, hence `chi(n)=1`.  The regular
character is zero away from the identity, so `chi=delta_e^G` forces `n=e`.
This proves `(FUQ1)`.  Since a surjection with trivial kernel is an
isomorphism, the nonhyperlinearity conclusion also follows from
`factor-universality-character-rigidity-implies-nonhyperlinear` (or directly
from `Q` being the GNS algebra of the regular character).

Finally, a representation of `G` factors through `q` if and only if it kills
`ker(q)`.  Applying this elementary factorization separately to every
universal witness proves the equivalence `(FUQ2)` and shows why rigidity of
the target quotient cannot replace kernel control.
