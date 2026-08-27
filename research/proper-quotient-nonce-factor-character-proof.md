---
rg: 2
id: proper-quotient-nonce-factor-character-proof
kind: route
title: Pull one non-CE factorial character through the quotient and evaluate it on the kernel
target: proper-quotient-nonce-factor-characters-are-ce
requires: []
---

Let `q:G -> K` be surjective and let `theta` be an extremal character of
`K`.  Write `(pi_theta,H_theta,xi_theta)` for its GNS representation and

```text
Q=pi_theta(K)''.
```

The pullback `chi=theta after q` has GNS von Neumann algebra `Q`: indeed,
surjectivity gives

```text
(pi_theta after q)(G)'' = pi_theta(K)''.
```

Hence `chi` is extremal whenever `theta` is.  If `Q` is non-Connes
embeddable, `chi` cannot be the character of a finite-dimensional factor
representation, because the GNS von Neumann algebra of a character is
determined by the character and a finite-dimensional factor character has
finite-dimensional GNS algebra.  Character rigidity of `G` therefore gives

```text
chi=delta_e^G.                                           (PQF1)
```

For `n in ker(q)`, however,

```text
chi(n)=theta(e)=1.
```

Equation `(PQF1)` is zero at every nonidentity element, so `n=e`.  Thus
`ker(q)={e}`.  Since `q` is already surjective, it is an isomorphism.  If
`k!=e` and `q(g)=k`, injectivity makes `g!=e`, and `(PQF1)` also gives

```text
theta(k)=chi(g)=0.
```

Thus `theta=delta_e^K`.  Its non-CE GNS factor is `L(K)`, proving that `K`
is nonhyperlinear.

Taking the contrapositive proves that every extremal character of a proper
quotient has CE GNS factor.  The split-extension, wreath, and retraction
consequences use only that their displayed projections are surjective with
the stated nontrivial kernel.  The relative-rigidity observation follows
from `chi(n)=1` for every `n in ker(q)`: the obstruction belongs to the
quotient face and is invisible to hypotheses that classify only characters
nontrivial on the kernel.
