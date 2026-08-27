---
rg: 2
id: cdi-character-rigid-image-bridge-proof
kind: route
title: Apply rigidity to the faithful factor character of the CDI image
target: cdi-character-rigid-image-quotient-is-an-exact-bridge
requires:
  - cdi-property-t-envelope-has-nonabelian-base
---

The representation in `(CIQ1)` descends to a faithful homomorphism
`pi_bar:Lambda->U(Q)`.  Its character

```text
chi_Lambda(g)=tau_Q(pi_bar(g))                           (CIP1)
```

is faithful because `chi_Lambda(g)=1` implies

```text
||pi_bar(g)-1||_2^2=2-2 Re chi_Lambda(g)=0,
```

and hence `g=e`.  It is extremal because its GNS algebra is the factor `Q`.
The inclusion
`M_0 subset Q` makes `Q` non-CE, so `(CIP1)` cannot be one of the
faithful nonregular characters allowed by the hypothesis.  Hence

```text
chi_Lambda=delta_e.                                     (CIP2)
```

The GNS von Neumann algebra of `(CIP2)` is `L(Lambda)`, while the GNS
algebra of `(CIP1)` is `Q`; equality of the characters gives the
trace-preserving isomorphism `(CIQ2)`.  If `Lambda` were hyperlinear,
`L(Lambda)` would be CE, contradiction.

For the kernel warning, a prescribed quotient `q:H->K` receives the CDI
representation only when `ker(q) subset ker(pi)`.  A finite factor has no
nonzero proper weakly closed ideals, so one cannot impose the missing group
relations afterward by taking a nontrivial von Neumann-algebra quotient of
`Q`.  The quotient must already occur at the group-representation level.
