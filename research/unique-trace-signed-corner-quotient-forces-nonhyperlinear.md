---
rg: 2
id: unique-trace-signed-corner-quotient-forces-nonhyperlinear
kind: claim
title: A unique-trace signed group corner surjecting onto a non-CE tracial algebra forces nonhyperlinearity
distinct_from:
  regular-trace-blocks-exact-local-predicate-return: that obstructs a trace-functorial forbidden-mass payment in the regular representation; this uses the regular signed-corner trace positively and identifies it with a non-CE quotient trace.
  nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear: that treats a unital map from the non-CE algebra into the corner and pulls back the canonical trace, requiring no uniqueness; this treats the opposite map direction, a corner quotient onto the non-CE algebra, where uniqueness is what identifies the quotient trace.
---

Let `Gamma` be a countable group and let `q in C[Gamma]` be a nonzero central
projection.  Write

```text
A=q C^*(Gamma) q,
tau_q(a)=tau_Gamma(a)/tau_Gamma(q).                   (USQ1)
```

Assume:

1. `tau_q` is the unique tracial state of `A`;
2. there is a unital surjective `*`-homomorphism

```text
Phi:A -> B;                                           (USQ2)
```

3. `B` has a tracial state, but no Connes-embeddable tracial state.

Then `Gamma` is not hyperlinear.

Indeed, choose a tracial state `sigma` on `B`.  The pullback `sigma Phi` is a
tracial state on `A`, hence uniqueness gives

```text
sigma Phi=tau_q.                                      (USQ3)
```

Because `Phi` is surjective, `(USQ3)` identifies the two GNS von Neumann
algebras:

```text
pi_(tau_q)(A)'' isomorphic to pi_sigma(B)''.          (USQ4)
```

More explicitly, `Phi` maps the `tau_q`-null ideal onto the `sigma`-null
ideal and induces an isometry of the dense GNS quotients; surjectivity makes
the induced map onto, and taking bicommutants gives `(USQ4)`.

If `Gamma` were hyperlinear, its canonical trace would be Connes embeddable.
Connes embeddability passes to the positive central corner `(A,tau_q)`, so
`(USQ4)` would make `sigma` Connes embeddable, contrary to assumption 3.

The criterion is deliberately a **quotient** theorem.  A corner embedding of
`B` is sufficient but unnecessarily strong.  Uniqueness of the source trace
reverses the usual trace-control problem: every quotient trace has the one
canonical pullback, and a quotient therefore has the same GNS algebra for
that trace.

### Character-rigidity sufficient condition

Suppose `q` is the central block projection of a finite normal subgroup
sector.  Tracial states on `A` correspond to normalized characters of
`Gamma` supported on that sector.  Hence hypothesis 1 follows if every
extremal character in the sector is either

```text
the canonical q-regular character
```

or comes from a finite-dimensional representation, and no
finite-dimensional representation of `Gamma` contains the selected finite
subgroup type.  This is the precise interface between higher-rank character
rigidity, central-extension finite-dimensional collapse, and the signed-Hecke
BCS compiler.
