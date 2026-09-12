---
rg: 2
id: finite-selector-cannot-support-infinite-child-fixedness
kind: claim
title: A finite nonlinear selector cannot support exact fixedness by an infinite self-copy child
distinct_from:
  finite-reynolds-carriers-have-only-finite-pointwise-stabilizer: That computes the literal fixed stabilizer of a finite Reynolds coefficient; this strengthens it to projective stabilizers and applies it to the Reynolds--Pauli selected atom and finite-quotient kernel localization.
  left-rank-amplification-is-not-a-fixed-sector: That separates invariant physical rank from pointwise adjoint fixedness in matrices; this proves that upgrading invariance to the needed exact fixedness collapses the infinite child algebraically.
  packet-covariant-kernel-gauge: That constructs large finite multiplicity gauges after packet covariance; this gives the preceding exact dichotomy before choosing any multiplicity model.
---

**ESTABLISHED SELF-COPY FIREWALL.**  If `0!=z in C[G]` has finite support,
its projective left stabilizer

```text
PStab_L(z)={g in G: gz in C^* z}                         (PSC1)
```

is finite.  Indeed `gz=lambda z` implies
`g supp(z)=supp(z)`.  Left translation gives an injective action of
`PStab_L(z)` on the finite set `supp(z)`: an element fixing one support point
is the identity.  The same conclusion holds for a finite-dimensional span of
finite-support coefficients after replacing the support by their finite
union.

Now take one shared-BCS forbidden atom and its one-bit Clifford selector:

```text
A=e_(H_a) Q_- (1+p_a)/2.                                (PSC2)
```

If the finite context/selector packet embeds, then `A` is a nonzero
finite-support group-algebra projection; in the canonical trace it has the
positive Plancherel mass computed by the finite packet.  Let `L` be an
infinite finitely generated group with a proper injective self-copy
`alpha(L)=tLt^(-1)<=L`.

Any exact conditional fixedness rows strong enough to make the child act by
scalars on the selected physical carrier,

```text
(alpha(s)-lambda_s)A=0                (s in a generating set of L), (PSC3)
```

force `alpha(L)<=PStab_L(A)`, hence force the child to be finite.  Likewise,
if `N` is an infinite kernel of a finite packet quotient, the localization

```text
(n-1)A=0                              (n in N)           (PSC4)
```

forces `N` into the finite stabilizer of `A`.  Thus exact localization of an
infinite quotient kernel on the Reynolds--Pauli atom either makes `A=0` in
the group algebra or destroys injectivity of the self-copy.

The only noncollapsing ordinary alternative is covariance/normalization:

```text
alpha(s) A alpha(s)^(-1)=A.                             (PSC5)
```

But `(PSC5)` makes the positive-rank left-multiplication carrier invariant,
not pointwise fixed under the adjoint action.  On a packet isotypic block the
child matrices have Schur form

```text
pi(alpha(s)) tensor W_s,                                (PSC6)
```

and the arbitrary multiplicity action `W` remains.  Its commutant density
can tend to zero in finite regular gauges, exactly as in
`packet-covariant-kernel-gauge`.

Therefore a direct infinite-tail coupling has a sharp dichotomy:

```text
exact child fixedness on A  => child collapses (or A=0),
packet covariance of A      => no positive-density fixed adjoint sector.   (PSC7)
```

Iterating the proper self-copy does not alter the first step of `(PSC7)`.
The Pauli selector solves nonlinear atom naming but remains finite support,
so it cannot conditionalize an infinite child kernel.  A viable self-copy
amplifier must produce an approximation-dependent macroscopic fixed
projection not equal to a fixed finite group-algebra carrier, using a
matrix-only global payload relation.  Finite Reynolds/Clifford coefficients
and exact self-copy covariance cannot do it.

DERIVATION
finite-selector-projective-stabilizer-proof
