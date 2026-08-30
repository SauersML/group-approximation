---
rg: 2
id: stw07-pullback-coordinate-embedding-proof
kind: route
title: Use the coordinate embedding for finiteness and quasidiagonality and the extension for nuclearity
target: stw07-surjective-pullbacks-preserve-nuclear-qd-finiteness
requires: []
artifacts:
  - research/artifacts/stw07-status-and-stable-character-reduction-2026-08-30.md
---

The pullback is a closed C-star subalgebra of `B direct_sum D`.  Finite direct
sums of quasidiagonal algebras are quasidiagonal, and quasidiagonality passes
to C-star subalgebras.  Hence `P` is quasidiagonal.

Stable finiteness is inherited by the same coordinate embedding.  In the
unital case, a proper matrix isometry in `P` would remain a proper isometry
in a matrix algebra over `B direct_sum D`, contradicting stable finiteness of
the two coordinates.  If `P` is nonunital, the inclusion extends injectively
to minimal unitizations,

```text
(b,d)+lambda 1  |->  (b,d)+lambda 1_((B direct_sum D)~).
```

The unitization of a finite direct sum of stably finite algebras is stably
finite, so the same matrix-isometry argument applies.  This is the standard
proof that stable finiteness passes to C-star subalgebras.

The one-sided surjectivity is used to retain nuclearity.  Projection to the
second coordinate is onto: for `d in D`, choose `b in B` with
`phi(b)=psi(d)`.  Its kernel is canonically `ker(phi)`, giving

```text
0 -> ker(phi) -> P -> D -> 0.                         (PB1)
```

The ideal `ker(phi)` is nuclear because `B` is nuclear, and `D` is nuclear by
hypothesis.  Nuclearity is closed under extensions, so `(PB1)` makes `P`
nuclear.  Closed subalgebras and pullbacks of separable algebras are
separable.  This proves the single-node theorem, and induction on the number
of internal nodes proves the finite-tree statement.

For the advertised leaves, Gabe's [*Traceless AF embeddings and unsuspended
E-theory*](https://arxiv.org/abs/1804.08095), Theorem C, makes every separable
exact traceless stably finite algebra AF-embeddable, hence quasidiagonal.
Nuclearity supplies exactness.  For the second type, the faithful-trace UCT
theorem of Tikuisis--White--Winter together with Schafhauser's AF-embedding
upgrade makes the algebra AF-embeddable, hence quasidiagonal.  The single-node
result and induction now apply to an arbitrary mixture of the two leaf types.

**Trust boundary.**  This is not general extension permanence of
quasidiagonality.  Quasidiagonality and stable finiteness come from the
injective two-coordinate map `P -> B direct_sum D`, not from `(PB1)`.  The
surjectivity hypothesis is needed for `(PB1)` and the nuclearity argument;
without it, an arbitrary C-star subalgebra of a nuclear direct sum need not be
nuclear.  No permanence assertion is made for infinite pullback products.
