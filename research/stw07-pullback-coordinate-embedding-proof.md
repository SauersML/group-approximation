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

No stable-finiteness hypothesis on the coordinates is needed.  The
unitization of a quasidiagonal algebra is quasidiagonal, and every unital
quasidiagonal C-star algebra is stably finite.  Applying these standard facts
to `P` gives stable finiteness after quasidiagonality has been established.

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
quasidiagonality.  Quasidiagonality comes from the injective two-coordinate
map `P -> B direct_sum D`, stable finiteness is then a consequence of
quasidiagonality, and neither comes from `(PB1)`.  The surjectivity hypothesis
is needed for `(PB1)` and the nuclearity argument; without it, an arbitrary
C-star subalgebra of a nuclear direct sum need not be nuclear.  No permanence
assertion is made for infinite pullback products.
