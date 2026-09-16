---
rg: 2
id: bootstrap-tensoring-cannot-create-qd-trace-positive-class
kind: claim
title: Tensoring with a unital quasidiagonal bootstrap-class algebra neither creates nor destroys a singular K_0-class positive on quasidiagonal traces
distinct_from:
  qd-nuclear-algebra-with-qd-trace-positive-singular-class: that is the open existence question; this shows that enlarging K_0 by tensoring with a bootstrap-class factor cannot turn a non-witness into a witness.
  stw07-trace-obstruction-forces-nonqd-trace-and-non-uct: that lists necessary consequences of a witness; this is a permanence theorem for witnesses under minimal tensor products.
  qd-trace-positive-class-iff-k0-state-off-qd-traces: that is the algebra-by-algebra K_0-state criterion; this applies it to tensor products through the Künneth theorem and the product form of extreme traces.
artifacts:
  - research/artifacts/qd-trace-positive-class-k0-state-form-2026-09-16.md
---

**Theorem 2 of the artifact.**  Call a separable unital nuclear quasidiagonal
algebra a *witness* if it has `x in K_0` with `Zx cap K_0^+ = {0}` and
`(Tr tensor tau)(x) > 0` for every quasidiagonal tracial state `tau`.

Let `A` and `D` be separable, unital, nuclear and quasidiagonal, with `D` in
the bootstrap class.  Then `A tensor D` is nuclear and quasidiagonal, and it
is a witness if and only if `A` or `D` is.

The proof uses only that the Künneth map
`K_0(A) tensor K_0(D) (+) K_1(A) tensor K_1(D) -> K_0(A tensor D)` has torsion
cokernel.  So the same conclusion holds for any nuclear quasidiagonal `D` with
that property against `A`.

**Consequences** (artifact, Corollary 3.1).  These are remarks, not part of
the statement certified by this node's route.  The first and third rest on
Gabe's theorem, which is not a graph node (abstract of arXiv:1511.02760v1
rechecked 2026-09-16).  For the explicit examples listed, quasidiagonality
of all traces is elementary: extreme traces of `C(X)` are characters, AF
traces are approximated through the finite-dimensional stages, and `Z` and
irrational rotation algebras are quasidiagonal and monotracial (a unital
quasidiagonal algebra has a quasidiagonal trace).  The `Z`-stability
reduction uses only the "if" direction and needs no literature input.

- **Bootstrap factors are never witnesses.**  By Gabe (arXiv:1511.02760v1:
  amenable traces on separable exact quasidiagonal UCT algebras are
  quasidiagonal), every trace of such a `D` is quasidiagonal.  So `D` is not a
  witness, and `A tensor D` is a witness iff `A` is.  This uses Gabe's theorem
  as a literature input.  Examples of such `D`: `C(X)`, UHF and AF algebras,
  `Z`, irrational rotation algebras.  In particular a witness may be assumed
  `Z`-stable and `Q`-stable.
- **Inner crossed products.**  For a unitary `w in A`,
  `A x|_(Ad w) Z ≅ A tensor C(T)`, so this crossed product is a witness iff
  `A` is.
- **Separation cannot be imported.**  Suppose `A` is not a witness but has a
  nonquasidiagonal trace `sigma`.  Then `sigma tensor tau_D` is not
  quasidiagonal, since it restricts to `sigma` on `A tensor 1`.  And
  `A tensor D` is not a witness, by the previous consequence.  Artifact
  Proposition 3 says that if `K_0` separates tracial states, then a
  nonquasidiagonal trace already makes a witness.  So `K_0(A tensor D)` does
  not separate the tracial states of `A tensor D`.  This is why the hole
  `trace-separating-k0-nuclear-qd-algebra-with-nonqd-trace` cannot be reached
  by such tensoring.

Proof: route `bootstrap-tensoring-cannot-create-qd-trace-positive-class-proof`.
