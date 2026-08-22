---
rg: 2
id: canonical-iwahori-projection-commutant-transfer
kind: claim
title: Canonical Iwahori microstates transfer positive-density projection centralizers between the two vertices
distinct_from:
  iwahori-unitary-commutant-transfer: that asks for a modulus over every pair of exact finite-dimensional vertex representations and every unitary; this is its canonical projection formulation, but residual-finite regular tensor camouflage proves the two are equivalent rather than genuinely weaker.
  iwahori-local-global-defect-question: that repairs arbitrary almost-compatible vertex representations to a compatible representation; this neither repairs the representations nor treats noncanonical characters.
---

OPEN.  Put

```text
A=SL_2(Z[1/2])=C_+ *_(B_+=B_-) C_-,
C_+=C_-=SL_2(Z),
```

with the index-three Iwahori edge isomorphism `sigma`.  Let
`pi_(n,+),pi_(n,-):C -> U(d_n)` be exact representations whose edge defects
tend to zero.  Evaluate fixed amalgam normal forms using these two
representations, obtaining asymptotic homomorphisms `Phi_n:A->U(d_n)`, and
assume the canonical trace condition

```text
tr_(d_n)(Phi_n(g)) -> delta_(g,1)       for every g in A.             (CIP1)
```

Prove that every sequence of projections `p_n in M_(d_n)` satisfying

```text
max_(c in S_C)||[p_n,pi_(n,+)(c)]||_2 ->0                            (CIP2)
```

also satisfies

```text
max_(c in S_C)||[p_n,pi_(n,-)(c)]||_2 ->0.                           (CIP3)
```

It is enough to prove this when
`min(tr(p_n),1-tr(p_n))` is bounded below:
`iwahori-transfer-failure-reduces-to-two-block-projection` replaces every
unitary failure by a projection failure after harmless doubling, and
`iwahori-transfer-failure-has-two-positive-density-blocks` proves that both
blocks then have uniformly positive normalized rank.

In a tracial matrix ultraproduct, `(CIP1)` says that the induced homomorphism
extends to a trace-preserving embedding `L(A)->M_omega`.  The endpoint is the
lift-conditioned relative-commutant assertion

```text
rho(C_+)' intersect M_omega = rho(A)' intersect M_omega              (CIP4)
```

tested only on projections and only for embeddings whose two vertex
restrictions lift to exact matrix representations.  This is strictly weaker
than arbitrary Iwahori repair.  It is **not** weaker than
`iwahori-unitary-commutant-transfer`: by
`canonical-iwahori-transfer-is-equivalent-to-full-transfer`, every arbitrary
failure can be tensor-camouflaged into this canonical sector.

## Exact remaining carrier

A counterexample must now exhibit projections of positive normalized rank
and corank which are asymptotically reducing for the first exact vertex but
are mixed by the second vertex by a fixed amount, while the two Iwahori edge
representations agree asymptotically and the amalgam character remains
regular.  Vanishing-rank outliers, scalar multiplicity unitaries, and
noncanonical finite-dimensional characters cannot refute this endpoint.

`canonical-iwahori-failure-is-a-regular-square-root-odd-mode` gives the exact
coordinate form.  In the tracial matrix ultraproduct the two vertices are
`(X^2,Y)` and `(X,Y^2)` with matched central word, and the positive-density
projection commutes with `X^2,Y` but not `X`.  Equivalently the obstruction
is one macroscopic selfadjoint mode negated by `Ad_X` inside the canonical,
vertex-liftable correspondence.  Proving that this odd mode vanishes is now
exactly the canonical endpoint; no all-character Iwahori repair is needed.

There can be no purely tracial or relation-theoretic proof of that
vanishing.  By `iwahori-square-root-odd-mode-is-amalgam-bending`, every
unitary in the first commutant bends the second vertex while preserving all
amalgam relations.  In particular the left regular representation of

```text
<A,t | [t,C_+]=1>
```

contains the exact bending unitary `t`.  The desired contradiction must say
that this bending correspondence cannot be realized by the specified exact
vertex lifts inside a **tracial matrix ultraproduct**.  That is precisely the
finite-coordinate asymmetry whose proof would establish nonhyperlinearity.

Scalar regularity itself supplies no extra leverage.  The tensor camouflage
lemma preserves the whole relative-commutant obstruction while forcing all
nonidentity amalgam traces to zero.  Any proof must therefore control the
matrix-coordinate bending/multiplicity geometry, not classify the limiting
character.

`iwahori-projection-overlap-is-a-spherical-coefficient` compresses that
geometry to one scalar.  For `t_n=tr(p_n)` and a fixed second-vertex unitary
`U_n`, transfer is exactly

```text
tr(p_n U_n p_n U_n^*) -> t_n.
```

Equivalently the normalized centered-projection spherical coefficient tends
to one.  `canonical-trace-square-is-blind-to-iwahori-overlap` shows why the
canonical character cannot force this: it controls the average trace over
all `d_n^2` adjoint directions, while the obstruction is one selected odd
direction.  The exact remaining scalar terminal is
`canonical-iwahori-one-hecke-overlap-saturates`.

## Full-HNN conditioning does not bypass the action fork

One might try to exploit the extra hypothesis actually present in the HNN
contradiction: the bending unitary and the base tuple jointly have the
canonical trace of the full group `<A,t | [t,C_+]=1>`.  This is genuinely
stronger than `(CIP1)`: an ordinary Bernoulli lamp makes distinct conjugate
lamps commute, whereas Britton normal form makes them free.

Nevertheless `sl2-centralizer-hnn-is-free-coset-wreath` identifies this full
HNN group with the free generalized wreath product

```text
Z wr^*_(A curvearrowright A/C_+) A.
```

Therefore `sofic-dyadic-action-produces-full-hnn-iwahori-countermodels`
shows that soficity of the dyadic vertex action gives positive-density
projection failures even with all full-HNN moments imposed.  Any successful
proof through this HNN must, at minimum, exclude those free-wreath
microstates; equivalently, it must prove a new nonsoficity theorem for the
Bruhat--Tits vertex action.  Full canonical conditioning is a useful
narrowing of the finite-coordinate target, but it is not a route around the
tree-action soficity/P-instability fork.
