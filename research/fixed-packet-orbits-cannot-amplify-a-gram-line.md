---
rg: 2
id: fixed-packet-orbits-cannot-amplify-a-gram-line
kind: claim
title: A fixed packet orbit cannot amplify one invariant Gram vector to positive density
distinct_from:
  paz-gram-vector-is-not-a-graph-projection: that separates the Gram vector, its rank-one projection, and its positive-density left support; this rules out the most direct finite-packet and finite gauge-orbit repairs of that separation.
  gauge-pair-holonomy-needs-one-source-moment: that constructs a finite gauge-pair orbit and isolates a missing source moment; this proves that orbit covariantization alone cannot create macroscopic coherent source rank.
  hecke-dilations-do-not-lock-capacity-gram: that audits finite monomial dilations and the primitive-type source deficit; this gives a spectral family showing why a fixed finite dilation cannot turn a single fixed vector into a positive-density fixed module.
---

The PAZ exact witness gives one invariant Gram vector

```text
Wg=g.                                                   (FPO1)
```

A natural repair of the graph type mismatch is to tensor with a fixed finite
packet, take a finite gauge orbit of `g`, and use its span as the graph
source.  This cannot produce positive normalized density.  The obstruction
is not peculiar to a chosen packet: a Gram unitary can have a fixed space of
vanishing adjoint density, and a fixed finite spectral menu cannot change
that asymptotic.

## Finite orbit span bound

Let `F` be a fixed finite-dimensional packet and let
`v_1,...,v_s` be any fixed finite list of packet/gauge words.  Starting from
one vector `g in K`, every covariantized vector of the form

```text
v_a(f tensor g)                                        (FPO2)
```

lies in a space of dimension at most `s dim(F)`.  Hence its orbit projection
in `F tensor K` has normalized trace at most

```text
s/dim(K).                                              (FPO3)
```

For the Gram Hilbert space `K=L^2(M_d)`, this is `s/d^2`.  Finite direct
sums, gauge doubling, and tensoring by a fixed packet multiply numerator and
denominator by fixed constants and do not repair `(FPO3)`.

This already rules out the literal proposal “covariantize the invariant
Gram vector by a finite packet orbit.”  There is a stronger spectral
version which also rules out choosing the whole fixed space of any finite
menu of packet-twisted returns.

## Fixed spectral menu theorem

### Theorem

Fix a finite-dimensional Hilbert space `F` and finitely many packet
unitaries

```text
T_1,...,T_s in U(F).                                   (FPO4)
```

For arbitrarily large `d` there is a diagonal unitary `D_d in U(d)` such
that, for

```text
K_d=L^2(M_d),
W_d=Ad(D_d),                                           (FPO5)
```

the Gram vector `I_d` is fixed exactly, but for every `a`

```text
dim Fix(W_d tensor T_a)<=d dim(F).                     (FPO6)
```

Consequently every projection `E_a` satisfying

```text
(W_d tensor T_a)E_a=E_a                               (FPO7)
```

has normalized operator trace at most `1/d`.

### Proof

Let `Sigma` be the finite union of the spectra of the `T_a`.  Choose
distinct phases `lambda_1,...,lambda_d` recursively so that

```text
lambda_i conjugate(lambda_j) notin Sigma^(-1)
                                                     (i!=j). (FPO8)
```

There are only finitely many forbidden choices at each step.  Put
`D_d=diag(lambda_1,...,lambda_d)`.  The matrix unit `E_ij` is a
`W_d`-eigenvector with eigenvalue

```text
lambda_i conjugate(lambda_j).                          (FPO9)
```

By `(FPO8)`, no off-diagonal `E_ij tensor f` is fixed by
`W_d tensor T_a`.  On the diagonal subspace the `W_d` eigenvalue is one, so
the fixed space has dimension

```text
d dim ker(T_a-I)<=d dim(F).                            (FPO10)
```

The ambient dimension is `d^2 dim(F)`, proving `(FPO6)--(FPO7)`.  Finally

```text
W_d(I_d)=I_d,                                          (FPO11)
```

so the original Gram return is perfect.  ∎

The same proof handles a fixed finite direct sum of packet twists: collect
all of their spectra into `Sigma`.  It also handles a finite gauge orbit,
because its permutation/monomial matrices have one fixed finite spectral
set.

## What the theorem does and does not rule out

The theorem does not say that an exact infinite HALT representation cannot
have an infinite `W`-fixed module.  Countable amplification may provide one,
and completeness is allowed to use it.  It says that no **fixed finite
packet orbit of the one Gram vector** proves the finite positive-density
clause needed by the graph return.

Nor does selecting a primitive packet type by canonical trace solve the
problem.  Canonical trace can give that type positive Plancherel mass, but
the packet projector is then unrelated to the `W`-fixed Gram line.  Imposing
only commutation makes the type `W`-invariant, not pointwise fixed.  The
finite-spectrum models `(FPO5)` still let its eigenvalue-one part have
vanishing relative density.

## Minimal surviving mixed corner

Let `q` denote the capacity-selected packet projection.  The exact relation
which would bridge the gap is the Hecke corner identity

```text
q(W_game-I)=0,                                         (FPO12)
```

together with a finite-matrix decoder proving

```text
Tr_norm(q)>=gamma tau(Q)-o(1).                         (FPO13)
```

Equation `(FPO12)` supplies exact HALT coherence and `(FPO13)` supplies the
finite positive density.  Once both hold, the graph involution is
unnecessary: the strict NO compression already contradicts a nonzero `q`.
But `(FPO12)` is additive Hecke syntax, not an ordinary group-word relation.
Writing

```text
V=qW_game+(1-q)                                        (FPO14)
```

and asking for `V=1` only renames the same missing corner compiler.  A group
letter for `V` must be forced to equal that Hecke sum on the selected type;
finite covariance relations merely preserve the type and do not force the
identity action there.

The exact HALT firewall is sound: use the perfect Gram line, or its
countably infinite amplification, as the `q` corner.  The regular firewall
requires `(FPO13)` to be a finite-matrix/canonical-coordinate conclusion,
not a universal tracial inequality.  Otherwise the same corner equation
would hit the regular representation and algebraically collapse the mark.

Thus fixed packet covariantization does not repair PGP18.  The smallest
surviving target is a capacity-gated ordinary-word realization of the one
Hecke corner `(FPO12)`, with finite-only density `(FPO13)` and an exact
properly infinite HALT extension.
