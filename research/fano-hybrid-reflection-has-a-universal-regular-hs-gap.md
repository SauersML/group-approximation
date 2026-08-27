---
rg: 2
id: fano-hybrid-reflection-has-a-universal-regular-hs-gap
kind: claim
title: The Fano hybrid reflection has a universal regular HS gap and a scalar tensor countersector
distinct_from:
  universal-central-selector-word-is-affine-for-any-actor: that proves qualitative affinity for a word assumed scalar on every marked selector atom; this specializes to the uncovered Fano truth table, gives the sharp regular-corner Hilbert--Schmidt gap, and adds the finite-matrix odd-tensor countersector.
  tensor-affine-selector-pattern-barrier: that classifies all scalar selector patterns realized with a fixed phase; this identifies three concrete honest hybrid-reflection sectors whose odd tensor product is the exact wrong-output sector.
  ghost-finite-router-induced-sector-or-perfect-corner: that produces an induced ghost sector for a finite router; this applies to arbitrary infinite ordinary-group, self-similar, Leavitt, and solution-group actors without an induction or finiteness hypothesis.
---

Let `Gamma` be any discrete group with a central involution `J` and containing

```text
D=<J,p,f> isomorphic to (C_2)^3,
```

where `p=1-2P` and `f=1-2F` are the two commuting selector signs. Put

```text
e_-=(1-J)/2,
q=e_- ((1+p)/2) ((1-f)/2),
R=e_- -2q.                                             (FHG1)
```

Thus `R` is the desired hybrid reflection in the marked corner: it is `-1`
exactly on `(P=0,F=1)` and `+1` on the other three joint selector atoms.
For every ordinary group word, viewed as a group element `w in Gamma`, the
canonical trace of `L(Gamma)` satisfies

```text
||e_- w-R||_2^2 >= 1/2.                               (FHG2)
```

Equivalently, for the normalized marked-corner trace `tau_-=2tau`,

```text
||e_- w-R||_(2,tau_-)^2 >= 1.                         (FHG3)
```

The constant is sharp: the constant `+1` word disagrees only on the forbidden
atom. Consequently no ordinary-group presentation gadget, finite or infinite,
can authenticate the exact hybrid identity representation-universally, and
no universal tracial normalized-HS estimate can make its error tend to zero.
HNN, self-similar, Leavitt-derived, and solution-group relations do not alter
this regular-representation obstruction.

There is also a matrix-only obstruction whenever completeness splits into
scalar selector sectors. Suppose the same presentation has finite-dimensional
marked representations realizing the desired scalar output `r=+1` on each
of

```text
(P,F)=(0,0), (1,0), (1,1).                            (FHG4)
```

Their tensor product is another finite-dimensional marked representation and
has

```text
(P,F,r)=(0,1,+1),                                     (FHG5)
```

because three copies preserve `J=-1` and scalar signs multiply. This is the
exact forbidden input with the wrong hybrid output. Hence even an infinite
presentation cannot enforce the table on all finite-dimensional scalar
sectors while retaining the three honest completeness sectors.

The only surviving formulation is necessarily non-universal and
sector-entangled: the normalized-HS theorem must select a special matrix or
canonical-trace class that excludes the regular trace, and its perfect model
must not decompose into independently tensorable scalar `(P,F)`
representations. In particular a successful actuator must keep a non-scalar
operator coordinate across the selector atoms; an infinite actor by itself
is not an authentication mechanism.
---
