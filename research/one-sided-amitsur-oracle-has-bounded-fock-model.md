---
rg: 2
id: one-sided-amitsur-oracle-has-bounded-fock-model
kind: claim
title: The one-sided Amitsur oracle has a bounded Fock representation and a unit matrix gap
distinct_from:
  two-generator-amitsur-levitzki-dimension-oracle: that adjoins two-sided formal inverses and proves only algebraic nonzeroness through the free skew field; this observes that one left inverse is enough and realizes every instruction by bounded operators on one Hilbert space.
  amplification-natural-words-cannot-read-packet-multiplicity: that rules out reading anonymous spectator multiplicity with a fixed authenticated word; this is a moving, dimension-matched algebra instruction and does not claim a finite word compiler.
  dimension-reported-julia-amplitude-return: that asks for the finite constant-HS controller carrying the detected instruction to the Julia return; this supplies its bounded infinite nontriggered model and exact finite-dimensional semantic floor, not that controller.
---

ESTABLISHED.  Let `F_2^+` be the free monoid on the two letters `x,y`, let
`L_x,L_y` be its left creation isometries on full Fock space, and put

```text
u_j=x y^j x,
p_n=s_(2n)(u_1,...,u_(2n)).                              (OAF1)
```

It is enough to adjoin **one** inverse relation per instruction.  The
countably presented unital star algebra

```text
A_left=<x,y,q_1,q_2,... | q_n p_n=1  (n>=1)>             (OAF2)
```

has a bounded star representation on one Hilbert space, but has no unital
finite-dimensional representation.

Indeed the words

```text
w_j=x y^j x                                                (OAF3)
```

form a prefix code.  Hence, for fixed `n`, the `(2n)!` concatenations

```text
w_(sigma(1)) ... w_(sigma(2n)),       sigma in S_(2n),     (OAF4)
```

are again prefix-incomparable.  Their left creation operators have pairwise
orthogonal ranges.  Therefore the Fock evaluation satisfies

```text
p_n^*p_n=(2n)! I.                                         (OAF5)
```

Taking

```text
q_n=((2n)!)^(-1) p_n^*                                   (OAF6)
```

gives `q_n p_n=I`, with

```text
||p_n||=sqrt((2n)!),       ||q_n||=1/sqrt((2n)!).          (OAF7)
```

Thus all countably many instructions coexist as bounded operators; no free
skew-field inverse or unbounded affiliated operator is used.

On the other hand, for arbitrary matrices `X,Y in M_d(C)`,
Amitsur--Levitzki gives

```text
p_d(X,Y)=0.                                                (OAF8)
```

Consequently every attempted unital `d`-dimensional realization, with any
matrix chosen for `q_d`, has the exact normalized-Hilbert--Schmidt floor

```text
||q_d p_d-I||_(2,d)=1.                                    (OAF9)
```

The oracle therefore already has the two semantic properties wanted from a
self-indexing finiteness detector: a single bounded infinite model in which
every instruction is inactive, and a unit defect at the instruction indexed
by the ambient finite dimension.

This does not yet produce a non-hyperlinear group.  The index `d` moves with
the matrix model, the standard polynomial is additive and has growing word
mass, and a fixed finite group presentation still has to PCP-localize the
moving unit defect and transport it to a fixed marked carrier.  The gain is
sharp: bounded HALT completeness and the finite-dimensional semantic gap are
no longer part of that compiler problem.

