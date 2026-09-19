---
rg: 2
id: matrix-conj-forces-unsafe-support
kind: claim
title: A harmless finite matrix conjunct can force affine-unsafe support in every perfect trace
distinct_from:
  nonaffine-relation-alone-cannot-force-affine-safe-factor-support: that gives an extreme full-support trace on two disjoint copies of an arbitrary relation; this gives a connected contextual block with a unique tracial state and then adjoins it to a tracial non-RU BCS.
  extreme-traces-and-local-pruning-do-not-select-fano-caps: that rules out extremality and pairwise pruning separately; this rules out every trace-selection rule, including global support minimality, because the bad block has only one trace.
  three-label-affine-lowering-no-go: that chooses one separated source trace whose affine relaxation is classically satisfiable; this proves that every trace of one separated source has a specified affine-unsafe context.
---

**ESTABLISHED UNIQUE-TRACE CONJUNCTION FIREWALL.**  There is a finite BCS
`B_tilde` which is tracially satisfiable and not `R^U`-satisfiable, and a
distinguished three-bit context `c_AND`, such that every satisfying trace has

```text
S_(c_AND)={000,010,100,111}.                              (UTC1)
```

In particular

```text
110=000 xor 010 xor 100
```

belongs to `Aff_F2(S_(c_AND))` but is forbidden.  Thus no satisfying trace of
`B_tilde` has affine-safe support in every context.  This remains true after
passing to an extreme trace, a support-minimal trace, or a trace minimizing
any finite list of local atom masses.

## The finite matrix block

Start with the Mermin--Peres magic-square BCS.  Write its nine involutions as

```text
A B C
D E F
G H I,
```

require the entries in every row and column to commute, require every row
product and the first two column products to be `+1`, and require the last
column product to be `-1`.  Its universal BCS algebra is `M_4(C)`.

For completeness, the four entries `A,B,D,E` generate.  The parity rows give

```text
C=AB,  F=DE,  G=AD,  H=BE,  I=GH.                       (UTC2)
```

The displayed row and column commutations include

```text
[A,B]=[A,D]=[B,E]=[D,E]=1.                              (UTC3)
```

Using `(UTC2)--(UTC3)`, the last-column equation is

```text
C F I=(AB)(DE)(AD)(BE)=AEAE=-1,                         (UTC4)
```

so `AE=-EA`.  The row-three commutation `[G,H]=1` then gives `BD=-DB`.
Thus `(A,E)` and `(B,D)` are two commuting Pauli pairs.  Their universal
algebra is a quotient of `M_2(C) tensor M_2(C)`, while the standard two-qubit
Pauli realization is onto `M_4(C)`.  Hence the magic-square algebra is
exactly `M_4(C)` and has one tracial state.

Adjoin one involution `Y` and one context `(A,B,Y)` whose allowed bit strings
are the graph of Boolean AND, namely the set in `(UTC1)`.  In every exact
model,

```text
(1-Y)/2=((1-A)/2)((1-B)/2),                              (UTC5)
```

so `Y` is already a polynomial in `A,B`; the enlarged block still has
universal algebra `M_4(C)`.  In its unique normalized trace the four joint
atoms of `(A,B)` are rank one, so all four strings in `(UTC1)` have trace
`1/4`.  The AND context is therefore unavoidably affine-unsafe.

## Adjoin the block to a separated source

Let `B_0` be any finite tracially satisfiable, non-`R^U` BCS and let

```text
B_tilde=B_0 disjoint-union B_MS^AND.                     (UTC6)
```

A satisfying trace exists, for example in the tensor product of satisfying
models.  Every satisfying trace restricts on the finite block to the unique
normalized trace of `M_4(C)`, proving `(UTC1)`.  If `B_tilde` had an `R^U`
model, restriction to the generators of `B_0` would give an `R^U` model of
`B_0`, contradiction.  This proves all assertions.

The conclusion is deliberately a compiler firewall, not a refutation of the
affine-support route for a specially chosen source.  It proves that the
positive criterion “choose a perfect trace with affine local supports” is
not invariant under adjoining a finite-dimensional exact conjunct which
preserves the tracial/non-`R^U` separation.  Any positive source theorem must
therefore use the detailed presentation and must exclude this permanent
finite matrix obstruction rather than rely on trace minimality or uniqueness.
