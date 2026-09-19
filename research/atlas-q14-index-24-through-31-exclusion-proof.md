---
rg: 2
id: atlas-q14-index-24-through-31-exclusion-proof
kind: route
title: Exclude indices twenty-four through thirty-one by orbital arithmetic and small-degree permutation classification
target: atlas-q14-simple-overgroup-index-is-at-least-32
requires:
  - atlas-q14-simple-overgroup-index-is-at-least-24
---

Continue with the faithful coset action `S` on `Omega=S/A`.  We use the next
entry of the standard low-index list for `A8`:

```text
the only nontrivial transitive A8 degrees below 32 are 8,15,28. (L32)
```

The degree-28 action is the natural action on two-subsets of eight points.

First let `n=24`.  In the primitive residue from `(OSI10)`, unequal subdegrees
8 and 15 are each self-paired.  The valency-eight orbital graph would be a
primitive rank-three graph with parameters `(v,k)=(24,8)`.  Its parameters
would obey

```text
8(7-lambda)=15 mu.                                   (E24)
```

The left side lies between zero and 56, so divisibility forces `mu=0` and
`lambda=7`; that gives disconnected cliques and contradicts primitivity.

In the imprimitive residue `(OSI11)`, the induced action on the twelve blocks
is faithful and primitive: any further block action has at most six points,
too few for `S`.  Its block stabilizer has order `40320` and contains `A` with
index two.  On the twelve blocks, `A8` has orbit profile `8+1+1+1+1`, so it
contains a permutation which is a single 3-cycle.  Jordan's theorem forces the
primitive group `S` to contain `A12`; since simplicity puts `S` inside `A12`,
this gives `S=A12`, contrary to `|S|=24|A8|`.  Thus `n!=24`.

At `n=25` the coset action is primitive, so `A` is self-normalizing and has
orbit profile `1+8+8+8`.  A marked transvection has cycle shape `2^4` in every
degree-eight orbit and therefore fixes exactly the base point.  The same orbit
arithmetic forces `B` to fix a point, hence to be a conjugate point stabilizer;
it too is self-normalizing and its marked transvection has one fixed point.
By q14 the two transvections commute, so they preserve each other's singleton
fixed sets.  The points, and hence the two point stabilizers, coincide.  This
contradicts `<A,B>=S`.

At `n=26`, a primitive action is impossible because 25 is not a sum of 8 and
15.  The only imprimitive residue has thirteen blocks of size two.  The block
action is primitive of prime degree, and `A` acts there as `8+1+1+1+1+1`,
again supplying a single 3-cycle.  Jordan's theorem gives `S=A13`, contrary to
order.  At `n=27`, every block action is too small and the primitive residue
would require 26 to be a sum of 8 and 15.  At `n=28`, the only imprimitive
residue has fourteen blocks of size two; the same block-action argument gives
`S=A14`.  The primitive residue would require 27 to be a sum of 8 and 15.
Hence indices 26, 27, and 28 are impossible.

At `n=29`, Burnside's prime-degree theorem makes `S` two-transitive and `(L32)`
forces point stabilizer `A8` to use its degree-28 action.  The finite
two-transitive classification in degree 29 has no simple group with point
stabilizer `A8` (the alternating case has point stabilizer `A28`), so this
index is impossible.

At `n=30`, a primitive action is excluded by `(L32)`.  For an imprimitive
action, fifteen blocks of size two give a primitive block action in which `A`
has profile `8+1^7`; a single 3-cycle and Jordan's theorem force `S=A15`.
Ten blocks of size three would embed `S` in `A10` with index three, impossible
for the simple group `A10`; all smaller block actions are excluded by order.
Thus `n!=30`.  Finally `n=31` is prime, so Burnside makes the action
two-transitive, but `(L32)` contains no transitive `A8` action of degree 30.
This proves `(OSI32-1)`.

For `n=32`, a primitive action makes `A` self-normalizing, and `(L32)` has the
unique decomposition

```text
31=8+8+15,
```

which is `(OSI32-2)`.  In an imprimitive action every block count below 16 is
excluded by order, leaving sixteen blocks of size two.  The faithful block
action lies in `A16`, and

```text
[A16:S]=(|A16|)/(32|A8|)=16216200,
```

giving `(OSI32-3)`.  Finally the product bound `(OSI7)` and `(L32)` give the
three intersection indices and types in `(OSI32-4)`.
