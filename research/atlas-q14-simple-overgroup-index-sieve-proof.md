---
rg: 2
id: atlas-q14-simple-overgroup-index-sieve-proof
kind: route
title: Use A8 low-index orbits, q14 fixed points, and primitive permutation-group theorems
target: atlas-q14-simple-overgroup-index-is-at-least-24
requires:
  - atlas-q14-finite-quotient-is-simple-overgroup-test
  - atlas-a4-packet-biclique-decomposition
  - atlas-q14-adds-stratified-thirteenth-double-coset
---

For a packet edge the marked generators have exact orders two and three and
satisfy `(ba)^3=1`.  The triangle presentation

```text
<b,a | b^2=a^3=(ba)^3=1> ~= A4
```

surjects onto their generated subgroup.  No proper quotient of `A4` retains
both an element of order two and an element of order three, so the image is
`A4`.  This proves `(OSI4)` and the stated row/column amalgam skeleton.  Since
q14 is `(t_1t_2)^2`, involutivity gives `(OSI5)`.  The marked `t23` is a
transvection.  In `A8 ~= GL_4(2)` the 105 transvections form one conjugacy
class, hence their centralizer has order `20160/105=192`.  If the commuting
`t_1` lies outside `B`, then `C_S(t_2)` properly contains `C_B(t_2)`, proving
`(OSI6)`.

The two chart groups are distinct, since they generate `S` and `S` is
strictly larger than `A8`.  Thus `T=A intersect B` is proper.  The standard
minimal-index theorem for alternating groups gives

```text
[A8:T] >= 8.
```

Since `AB` is a subset of `S`,

```text
|A||B|/|T|=|AB| <= |S|,
```

which is `(OSI7)` and initially gives `n>=8`.  Finally conjugation maps
`N_S(A)` into `Aut(A8)`, with kernel `C_S(A)` and with the inner automorphism
group supplied by `A`; since `Out(A8) ~= C2`, `(OSI8)` follows.

We now sharpen the index.  Use these standard finite permutation-group facts.

```text
(F1) The only nontrivial transitive A8 permutation degrees below 24 are
     8 and 15.  The degree-eight action is natural; the degree-fifteen
     action is GL_4(2) on its nonzero vectors and is two-transitive.
(F2) A maximal proper subgroup in a nonabelian simple group is
     self-normalizing.
(F3) A nonabelian simple transitive group of prime degree is two-transitive
     (Burnside's prime-degree theorem).
(F4) The finite three-transitive classification in degree 16 leaves, for
     point stabilizer A8 in its degree-fifteen action, the affine group
     2^4:A8; that group is not simple.
(F5) A proper subgroup of A11 of index below 55 has index 11; in particular
     A11 has no subgroup of index 45.
```

Facts `(F1)` and `(F5)` are the relevant initial entries of the usual
low-index subgroup lists for alternating groups.

Let `S` act faithfully on `Omega=S/A`, of degree `n`.  For `8<=n<=16`, any
nontrivial block action would embed the simple group `S` into an alternating
group on at most eight blocks, impossible by order.  Hence the action is
primitive, `A` is maximal and self-normalizing, and `A` fixes exactly the base
point.  Its remaining orbits have the degrees in `(F1)`.

For `n=8`, order already forbids `S < Sym(8)`.  For `10<=n<=15`, the integer
`n-1` is neither 8 nor 15 nor a sum of them, so no orbit decomposition exists.
For `n=16`, the remaining fifteen points form the two-transitive degree-fifteen
`A8` orbit.  Thus `S` is three-transitive, and `(F4)` contradicts simplicity.

It remains to exclude `n=9`.  The faithful coset action has

```text
|S|=9|A8|=|A9|,
```

and its sign is trivial, so `S=A9`.  Both chart copies are point stabilizers:
every faithful degree-nine action of `A8` is its natural degree-eight action
plus one fixed point.  A transvection has cycle shape `2^4` on those eight
points, hence each of `t_1,t_2` has a unique fixed point in degree nine.
Commuting permutations preserve each other's fixed-point sets, so `(OSI5)`
forces those unique points to coincide.  The two point stabilizers are then
equal, contrary to generation of `A9`.  Thus q14 eliminates index nine.

For `n=17`, prime-degree theorem `(F3)` makes the action two-transitive, while
`A` can only split the other sixteen points into two degree-eight orbits, a
contradiction.  For `18<=n<=21`, every possible nontrivial block action is
excluded by order and divisibility in the induced alternating group on the
blocks (at `n=20`, the only largest case would require
`403200=|S|` to divide `|A10|`, which it does not).  Hence these actions are
primitive, but none of `17,18,19,20` is a sum of 8 and 15, so `(F1)` again
contradicts the required decomposition of `Omega` minus its base point.

At `n=22`, a primitive action would require 21 to be a sum of 8 and 15.  An
imprimitive action can only have eleven blocks of size two, and simplicity
would embed `S` into `A11` with

```text
[A11:S]=|A11|/(22|A8|)=45,
```

contrary to `(F5)`.  At `n=23`, prime degree gives primitivity, while 22 is
again not a sum of 8 and 15.  This proves `(OSI3)`.

Finally take `n=24`.  If the coset action is primitive, self-normalization
leaves one fixed point and `(F1)` forces the unique subdegree multiset
`1,8,15`, proving `(OSI10)`.  If it is imprimitive, simplicity embeds `S`
faithfully in the alternating group on the blocks.  Every block count below
twelve is excluded by order; twelve blocks of size two remain, and direct
order division gives `[A12:S]=495`, proving `(OSI11)`.  Also `(OSI7)` and the
low-index list for `A8` say that the proper intersection `T` has index 8 or
15, giving exactly the two groups in `(OSI9)`.
