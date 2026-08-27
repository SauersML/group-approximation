---
rg: 2
id: degree-four-kl-inner-retractions-fail-proof
kind: route
title: Reject canonical inner and proper prefix-corner images on exact moved vectors
target: degree-four-kl-inner-retractions-fail
requires:
  - degree-four-kl-source-face-retraction
---

Use the four relators `(DG2)` in
`degree-four-kl-source-face-retraction-proof`.  A candidate retraction fixes
`G_0`.  For each `i=1,2,3`, choose

```text
phi_i=1,  phi_i=Ad(p^k),  or
phi_i=Ad(p^k q p^(-k)),  or
phi_i=Ad(p^k) o iota_j,       j in {0,1}, 0 <= k < 20. (IR1)
```

Here `iota_j` acts as the given matrix on the prefix-`j` cylinder and as the
identity on its complement.  It is the canonical proper self-embedding
induced by the Leavitt corner `s_j R t_j`.  There are `81^3=531441` triples.
The equation `R0=1` is linear in its final
`z`, so it uniquely sets

```text
z=(r0 e1 a2 c1 b3 d2 p3)^(-1).                       (IR2)
```

The artifact substitutes `(IR2)` into `R1,R2,R3`.  It acts each resulting
word on the faithful standard module whose basis is a matrix coordinate and
an infinite binary word.  For a tested vector the script retains an opaque
tail and exposes at least as many initial bits as the total number of deletion
operators in the word.  Therefore a moved vector is a literal witness in the
infinite module, not evidence from a truncation.  Four deterministic prefix
patterns and all twenty matrix coordinates suffice to find a witness in every
case.

The run was performed remotely through the permitted MSI wrapper:

```text
/Users/user/msi-node/msi put \
  research/artifacts/screen-degree4-full-copy-inner.py \
  /projects/standard/hsiehph/sauer354/screen-degree4-full-copy-inner.py
/Users/user/msi-node/msi \
  'python3 /projects/standard/hsiehph/sauer354/screen-degree4-full-copy-inner.py'
```

The exact output was

```text
cases=531441
rejected_by_R1_R2_R3=(531441, 0, 0)
witness_screen_survivors=0
three_leaf_cases=384000
three_leaf_rejected_by_R1_R2_R3=(384000, 0, 0)
three_leaf_witness_screen_survivors=0
```

The phrase `witness_screen` limits the positive direction only: a survivor
would require a complete identity audit.  Since every case has an explicit
moved vector, the zero-survivor conclusion for the family `(IR1)` is exact.

## The first complete-prefix-code obstruction

A tempting infinite-depth proof would choose a cylinder outside the supports
of all three proper corner maps.  The first symbolic shape where that is
impossible is the three-leaf code

```text
{0,10,11}.                                             (IR3)
```

The artifact therefore tests `(IR3)` separately: all six assignments of its
leaves to copies `1,2,3`, and independently on each copy all forty outer
conjugators `p^k` and `p^k q p^(-k)`.  These are
`6*40^3=384000` cases.  The coordinate-`q` sector is load-bearing because it
need not preserve the cylinder blocks.  Nevertheless every case is rejected
already by `R1` on an exact moved vector, as the final three output lines show.

This removes the first obstruction to a partition-sensitive induction.  It
does not itself supply that induction for arbitrary nested prefix codes or
for inner words of unbounded packet length.
