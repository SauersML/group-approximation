---
rg: 2
id: pair-flips-in-finitary-symmetric-group-add-no-envelope
kind: claim
title: Pair flips in a finitary symmetric group add no new Cartan envelope
distinct_from:
  amenable-group-basis-sl3-envelope: that allows an arbitrary amenable group basis and a non-Cartan embedding of the rigid factor; this audits the most concrete proposed basis `S_fin(Y times {0,1})` and shows its visible pair-flip subalgebra is exactly the old abelian lane and is not Cartan.
  algebraic-compact-action-envelope-for-non-ce-relation: that asks for a non-CE inclusion in an abelian Haar crossed product; this proves that the canonical pair-flip inclusion inside the larger noncommutative crossed product is precisely such an abelian Haar crossed product, with no automatic promotion of the source relation.
---

Let a countable group `Lambda` act on a countable set `Y`, put

```text
K=S_fin(Y times {0,1}),
A=< (y,0)(y,1) : y in Y > = direct_sum_Y C_2,
```

and let `Lambda` act on `K` by permuting the `Y`-coordinate.  Then there is a
canonical trace-preserving inclusion

```text
L(A) rtimes Lambda  ->  L(K) rtimes Lambda.             (PFS1)
```

The source of `(PFS1)` is exactly the compact-abelian Haar crossed product
for the Bernoulli/coset lamp action on `{+-1}^Y`; thus using only the pair-flip
coordinates does not escape the affine-Haar envelope problem.

Moreover `L(A)` is not a MASA, hence not a Cartan subalgebra, of `L(K)` when
`Y` is infinite.  Every finitary permutation has a finite conjugacy orbit
under `A`; summing any nontrivial such orbit gives an element of
`L(A)' cap L(K)` outside `L(A)`.  Therefore the larger symmetric group does
not turn the pair-flip coordinates into a universal invariant Cartan.  Any
gain from `(PFS1)` would have to be a genuinely non-Cartan use of the extra
finitary permutation operators.

