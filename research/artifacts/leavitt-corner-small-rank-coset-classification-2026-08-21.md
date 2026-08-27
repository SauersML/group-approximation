# Small support in the C3-fixed Leavitt unitization

Let `H=<g>` have order three and let `z=sum_H[h]` in `F_2[G]`.  For a finite
support set `X`, right multiplication by `z` replaces every point by its full
right `H`-coset.  Hence the coefficient on a right coset is the parity of the
number of points of `X` in it.  The identity

```text
(sum_X[x])z=z
```

means odd incidence on the base coset `H` and even incidence on every other
right coset.  Left multiplication gives the identical left-coset rule.

At support three, the two off-base points occupy one left/right cell.  That
cell has at least two elements, so the corresponding conjugate of `H`
intersects `H` nontrivially.  Order three makes the two subgroups equal.  The
support is contained in a finite-by-cyclic amenable subgroup, and cannot be
one factor of a genuine one-sided inverse in a group algebra.

At support five, the number of base points is one or three (it cannot be five
because `|H|=3`).  The three-point case is normalizer-supported.  In the
one-point case, the remaining four edges form a two-regular bipartite graph
between two left and two right
cosets.  Two doubled edges are again normalizer-supported.  A four-cycle
outside the normalizer has the forced rectangle

```text
{x,rx,xs,rxs},       r,s in H minus {1},
```

and its group-algebra sum is `(1+[r])[x](1+[s])`.

For the Leavitt corner, unitized factors `alpha=a+z`, `beta=b+z` both fix
`z`, since `a,b` live under `e=1-z`.  Therefore the rank-three branch is
closed and `(5,7)` is the first surviving profile.  The five-term factor has
the normalizer/rectangle dichotomy above.  Finishing `(5,7)` now requires
using the seven-term partner and the product equation; the one-factor coset
constraints alone are exhausted by this classification.
