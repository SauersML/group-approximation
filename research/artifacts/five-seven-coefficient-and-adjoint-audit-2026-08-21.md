# The exact five-by-seven coefficient system

Let `H=<g>=C_3`, `z=1+g+g^2`, `e=1+z=g+g^2`, and write the rectangle
factor as

```text
alpha=h_0+(1+r)x(1+s),
```

where `h_0,r,s in H`, `r,s !=1`, and `x` does not normalize `H`.  If
`beta=sum_q b_q[q]`, the equation `alpha beta=1` is exactly

```text
b_p + sum_{a in {1,r}, c in {1,s}}
          b_(c^-1 x^-1 a^-1 h_0 p)
    = 1_(p=h_0^-1).                                      (1)
```

Thus the unresolved `(5,7)` case is a seven-vertex finite-support solution
of one explicit four-predecessor parity recurrence.  The reverse product is
governed by the genuinely different equations

```text
b_(q h_0^-1) + sum_{a in {1,r}, c in {1,s}}
          b_(q c^-1 x^-1 a^-1)
    = 1_(q=1).                                           (2)
```

Equations (1) do not turn into (2) by the `C_3`-fixedness conditions.

## Exact normalization and the failed adjoint shortcut

Inside `e F_2[H] e=F_4`, one has

```text
1+r=r^-1 e,       (1+r)^-1=r e
```

and similarly for `s`.  Multiplication on the left by `(1+r)^-1`, on the
right by `(1+s)^-1`, and then by the inverse of the remaining scalar sends
`e alpha e` to

```text
e(1+y)e,       y=s^-1 h_0^-1 r^-1 x.                    (3)
```

The adjoint is `e(1+y^-1)e`.  Therefore an element `n in N_G(H)` with
`nyn^-1=y^-1` would indeed identify the normalized factor with its adjoint;
right invertibility would then imply left invertibility and kill that
particular rectangle.  But no such `n` follows from the rank-five support
equations.  In the universal model `G=H*<x>`, the normalizer of `H` is `H`,
and reduced-word normal form shows that no `h in H` conjugates `kx` to
`x^-1 k^-1`, for any `k in H`.  Hence adjoint symmetry is an additional
relation on the double coset, not a consequence of the Hecke rectangle.

## The seven-term incidence list

For the unitized corner pair, `z beta=beta z=z`.  Regard every support term
of `beta` as an edge between its left and right `H`-cosets.  The parity of
the degree is odd at the two base vertices and even everywhere else.  The
number `m=|supp(beta) intersect H|` is therefore `1` or `3`; after deleting
those `m` base-cell edges, every degree is even.  A cell has capacity one
off the normalizer and capacity three in the normalizer.  Decomposition of
the remaining Eulerian bipartite multigraph into cycles gives the complete
list:

```text
m=3:  one 4-cycle, or two 2-cycles;
m=1:  one 6-cycle, one 4-cycle plus one 2-cycle,
      or three 2-cycles.
```

A 2-cycle is precisely a doubled normalizer cell.  Together with support
localization, all vertices in this list lie in `<H,x>` in the rectangle
branch.  This is the exact finite geometry on which (1) must be solved; it
does not by itself exclude a solution.

## What happens in the normalizer branch

Put `N=N_G(H)`.  Since `e` is invariant under `N`, the corner `eF_2[N]e` is
the crossed product of `F_4=eF_2[H]e` by `N/H` (with the action and section
cocycle induced by conjugation and by a choice of quotient representatives).
For the binary Leavitt unit group,

```text
N = L_F4(1,2)^x semidirect Gal(F_4/F_2),
```

so this is a crossed product over the corresponding projective semilinear
quotient, not an ordinary group algebra to which one may recursively apply
the original `F_2` rank theorem.

If a normalizer-supported five-term factor contains all three elements of
the base `H`-cell, its other two terms form one doubled quotient cell.  The
base triple compresses to zero and the doubled cell to one nonzero `F_4`
coefficient times a quotient monomial.  Its corner component is therefore
invertible, so this subcase cannot witness one-sided failure.  The only
normalizer survivor has one base term and two doubled cells: it compresses
to exactly three crossed-product monomials.  A seven-term partner with three
base terms compresses to a binomial.  After one monomial normalization that
binomial belongs to the corner over one cyclic quotient subgroup, hence to
an amenable finite-by-cyclic corner; coset projection and direct finiteness
there exclude a proper one-sided inverse.  The partner therefore has one
base term and three doubled cells, and compresses to exactly four monomials.
Thus the normalizer half is exactly one `3`-by-`4` problem over this fixed
`F_4` crossed product.  Passing to `F_16` is neither needed nor justified.

For a rectangle factor, a partner wholly supported in `N` is impossible:
`h_0 beta` remains in `F_2[N]`, whereas every term of
`(1+r)x(1+s)beta` remains outside `N`.  Equality to the identity would force
`h_0 beta=1`.  The rectangle branch therefore retains only

```text
m=3:  one 4-cycle;
m=1:  one 6-cycle, or one 4-cycle plus one doubled normalizer cell.
```

The remaining `m=3` four-cycle compresses, after removing its two edge
coefficients, to a literal `e[u]e`.  A left inverse for that literal is an
injectivity statement for the incidence operator between the `H`- and
`uHu^-1`-coset systems.  Relations create cycles in that graph, and nothing
in the coefficient equations turns injectivity into surjectivity.  This is
the irreducible obstruction left by the symbolic reduction.
