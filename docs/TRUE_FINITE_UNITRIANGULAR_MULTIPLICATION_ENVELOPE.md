# A finite unitriangular envelope synchronizes every bounded root product

Date: 2026-08-14

## 1. Outcome

The cross-root multiplication data should not be exactified one Heisenberg
pair at a time.  Every finite coefficient window in the Leavitt algebra has
one **finite upper-unitriangular envelope** containing all of its bounded
Steinberg products in common matrix coordinates.

This removes a genuine but limited ambiguity.  All additive root groups,
all products occurring along a positive root chain, and the complete local
table

```text
t_l s_k = delta_(l,k)
```

can be placed in one finite group before taking a matrix microstate.  Hence
there is no need to choose unrelated Stone--von Neumann gauges for the
individual `A_2` cells.

It does **not** solve nonhyperlinearity.  The comb compressor is not in this
finite group.  After the finite envelope is repaired, its matrix is still an
intertwiner between a source subgroup and a proper compressed subgroup, and
the unresolved datum is the multiplicity-space action of that intertwiner.
The construction below therefore narrows common-coordinate extraction; it
does not silently assume it.

## 2. Finite nilpotent-envelope lemma

Let `R` be an algebra over `F_2`, let `m>=2`, and for each `i<j` let
`V_(i,j)` be a finite-dimensional `F_2`-subspace of `R`.  Assume

```text
V_(i,j) V_(j,k) <= V_(i,k)              (i<j<k).       (FUE1)
```

Let `N(V)` be the vector space of strictly upper-triangular `m` by `m`
matrices whose `(i,j)` entry belongs to `V_(i,j)`.  Matrix multiplication
and `(FUE1)` give

```text
N(V) N(V) <= N(V),          N(V)^m=0.                 (FUE2)
```

Consequently

```text
U(V)=1+N(V)                                             (FUE3)
```

is a finite group.  Indeed, it is closed under multiplication and

```text
(1+A)^(-1)=1+A+A^2+...+A^(m-1)                         (FUE4)
```

in characteristic two.  Moreover

```text
|U(V)|=2^(sum_(i<j) dim_F2 V_(i,j)).                   (FUE5)
```

Every root element `x_(i,j)(a)=1+a e_(i,j)` with
`a in V_(i,j)` lies in `U(V)`, and all Steinberg commutators between these
roots are computed inside this one finite group:

```text
[x_(i,j)(a),x_(j,k)(b)]=x_(i,k)(ab).                  (FUE6)
```

No approximation or representation theory is used in this lemma.

## 3. Every finite window admits such an envelope

Start with arbitrary finite seed sets `S_(i,j) subset R`.  For `i<j`, define
`V_(i,j)` to be the span of all products

```text
a_0 a_1 ... a_(r-1)                                  (FUE7)
```

arising from a chain

```text
i=i_0<i_1<...<i_r=j,
a_q in S_(i_q,i_(q+1)).                              (FUE8)
```

There are finitely many chains and finitely many choices on each chain, so
every `V_(i,j)` is finite dimensional.  Concatenating two chains proves
`(FUE1)`.  Thus any prescribed finite family of coefficients can be seeded
on the needed roots and closed under every positive-root product without
creating an infinite group.

For `m=5`, at most four seed factors occur.  This is exactly the depth needed
to retain all associativity squares along a four-root Steinberg chain.  Long
Leavitt words cause no problem: a word already present in the finite window
is treated as one seed coefficient; only the number of root positions, not
its internal word length, bounds `(FUE7)`.

The same statement works in the concrete elementary group.  The matrices
`1+N(V)` are literal invertible matrices over `R`, so no unstable `K_2`
identification is required.  If the candidate is presented through a
Steinberg cover, one may either use its positive-root normal form or pass to
the elementary quotient for this finite packet.

## 4. Application to the binary branch table

Choose four ordered matrix coordinates

```text
i < 0 < 4 < j.                                        (FUE9)
```

Seed the envelope with the incoming and outgoing branch roots

```text
I_l(b)=x_(i,0)(b t_l),
O_k(a)=x_(0,j)(s_k a),                                (FUE10)
```

their raw-routed counterparts

```text
x_(i,4)(b),             x_(4,j)(a),                  (FUE11)
```

and every coefficient from the chosen finite `a,b` window.  The envelope
then contains the complete products

```text
[I_l(b),O_k(a)]
 =x_(i,j)(b t_l s_k a)
 =x_(i,j)(delta_(l,k) b a).                           (FUE12)
```

All four branch cases and all their central characters now belong to one
finite representation problem.  Enlarging the seed list also includes the
compressed coefficients `s_0 a t_0` used by the comb covariance.

Given a hyperlinear microstate, request multiplicativity on the whole finite
group `U(V)`, not on separate root triples.  Finite-group
Hilbert--Schmidt stability then repairs this restriction, up to an
asymptotically negligible dimension adjustment, to a genuine representation
of `U(V)`.  Since the window is fixed before the microstate tolerance is
chosen, no uniform stability constant in `|U(V)|` is required.  A primary
source for this finite-group repair is Gowers--Hatami,
[Inverse and stability theorems for approximate representations of finite
groups](https://arxiv.org/abs/1510.04085).

Thus every root PVM and every multiplication character in `(FUE12)` is now
read in one Wedderburn decomposition.  Pairwise projective-cocycle matching
is no longer part of the atlas gate.

## 5. Exact limitation: the regular envelope is a countermodel

The left regular representation of `U(V)` realizes `(FUE6)` and `(FUE12)`
exactly.  It contains the same finite Pauli sectors that defeated the local
Weyl-sign decoder.  Therefore the following inference remains false:

```text
one common finite multiplication envelope
  => classical coefficient maps
  => binary Leavitt contradiction.                    (FUE13)
```

What is missing is the matrix of the **comb compressor** relative to this
single repaired decomposition.  It approximately satisfies

```text
C rho(x_(r,s)(a))
  =rho(x_(r,s)(s_0 a t_0)) C,                         (FUE14)
```

while the raw router distinguishes the complementary `1` branch.  In the
regular representation of the full infinite group, the coefficient spaces
in `(FUE14)` have infinite multiplicity and no dimension contradiction is
available.  In finite matrices the multiplicities are finite, but proving
that the three branch blocks share the pairing coordinate is precisely the
remaining CE-specific statement.

The finite envelope consequently gives a cleaner formulation of the live
theorem:

> Repair one growing `U(V_n)` packet exactly, disintegrate the single comb
> matrix over that one representation, and prove that its two diagonal
> branch blocks and one crossed block satisfy the three common-coordinate
> pairing defects.

Once this is obtained, `TRUE_DIAGONAL_PAIRING_DEFECT_SUPPLIES_SPECTRAL_INVARIANCE.md`
and the `2-sqrt(3)` Leavitt floor finish the contradiction.  No additional
Pauli gauge matching, positive-density argument, or spectral-invariance
lemma remains.

## 6. Research decision

Future packet searches should use one finite unitriangular envelope and ask
only how the comb matrix acts on its multiplicities.  Enlarging collections
of separately exactified Heisenberg cells is unnecessary.  Conversely, any
argument that stops before `(FUE14)` is locally sterile, because the regular
representation of `U(V)` is an exact finite countermodel.

No local computation or build was run for this note.
