# Iwahori combinatorial unboundedness comes only from core misalignment

Date: 2026-08-14

## 1. Outcome

For either untwisted index-three inclusion

```text
B_+<K=SL_2(Z),             B_-<K,                     (ICM1)
```

the restriction graph on finite-dimensional irreducible unitary
representations has uniformly finite connected components.  More precisely,
every component contains at most six `K`-types and at most twelve
`B_+`-types (and the same statement holds for `B_-`).

This follows because the normal core of either Iwahori subgroup is

```text
N=Gamma(2)=ker(SL_2(Z)->SL_2(F_2)),                   (ICM2)
```

and the quotient pair is the finite pair

```text
B_+/N = C_2 < S_3 = K/N.                              (ICM3)
```

Thus no unbounded representation-type incidence chain is created by
restriction through one Iwahori inclusion.  Clifford theory reduces the
combinatorics of every one-sided component to finite quotient data of
uniformly bounded size.

The compressor identification

```text
sigma:B_+->B_-                                        (ICM4)
```

does not preserve `N`.  In matrix coordinates it moves one factor of two
from the lower off-diagonal entry to the upper one.  Therefore the two
finite Clifford decompositions are organized over different index-two
cores inside the edge.  Alternating the two modular extension structures is
the only place where an unbounded scale chain can occur.

This sharpens the active Iwahori gate: the desired uniform matching theorem
does not need a uniform analysis of arbitrary wild restrictions of
`SL_2(Z)`.  It needs control of the one explicit two-adic core-misalignment
direction created by `(ICM4)`.

## 2. The normal core

Reduction modulo two is onto:

```text
q:K->SL_2(F_2)=S_3.                                   (ICM5)
```

The upper and lower Iwahori subgroups are the inverse images of two point
stabilizers in the natural three-point action of `S_3`.  A point stabilizer
has order two and has trivial core in `S_3`.  Consequently

```text
core_K(B_+)=core_K(B_-)=ker(q)=N.                     (ICM6)
```

In particular, `N` is normal in `K`, is contained in each Iwahori subgroup,
and the quotient indices are

```text
[K:N]=6,                [B_+:N]=[B_-:N]=2.            (ICM7)
```

## 3. Uniformly finite Clifford components

Form the bipartite restriction graph whose left vertices are irreducible
finite-dimensional unitary representations of `K`, whose right vertices
are irreducible representations of `B_+`, and whose edges record occurrence
under restriction.

Fix an irreducible `N`-representation `xi` occurring below one vertex and
let

```text
O=K xi                                                   (ICM8)
```

be its conjugacy orbit.  Since `K/N=S_3`, one has

```text
|O|<=6.                                                (ICM9)
```

Finite-index Clifford theory says that irreducible `K`-representations
lying over `O` are parametrized by irreducible projective representations
of the finite inertia quotient

```text
I_K(xi)/N <= S_3.                                     (ICM10)
```

For any fixed multiplier, the number of irreducible projective
representations of a finite group is at most its order.  Hence there are at
most six irreducible `K`-types lying over `O`.

Now decompose `O` into `B_+`-orbits.  There are at most six such orbits.
For each orbit, the corresponding inertia quotient is a subgroup of

```text
B_+/N=C_2.                                            (ICM11)
```

It has at most two irreducible projective representations.  Therefore at
most twelve irreducible `B_+`-types lie over all the `B_+`-orbits inside
`O`.

If a `K`-type and a `B_+`-type are adjacent, their restrictions to `N`
contain types in the same `K`-orbit `O`.  Moving across any further edge
does not change `O`.  Thus the entire connected component stays inside the
finite collection just counted.

**Theorem 1 (uniform one-sided component bound).**  Every component of the
`K`--`B_+` restriction graph has at most six `K` vertices and at most twelve
`B_+` vertices.  The same holds with `B_-` in place of `B_+`.

The numerical bounds are deliberately coarse.  The important point is that
they are absolute and independent of representation dimension and of the
particular `N`-type.

Combined with
`TRUE_IWAHORI_INDEX_THREE_HAS_BOUNDED_BRANCHING.md`, every edge of these
components has multiplicity one, every vertex has degree at most three, and
the dimensions of adjacent types differ by at most a factor of three.

## 4. The compressor moves the core

Write an element of `B_+` as

```text
g=[[a,b],[2c,d]].                                      (ICM12)
```

The Iwahori isomorphism is

```text
sigma(g)=[[a,2b],[c,d]].                               (ICM13)
```

The condition `g in N` is

```text
a,d odd,                  b even,                     (ICM14)
```

while `c` is unrestricted because the lower entry in `(ICM12)` is already
even.  Therefore

```text
sigma(N)
 ={[[a,2b],[c,d]] in B_- : a,d odd, b even}.          (ICM15)
```

Equivalently, the upper-right entry in `(ICM15)` is divisible by four,
whereas its lower-left entry need not be even.  On the other hand,

```text
N
 ={[[a,2b],[c,d]] in B_- : a,d odd, c even}
 subset B_-.                                           (ICM16)
```

Thus `sigma(N)!=N`.  For an explicit witness,

```text
[[1,0],[2,1]] in N,
sigma([[1,0],[2,1]])=[[1,0],[1,1]] notin N.            (ICM17)
```

Both `N` and `sigma(N)` have index two in `B_-`, but they are distinct.
Their intersection requires simultaneous lower-left divisibility by two
and upper-right divisibility by four.  This is the first two-adic refinement
created by alternating the two vertex origins.

## 5. Exact consequence for the matching program

The fixed-library proof treated a finite restriction matrix at a time and
lost uniformity when the irreducible library varied.  Theorem 1 shows that
varying dimension is not, by itself, what makes one restriction matrix
large: after organizing types by their `N`-orbit, every untwisted component
has uniformly bounded combinatorial size.

What can create an unbounded incidence chain is the relation between the two
decompositions after applying `sigma`.  The first decomposition is organized
over `N`-types; the transported second decomposition is organized over
`sigma^(-1)(N)`-types in `B_+`.  These are distinct finite-index normal cores
of the edge group.  Repeated comparison refines the two-adic lattice data
rather than remaining in one finite `S_3` component.

There is still an analytic source of nonuniformity inside this bounded
combinatorics.  The group `N=Gamma(2)` is virtually free and has continuous
families of finite-dimensional unitary representations.  As the underlying
`N`-type varies with dimension, spectral separation and metric
transversality constants can tend to zero even though the number and
multiplicity of adjacent types stay bounded.  Theorem 1 does not rule out
that degeneration.

Consequently, a completion of the Dogon--Vigdorovich matching question may
be localized to the following statement.

> **Two-adic core-alignment theorem.**  If two exact modular-vertex
> representations become Hilbert--Schmidt close after the Iwahori transport
> `sigma`, then, after changing `o(d)` dimensions, their finite Clifford
> packets over `N` and `sigma^(-1)(N)` can be assembled into packets on which
> the alternating two-adic core refinements close to an odd-congruence
> representation.

The conclusion says "odd-congruence" because finite-dimensional
representations of `SL_2(Z[1/2])` are precisely the compatible modular
representations factoring through congruence quotients of odd level, as in
Dogon--Vigdorovich Question 1.4.

The theorem is not proved here.  The advance is the exact localization of
all unbounded **combinatorial incidence** behavior to
`(ICM15)--(ICM16)`.  One-sided Iwahori branching is uniformly finite.  The
remaining analytic work must control both the two-adic core refinement and
the possible collapse of transversality as the underlying `N`-type varies.
