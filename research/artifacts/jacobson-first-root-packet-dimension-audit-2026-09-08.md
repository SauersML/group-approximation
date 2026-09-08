# The first root packet forces dimension at least 52

The stronger [single-orbit obstruction](jacobson-single-rank-one-orbit-obstruction-2026-09-08.md)
raises this bound to 98 by comparing the two finite root packets.
The orbit and four-extension calculations below provide the first
step of that argument.

2026-09-08. Every exact finite-dimensional complex unitary representation
of `Xi` retaining the head has dimension at least 52. This is a necessary
dimension bound; it does not assert a gap as the dimension grows or
construct a representation in dimension 52.

Use `Xi` and its derived finite subgroup

```text
P=N semidirect F,
N=Mat_(3 x 3)(F_2)_add,
F=GL_3(F_2)_Q x GL_3(F_2)_P,
```

from [the first-level root reconstruction](jacobson-ts-splitting-and-first-level-root-packet-2026-09-08.md).
The distinguished root is the same word

```text
D=D(e_1,e_1^*)=h a_1 h,       a_1=x_21,Q.             (1)
```

## 1. Independent audit of the source extension

The reconstruction's head extension is valid. The element `D`
centralizes `x_21,Q,x_31,Q,x_23,Q` in the exact boundary packet.
The first braid and split TS relation add `x_32,Q`. These generate
the full stabilizer of the covector `e_1^*`, whose matrices have first
row `(1,0,0)`. The independently obtained tail stabilizer fixes `e_1`.

Consequently the full `F`-orbit `D(v,f)` is independent of the
choices of transporters. The source and target addition identities
already present on the two coordinate planes extend to all pairs by
the respective finite group actions. Expanding `D(v+v',f+f')` in
the two possible orders and cancelling the first and last factors
forces all cross commutators to vanish. The literal level-zero to
level-one action identifies the nine independent coordinates and
shows `N intersect F=1`. Thus the full matrix packet used below
requires no assumption about complex defining representations.

## 2. The nonzero character orbits have dimensions at least 49

Identify the character group of `N` with the dual three-by-three
matrix space, using the trace pairing over `F_2`. Its `F`-orbits
are distinguished by matrix rank. Their sizes are

```text
rank:       0     1      2      3
orbit:      1    49    294    168.
```

There are `7*7=49` rank-one matrices. A rank-two map has one of
seven kernel lines, one of seven image planes, and one of six
isomorphisms between the resulting two-dimensional spaces. The
invertible maps form `GL_3(F_2)`, of order 168.

In a complex representation, all character spaces in an orbit have
equal dimension. A nontrivial head makes `a_1`, hence `D` by (1),
nonidentity: the nonidentity head transvections are conjugate. Thus
some nonzero `N`-character occurs, giving dimension at least 49.

If the total dimension is 49, 50, or 51, the `N`-nontrivial part
must be exactly one rank-one orbit, with one-dimensional character
spaces. The remaining `N`-trivial part has dimension at most two.

## 3. All four 49-dimensional extensions have the wrong head rank

The stabilizer of a rank-one character in `F` is a product of two
groups isomorphic to `S_4`: a vector stabilizer and a covector
stabilizer. Because a character space has dimension one, each factor
acts on it by either its trivial character or its sign character.
Equivalently, the restriction to `F` on this 49-dimensional part is

```text
rho_epsilon tensor rho_eta,
rho_0=Ind_(S_4)^G(1),
rho_1=Ind_(S_4)^G(sign),                 epsilon,eta in {0,1}.
```

This also follows directly by choosing a vector in one character
line and transporting it around the transitive `F`-orbit; there
are no other multiplicity-one possibilities.

Let `tau` be a nonidentity involution of `G=GL_3(F_2)`. Its
conjugacy class consists of the 21 transvections, so its centralizer
has order eight. Each `S_4` stabilizer contains six transpositions
and three double transpositions. The induced-character formula gives

```text
chi_(rho_0)(tau)=(8/24)(6+3)=3,
chi_(rho_1)(tau)=(8/24)(-6+3)=-1.
```

Therefore the negative eigenspace dimension of the head element
`a_1` on the 49-dimensional part is either

```text
(49-7*3)/2=14,
(49-7*(-1))/2=28.                                    (2)
```

By contrast, `D` has negative rank exactly 16 there. A rank-one
dual matrix is `alpha tensor f` with each factor nonzero; it takes
value one on the elementary matrix `D` precisely when both factors
evaluate to one on its prescribed nonzero coordinates. There are
four choices for each factor, giving `4*4=16` negative characters.
The possible sign twists of the stabilizer action do not change
these `N`-eigenvalues.

The two values in (2) disagree with 16. This contradicts the unitary
conjugacy (1), and excludes dimension 49.

## 4. Two extra dimensions cannot repair the mismatch

The `N`-trivial complement is `F`-invariant. Its head action is
trivial if its dimension is at most two. One can see this without
a character table: `G` is perfect, so a two-dimensional unitary
representation has determinant one. In `SU(2)` every nonidentity
involution is the central matrix `-I`. All transvections of `G`
are conjugate, and two distinct commuting transvections can have
a transvection as their product. They therefore cannot all map to
`-I`; they all map to `I`. Since they generate `G`, the entire
representation is trivial. The one-dimensional case follows from
perfectness directly.

Thus the complement contributes no negative eigenvalues to either
`a_1` or `D`. The mismatch (2) versus 16 persists in dimensions
50 and 51. This proves the stated lower bound

```text
dimension >= 52.
```

No classification of representations in dimension 52 or above is
claimed. In particular, excluding the smallest character orbit does
not turn this bound into a dimension-independent matrix obstruction.
The argument is exact finite-group character theory; no computation
or formal proof checker was used.
