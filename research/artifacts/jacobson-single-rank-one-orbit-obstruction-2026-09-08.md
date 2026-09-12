# A single rank-one root orbit is impossible

2026-09-08. In every exact finite-dimensional complex unitary
representation of `Xi` retaining the head, the nontrivial part of
the first-level root packet cannot consist of one rank-one character
orbit with one-dimensional fibers, even with an arbitrary root-trivial
complement. Consequently the representation has dimension at least
98. This proves a bounded-dimension obstruction, not a positive gap
over all dimensions.

## 1. The two finite root packets

Use `Xi` from
[the mixed root reconstruction](jacobson-ts-splitting-and-first-level-root-packet-2026-09-08.md)
and its two exact finite packets

```text
F=G_Q x G_P,                         G=GL_3(F_2),
P=N semidirect F,                    N=Mat_(3 x 3)(F_2)_add,
J=E semidirect (K_Q x G_*),           E=Hom(F_2^2,F_2^3).
```

The common head subgroup is
`P_Q=A_Q semidirect K_Q~=S_4`, where `A_Q~=C_2^2` is
the head row-two group and `K_Q~=S_3` acts in coordinates `1,3`.
The subgroup `K_P~=S_3` acts in coordinates `1,3` of both
`G_P` and `G_*`. These copies agree in the finite-packet overlap.

Retain the actual common words

```text
a_1=x_21,Q,           D=h a_1 h in N,
c=x_13,P,            b=w_23,Q w_23,P.
```

The first braid makes `h` conjugate to `b`; the exact shifted
group makes `h` conjugate to `c`. Hence every representation obeys

```text
rank_-(D)=rank_-(a_1),
trace(c)=trace(b).                                   (1)
```

The nonzero character orbits of `N` have ranks one, two, and three,
and sizes `49,294,168`. Suppose that the entire `N`-nontrivial
part consists of the rank-one orbit with one-dimensional character
spaces. The `N`-trivial complement is allowed to have arbitrary
dimension and arbitrary action consistent with `F`.

## 2. The head action of the arbitrary complement is sharply restricted

The stabilizer of a rank-one `N`-character is a product of two
copies of `S_4`. A one-dimensional fiber carries the trivial or
sign character on each factor. Thus the restriction to `F` on the
49-dimensional nontrivial part is

```text
rho_epsilon tensor rho_eta,
rho_0=Ind_(S_4)^G(1),
rho_1=Ind_(S_4)^G(sign),              epsilon,eta in {0,1}.
```

The two induced representations have dimension seven and involution
traces three and minus one, respectively. The head negative rank
on this part is therefore 14 if `epsilon=0`, and 28 if
`epsilon=1`.

The root `D` has negative rank 16, independently of these two
sign choices. Indeed, a rank-one dual matrix takes value one on
its prescribed elementary coordinate for exactly `4*4=16` of
the 49 characters. It acts trivially on the root-trivial complement.
The conjugacy in (1) forces `epsilon=0`, and forces head negative
rank exactly two on that complement.

The elementary character calculation in the appendix shows that
the nontrivial irreducible representations of `G` with negative
involution rank two have dimensions `3,3,6`. Every other
nontrivial irreducible has negative rank four. An irreducible
representation of `F` is a tensor product of irreducibles of its
two factors. Therefore a complement with total head negative rank
two has the precise form

```text
sigma_Q tensor 1_P  direct-sum  1_Q tensor R_P,        (2)
```

where `sigma` is one of the two three-dimensional irreducibles
or the six-dimensional irreducible, and `R_P` is arbitrary.
There can be only one nontrivial head summand; its tail dimension
must be one. Since `G` is perfect, that tail character is trivial.

Combining the orbit and complement, the entire restriction to `F`
is consequently

```text
(rho_0)_Q tensor (rho_eta)_P
  direct-sum sigma_Q tensor 1_P
  direct-sum 1_Q tensor R_P.                          (3)
```

This is why adding an arbitrary root-trivial complement cannot
freely repair the finite-packet restrictions.

## 3. The braid determines the tail sign twist

Let `t_eta` be the involution trace of `rho_eta`, so it is
three or minus one. On the first summand of (3), the difference
between the traces of `c` and `b` is

```text
7 t_eta-3 t_eta=4 t_eta.
```

On the `sigma` summand, the same difference is
`dim(sigma)-trace(sigma(a_1))=4`, because its negative rank is
two. The arbitrary final summand contributes zero: in the tail
group, `x_13` and `w_23` are conjugate. Equation (1) therefore
gives

```text
4 t_eta+4=0.
```

Thus necessarily `eta=1`. The restriction of this tail
representation to `K_P~=S_3` is

```text
rho_1|K_P = 1 direct-sum 2*sgn direct-sum 2*tau,       (4)
```

where `tau` is the two-dimensional standard representation of
`S_3`. For example, its character on identity, involution, and
order-three elements is `(7,-1,1)`, which gives (4) immediately.

## 4. What the original packet supplies on the head fixed space

Take the `A_Q`-fixed subspace and then its `tau_Q` isotypic
part under `K_Q~=S_3`. Its multiplicity space remains a
representation of `K_P`, since the two factors commute.

The relevant head restrictions are

```text
(rho_0)^(A_Q) = 2*1 direct-sum tau,
(sigma_3)^(A_Q) = 0,
(sigma_6)^(A_Q) = 1 direct-sum tau.                   (5)
```

The first follows by restricting the seven-point permutation
representation to the point stabilizer `S_4`: it decomposes as
`2*1+tau_2+standard_3`, and only the first two terms are fixed
by the normal four-group. The three-dimensional irreducibles
restrict to the sign twist of the standard `S_4` representation,
which has no four-group fixed vectors. The six-dimensional
representation is `rho_0-1`, giving the last formula.

The arbitrary head-trivial summand in (3) contributes only the
trivial `K_Q` type and does not affect this `tau_Q` multiplicity
space. By (3)--(5), that space has `K_P` representation

```text
M_F = rho_1|K_P                    if dim(sigma)=3,
M_F = rho_1|K_P direct-sum 1        if dim(sigma)=6.   (6)
```

These conclusions hold with no bound on the dimension of `R_P`.

## 5. What the boundary packet necessarily contributes

The dual of `E` is `Hom(F_2^3,F_2^2)`. Its nonzero character
orbits have ranks one and two, with sizes 21 and 42. If `m_1,m_2`
are their common fiber dimensions, the exact boundary-packet
calculation gives

```text
rank_-(a_1)=8m_1+24m_2.
```

The left side is 16 by (1). Hence

```text
m_1=2,                 m_2=0.                       (7)
```

The `E`-trivial subspace can still be arbitrarily large.

Write a rank-one character as `lambda=alpha tensor f`, with
nonzero `alpha in F_2^2` and nonzero target covector
`f in (F_2^3)^*`. Its restriction to `A_Q` is indexed by
`f(e_2) alpha`. Thus exactly the nine characters with
`f(e_2)=0` contribute to the `A_Q`-fixed part of this orbit.
They each have a two-dimensional fiber by (7).

Choose one of them with `f=e_1^*`. The stabilizer of its
character in `K_Q x G_*` is

```text
C_2(source) x S_4(target).                           (8)
```

The target factor is the covector stabilizer of `e_1^*`. The
stabilizer of `e_1^*` within `K_P` is generated by `x_31`.
Inside the target `S_4`, this element belongs to the normal
four-group, whose other nonidentity elements include `x_21`.

Every representation of `S_4` of dimension at most two kills
that normal four-group: its possible irreducibles have dimensions
one and two and factor through the sign quotient or the quotient
`S_4/V_4~=S_3`. Therefore the target `C_2` acts trivially on
the two-dimensional fiber in (8). Let `n_+,n_-` be the positive
and negative dimensions for the source `C_2`, with
`n_++n_-=2`.

The group `K_Q x K_P` acts transitively on the nine characters.
Inducing the fiber from the product of the two `C_2` stabilizers
shows that this 18-dimensional subspace has representation

```text
(n_+*1 direct-sum n_-*sgn direct-sum 2*tau)_Q
  tensor (1 direct-sum tau)_P.                       (9)
```

Here induction from the trivial character of `C_2` to `S_3`
is `1+tau`, and induction from its sign character is `sgn+tau`.
Consequently the contribution of (9) to the same `tau_Q`
multiplicity space used in (6) is exactly

```text
M_nonzero = 2*1 direct-sum 2*tau.                    (10)
```

All remaining contributions to that multiplicity space come from
the `E`-trivial subspace. That subspace carries an exact
representation of `K_Q x G_*`. Its `tau_Q` multiplicity space
is therefore an actual representation of the full group `G_*`,
not merely of `K_P`.

## 6. Both possible head complements are impossible

If `dim(sigma)=3`, equations (4) and (6) give only one trivial
`K_P` constituent in `M_F`. But the subrepresentation (10)
already requires two. An additional subrepresentation cannot
subtract a constituent. This is a contradiction.

If `dim(sigma)=6`, equations (4), (6), and (10) leave the
`E`-trivial `tau_Q` multiplicity space with restriction

```text
M_zero|K_P = 2*sgn.                                 (11)
```

It has dimension two. Every representation of `G=GL_3(F_2)`
of dimension at most two is trivial, by the appendix (or directly
by perfectness and the commuting-transvection argument). Its
restriction to `K_P` must therefore be `2*1`, contradicting
(11).

These contradictions prove that a sole rank-one `N` orbit with
fiber dimension one is impossible, independently of the size or
tail action of its `N`-trivial complement.

## 7. Dimension bound and its precise compactness consequence

The head mark is nontrivial only if `D=h a_1 h` is nontrivial,
so some nonzero `N`-character must occur. If the total dimension
is less than 98, the orbit sizes `49,168,294` allow only one
rank-one orbit with fiber dimension one. The result just proved
excludes this. Therefore

```text
every exact head-retaining representation of Xi has dimension >=98.
```

There is also a positive, unspecified gap when dimensions are
restricted to at most 97. For each such dimension, the space of
exact representations of the finite factors `F,J` which agree
on `L'` and satisfy `||pi_F(w)-I||=2` for the head involution
`w=x_13,Q` is closed in a finite product of compact unitary
groups. The maximum of the first-braid and TS defects is continuous.
It cannot vanish on this space, since a zero would give an exact
head-retaining representation of `Xi`. Taking the finite union
of these compact spaces gives a strictly positive minimum whenever
the union is nonempty; if it is empty, any positive bound holds
vacuously.

This compactness argument supplies no numerical constant and no
uniform bound over all dimensions. The full non-MF gap remains
unproved.

## Appendix: elementary finite-character data

For completeness, all character classification used above can be
obtained without a computational character table. Rational canonical
forms over `F_2` give six conjugacy classes in `G`, with orders
and sizes

```text
order:       1    2    3    4    7    7
class size:  1   21   56   42   24   24.
```

The involutions are the 21 rank-one nilpotent transvections.
Order-four elements have one three-by-three unipotent Jordan block.
Order-three elements have a one-dimensional fixed space and one
irreducible quadratic block. The two irreducible cubic polynomials
give the order-seven classes. Their centralizer orders are
`168,8,3,4,7,7`, respectively, yielding the displayed sizes.

Subtracting the trivial constituent from the seven-point permutation
representation gives the irreducible character

```text
chi_6=(6,2,0,0,-1,-1).
```

It is irreducible because the seven-point action is doubly transitive;
equivalently its squared character norm is one. A point or covector
stabilizer is `S_4`. Its sign character induces the character

```text
chi_7=(7,-1,1,-1,0,0),
```

whose squared norm is also one. The induced values follow from the
six transpositions, three double transpositions, eight three-cycles,
and six four-cycles of `S_4` and the centralizer orders above.

Let `tau_2` be the two-dimensional representation of `S_4` that
factors through `S_4/V_4`. Its induction to `G` has character

```text
Ind(tau_2)=(14,2,-1,0,0,0).
```

The restriction of `chi_6` to `S_4` is
`1+tau_2+standard_3`, so Frobenius reciprocity puts exactly one
copy of the six-dimensional representation in this induction.
Removing that actual constituent gives an honest representation
with character

```text
chi_8=(8,0,-1,0,1,1),
```

again of squared norm one. Along with the trivial representation,
the degrees so far are `1,6,7,8`, whose squared sum is 150.
There are six conjugacy classes, hence precisely two remaining
irreducibles. Their squared degrees sum to `168-150=18`, so
both have degree three.

The group `G` is perfect: elementary transvections generate it,
and each is a commutator `[x_ik,x_kj]=x_ij` with distinct
indices. Therefore the determinant of any representation is
trivial. In a nontrivial three-dimensional irreducible, a
transvection cannot act trivially, since all transvections are
conjugate and generate the group. Its determinant-one involution
therefore has negative rank two and trace minus one.

The full list of irreducible dimensions and negative involution
ranks is consequently

```text
dimension:      1   3   3   6   7   8
negative rank:  0   2   2   2   4   4.
```

This also proves that every representation of dimension at most
two is trivial. The two three-dimensional irreducibles restrict
to the sign twist of `standard_3` in `S_4`: both involution
classes have trace minus one, whereas `standard_3` has
transposition trace plus one, and all sums of one- and
two-dimensional representations have trivial normal-four-group
action. This establishes every restriction and dimension fact
used in the proof.
