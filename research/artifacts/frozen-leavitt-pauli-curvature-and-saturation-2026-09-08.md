# Frozen Leavitt factors do not give small invariant curvature supports

2026-09-08. Exact handwritten finite-group, matrix, and trace calculations.
No code, build, enumeration, or numerical experiment is used.

This is a counterexample to an inference from exact finite-factor
profiles and localized curvature to small reducing containment under
unchanged actors. The curvature is in the actual certificate word
`rho_1=j^2`. It is not a construction with small full nine-word defect,
and it does not refute a repair that changes the actors.

## 1. An unbounded family of exact frozen-factor models

Fix a prime `p>=5` and set `G=PSL_2(F_p)`. Let `s,c` denote the
projective classes of the matrices

```text
S = [ 0 -1 ],      C_0 = [ 0 -1 ] = S [ 1 1 ].
    [ 1  0 ]            [ 1  1 ]         [ 0 1 ]
```

Since `S^2=C_0^3=-I`, their projective orders are two and three.
They generate `G`: `S^(-1) C_0` is the upper unipotent with entry one;
its powers give every upper elementary matrix over the prime field.
Conjugating by `S` gives every lower elementary matrix. Elementary row
reduction shows that these generate `SL_2(F_p)`, and hence its projective
quotient. This argument requires no simplicity theorem about `G`.

For completeness, `|SL_2(F_p)|=p(p^2-1)`: there are `p^2-1` choices
for the nonzero first column and `p` second columns of determinant one.
The central quotient has size

```text
g:=|G|=p(p^2-1)/2.
```

This is divisible by six for `p>=5`, and tends to infinity with the
primes. Let `lambda` be the left regular representation of `G`, on
the basis `e_x`, and work on

```text
H=C[G] tensor C^2 tensor C^2,       n=4g=24k.
```

Write `X,Y,Z` for the usual Pauli matrices, with
`XY=iZ`, `YZ=iX`, and `ZX=iY`. Start with

```text
C = lambda(c) tensor I tensor I,
B_1 = lambda(s) tensor I tensor I,
B_2 = I tensor Z tensor I,
B_3 = I tensor I tensor Z.                             (1)
```

The restriction of a regular representation to a subgroup is a sum of
regular representations, by the coset decomposition. Thus `C` has
each cube-root eigenvalue with multiplicity `n/3`. The two eigenvalues
of `lambda(s)` each occur `g/2` times. Combining these with the two
ancillary signs shows that each of the eight joint characters of
`B_1,B_2,B_3` has multiplicity `g/2=n/8`. Hence (1) has precisely the
frozen regular `C_3` and `C_2^3` profiles.

The construction can be put in the usual single-relative-unitary form
by a global basis change. Its assertions are invariant under that change
of basis.

## 2. A rank-two rotation preserving every finite-factor condition

Let

```text
u=(e_1+e_s)/sqrt(2),          lambda(s)u=u,
tau=c s c^(-1),              T=lambda(tau) tensor I tensor I.
```

The element `tau` is different from `1,s`. It is a nontrivial involution,
and a lift is

```text
C_0 S C_0^(-1) = [ -1 -1 ],
                 [  2  1 ]
```

whose upper-left entry excludes equality with either projective class
of `S`. The supports `{1,s}` and `{tau,tau s}` are therefore disjoint.
Consequently `u` and `lambda(tau)u` are orthogonal.

Let `e_+` be the positive `Z` eigenvector in the last ancillary factor.
Define `K` to act as `exp(i pi X/4)` on

```text
L_0=span(u) tensor C^2 tensor span(e_+)
```

and as identity on its orthogonal complement. This is a rank-two
modification of identity. It commutes with `B_1` because `u` is a
positive eigenvector of `lambda(s)`, and commutes with `B_3` by its
last-factor support. Replace (1) by

```text
C'=C,       B_1'=B_1,       B_2'=K B_2 K^*,       B_3'=B_3. (2)
```

All three `B_i'` are the simultaneous `K` conjugates of the original
`B_i`. Thus their orders, pairwise commutativity, and every joint
eigenvalue multiplicity remain exact. The matrix `C` is unchanged.

The elementary Pauli identity

```text
exp(i pi X/4) Z exp(-i pi X/4)=Y
```

shows that `B_2'` is `Y` on `L_0` and remains `Z` on all other
first-ancillary fibers. In particular

```text
||B_2'-B_2||_(2,n)=2/sqrt(n).                          (3)
```

Only this generator changes. The factor conditions therefore place no
obstacle to this perturbation at the normalized-HS tangent scale.

## 3. The actual certificate residual is exactly rank four

Use the original compiler from the explicit nine-word certificate:

```text
gamma(W)=C W C^(-1),
d=[B_2',gamma(B_1')],    h=gamma^2(d),
a=[d,h],                e=gamma(d),
j=a e a^(-1),           rho_1=j^2.                    (4)
```

Here the commutator convention is `[U,V]=UVU^(-1)V^(-1)`.
Since `gamma(B_1')=T` and both inputs are involutions,

```text
d=B_2' (T B_2' T).
```

Conjugation by `T` moves the exceptional `Y` fiber from `u` to
`lambda(tau)u`. These two fibers are orthogonal, so direct multiplication
gives the following complete table:

| Subspace | `B_2'` | `T B_2' T` | `d` |
|---|---|---|---|
| `span(u) tensor C^2 tensor e_+` | `Y` | `Z` | `iX` |
| `span(lambda(tau)u) tensor C^2 tensor e_+` | `Z` | `Y` | `-iX` |
| Orthogonal complement | `Z` | `Z` | `I` |

In the last row, the notation means the unchanged first-ancillary `Z`
operator on the complementary invariant space. Let `F` be the projection
onto the sum of the first two rows. It has rank four, and

```text
d^2=I-2F.                                              (5)
```

The conjugate form of `j` in (4) is a literal free-product word identity;
it does not depend on any additional Leavitt relations. Hence

```text
rho_1=a C d^2 C^(-1)a^(-1)=I-2P,
P=a C F C^(-1)a^(-1),       rank(P)=4.                 (6)
```

All matrices in (2) define an exact homomorphism from `C_3*C_2^3`.
Moreover (6) is the word `rho_1` of the authenticated native kernel
packet, rather than an auxiliary invented relator.

With normalized trace and Schatten norms, (6) gives

```text
delta:=||rho_1-I||_2=4/sqrt(n),
||rho_1-I||_1=8/n=delta^2/2,
tr(P)=4/n=delta^2/4,
||(rho_1-I)(I-P)||_op=||(I-P)(rho_1-I)||_op=0.          (7)
```

Every nonzero error singular value is two. Thus the residual has no
small-angle energy, and all its delta-rescaled square mass remains in
tails beyond every fixed cutoff as `n` increases.

The scale `delta` in (7) refers only to this one relator. The construction
does not assert that the maximum of the nine defining errors tends to
zero. Accordingly it is not an application or counterexample to the
full-input hypotheses of either Kazhdan curvature-correction theorem.

## 4. Twelve coordinate fibers support the residual

Put

```text
S_0={1,s,tau,tau s} subset G.
```

For `S subset G`, let `chi_S` project onto
`span{e_x:x in S} tensor C^2 tensor C^2`. The rank-four space of `F`
lies inside `chi_(S_0)H`, and `d-I` is supported there on both sides.
Since `C^3=I`, the matrix `h=C^(-1)d C` differs from identity only
on the coordinate set `c^(-1)S_0`.

Therefore `a=[d,h]` is identity outside
`S_0 union c^(-1)S_0`, and has no matrix entries between this set and
its complement. Applying `a` to a vector supported in `cS_0` can
add support only in those two other sets. It follows from (6) that

```text
P <= chi_S,
S=cS_0 union S_0 union c^(-1)S_0,       |S|<=12.        (8)
```

The projection `P` need not be a coordinate projection. Only its
containment in (8) is used below.

## 5. Exact invariant containment has rank at least n/12

Suppose `E` is an orthogonal projection with

```text
P<=E,       [E,C]=[E,B_1']=0.                         (9)
```

The two unchanged group elements generate `G`, so `E` commutes with
`lambda(G) tensor I tensor I`. All diagonal group-coordinate fiber
traces of `E` are consequently equal. Using ordinary, unnormalized
matrix trace `Tr`, each is `rank(E)/g`. Since `P` is contained in
both `E` and `chi_S`, positivity gives

```text
4=Tr(P) <= Tr(chi_S E chi_S)
         = |S| rank(E)/g <= 12 rank(E)/g.              (10)
```

For the first inequality, extend an orthonormal basis of `P H` to one
of `chi_S H`. Every basis vector in `P H` contributes one to the trace
of the positive compression, and the remaining contributions are
nonnegative. Thus

```text
rank(E)>=g/3=n/12.                                    (11)
```

In particular a projection reducing all four generators and containing
their concentrated `rho_1` error must obey (11). Exact factor regularity
does not turn its rank-four support into an `o(n)` reducing support.

The estimate is stated for unchanged `C,B_1'`. No bound is claimed for
support containment after these actors are changed.

## 6. Direct-sum padding does not remove this bound

Let `H` be the original `n`-dimensional summand in `H direct-sum K_aux`,
and keep the two actors in the forms

```text
C_bar=C direct-sum C_aux,
B_bar=B_1' direct-sum B_aux.
```

The auxiliary operators may be arbitrary unitaries. Let `E_bar` be a
projection containing the original `P H` and commuting with these two
padded actors. Compress it to the original summand:

```text
E_00=Pr_H E_bar |_H.
```

This is a positive contraction commuting with `C,B_1'`, hence with the
original regular action. It acts as identity on `P H`; its trace is
at most `rank(E_bar)`. The constant-diagonal argument (10), applied to
`E_00`, yields

```text
4 <= |S| Tr(E_00)/g,
rank(E_bar) >= Tr(E_00) >= g/3=n/12.                 (12)
```

This holds for any padding dimension. If `dim(K_aux)=o(n)`, the
normalized rank in the padded space stays at least `1/12-o(1)`.
Preserving the original summand and its actors is an explicit hypothesis;
the argument does not cover padding accompanied by changes to the old
actor matrices.

## 7. The correction that this example does allow

Undoing `K` in (2) returns to (1). The generator movement is exactly
`2/sqrt(n)=delta/2` by (3), and all frozen factor multiplicities remain
unchanged. At the restored tuple, `B_2` commutes with `C` and `B_1`,
so `d=j=I` and `rho_1=I`.

This is a complete, cheap repair of the displayed one-word curvature.
It explains why the large invariant hull is not an obstruction to every
actor-changing surgery. The example specifically defeats saturation
under the unchanged regular actors; it supplies no failure of a method
allowed to alter them or to use further nine-word compatibility.

The hypotheses of the two Kazhdan correction results include a separate
ordinary all-unitary Hilbert H2 vanishing theorem for the presentation
under study. No such hypothesis for the nine-word quotient is supplied
by this artifact. Even when curvature concentration is available, the
factor-only invariant-support passage refuted above remains a separate
obligation.
