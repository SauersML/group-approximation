# Central finite-packet cuts give a compressed shift with two defects

2026-09-08. The natural compression of the stable letter by a
finite-subgroup invariant projection is an exact partial isometry.
Its initial and final defects are both explicit. In finite
dimensions they have equal rank; a regular finite-packet model
retains both. The same calculation applies to matching central
isotypic cuts of every subgroup of the intertwined finite group.

This tests a specified compressed-shift formula. It does not rule
out noncentral or multiplicity-dependent decoding, and does not
decide the four-error gap for `Gamma_triangle`.

## 1. The exact finite data and the general projection formula

Use the authenticated finite data and admissible matrix tuples from
[the four-error matrix criterion](jacobson-coherent-quotient-and-four-word-matrix-gap-2026-09-08.md).
To distinguish the individual tail factor from the large finite
packet, write

```text
G=GL_3(F_2),
A=tau(G),          B_0=delta(G),
P=G_P={(g_A,g_(B_0)):g in G} <= A x B_0.
```

Thus `P` is the prescribed diagonal copy inside two commuting
copies of `G`. The stable-letter matrix `T` exactly satisfies

```text
T rho_P(g) T^*=rho_(B_0)(g)       for every g in G.     (1)
```

The other exact intertwining condition sends `G_Q` to `A`.
The formulas below use (1) and the exact `A x B_0` table.
They therefore hold on the entire admissible matrix domain,
independently of the values of its four remaining word errors.

Let `K<=G` be any subgroup, and let `e` be a central
self-adjoint projection in the finite group algebra `C[K]`.
Evaluate the same element in the two copies in (1):

```text
C=rho_(B_0)(e),          D=rho_P(e).
```

These are projections. Moreover,

```text
[C,D]=0,                T D T^*=C.                   (2)
```

To check the first identity, `C` commutes with every `A(k)`
because the two group factors commute. It commutes with every
`B_0(k)`, `k in K`, because `e` is central in `C[K]`.
Hence it commutes with each `P(k)=A(k)B_0(k)` and with
their linear combination `D`. The second identity follows by
linearity from (1).

Set

```text
q=C D,                  S=C T C.
```

Then `q` is a projection, and `C T=T D` gives

```text
S=T q,
S^*S=q,
SS^*=T q T^*.                                         (3)
```

Both supports in (3) lie under `C`, so `S` is a partial
isometry in the same square corner `C M_d(C) C`. Its two
defect projections are

```text
C-S^*S=C(1-D),
C-SS^*=T D(1-C)T^*.                                  (4)
```

In finite dimensions, (2) gives `rank(C)=rank(D)`. Removing
their common intersection `q` yields

```text
rank(C(1-D))=rank(D(1-C)).                             (5)
```

In particular, either both defects vanish or both are nonzero.
When they are nonzero, both have operator norm one. Replacing
the matching cuts `C,D` by `1-C,1-D` interchanges the two
untransported defect projections. Passing from an invariant cut
to its augmentation complement does not remove a defect.

Equations (2)--(4) are valid in every unitary representation,
without finite-dimensionality. The finite-dimensional step is
the equality of finite ranks in (5). There is no unproved
infinite-group invariant-vector estimate in this calculation.

This statement concerns the specified occurrence `C T C` with
matching central cuts. It does not cover an arbitrary operation
using several noncommuting cuts, arbitrary multiplicity subspaces,
or finite-packet matrix coefficients outside this interface.

## 2. The invariant-cut defects in every irreducible type

Take `K=G` and its averaging idempotent. Write

```text
p_A=|G|^(-1) sum_g rho_A(g),
p_B=|G|^(-1) sum_g rho_(B_0)(g),
p_P=|G|^(-1) sum_g rho_P(g).
```

Averaging one factor after averaging the diagonal gives

```text
p_P p_B=p_B p_P=p_A p_B=:q.                            (6)
```

For example, expand the product as the average of
`A(g)B_0(gk)` over `g,k in G`, and change the second
index from `k` to `gk`. Thus, with

```text
C=p_B,
H=p_B-p_A p_B,
R=p_P-p_A p_B,
S=p_B T p_B,
```

the concrete formula is

```text
S=Tq,
S^*S=C-H,
SS^*=C-T R T^*,
rank(H)=rank(R).                                      (7)
```

The projection `R` is precisely the additional invariant space
of the diagonal action which is not invariant under the two
factors separately. It is generally nonzero.

Here is its complete irreducible decomposition. For any exact
finite-dimensional representation of `A x B_0`, write

```text
V=directSum_(sigma,tau in Irr(G))
       V_sigma tensor V_tau tensor C^(m_(sigma,tau)).
```

Let `d_sigma=dim(V_sigma)` and let `bar(sigma)` denote the
contragredient irreducible representation. On the summand
`V_sigma tensor V_tau`, the projection `p_B` is nonzero
exactly when `tau=1`, in which case it is the identity.
The product `p_Ap_B` is nonzero exactly when both types are
trivial. Hence

```text
rank(H)=sum_(sigma!=1) d_sigma m_(sigma,1).             (8)
```

The diagonal invariant space is naturally the intertwiner space
from `bar(V_sigma)` to `V_tau`. By the finite-dimensional
Schur lemma it has dimension one when `tau=bar(sigma)` and
zero otherwise. Removing the trivial-trivial summands gives

```text
rank(R)=sum_(sigma!=1) m_(sigma,bar(sigma)).             (9)
```

These formulas include every irreducible type and arbitrary
multiplicities. In particular, they exhibit the terms lost by
the false replacement `p_P=p_Ap_B`.

In the regular representation of `A x B_0`, the multiplicity
of `sigma tensor tau` is `d_sigma d_tau`. Both (8) and
(9) equal

```text
sum_(sigma!=1) d_sigma^2=|G|-1=167.                    (10)
```

Equivalently, `p_B,p_P,q` have ranks `168,168,1`.

This counterprofile occurs in the full admissible finite-packet
domain, not only in an isolated `A x B_0` representation.
The earlier criterion constructs an admissible tuple using the
regular representation of the large packet
`mathcal B=GL_6(F_2) x delta(G)`, glued to the appropriate
multiple of the regular representation of the other finite
packet `mathcal C`, with an exact `F` intertwiner `T`.
Its restriction to `A x B_0` is a positive integer multiple
of the regular representation just considered. The head survives,
and both defects in (7) are nonzero with equal rank.

This is not an exact representation of `Gamma_triangle`: no
smallness, much less vanishing, of its four word errors is being
asserted. It proves that the exact finite tables and exact
`F` intertwining alone cannot discard the second defect in
this particular compressed-shift formula.

## 3. One transported pair need not give an algebra endomorphism

There is a further elementary obstruction to using (2) as an
endomorphism of a bounded finite-dimensional algebra. The algebra
generated by the two commuting projections `C,D` has dimension
at most four. But (2) transports only `D` to `C`; it does
not say that conjugation by `T` preserves that algebra.

Here is a finite exact countermodel to that inference. For any
nontrivial finite group `G`, work on `ell^2(G^3)`, with
basis labelled by `(x,y,z)`. Let `G_Q,A,B_0` act by left
translation on the first, second and third coordinates,
respectively. Let `P` be the diagonal of the last two factors.
Define a permutation unitary by

```text
T delta_(x,y,z)=delta_(y^(-1) z,x,y).                   (11)
```

The labelling map is bijective: its inverse sends `(a,b,c)`
to `(b,c,ca)`. Direct substitution gives

```text
T rho_Q(g)T^*=rho_A(g),
T rho_P(g)T^*=rho_(B_0)(g).                           (12)
```

Thus this model satisfies the entire two-factor `F` intertwining.
For the invariant cuts in Section 2 it also gives

```text
T p_B T^*=p_Q.                                       (13)
```

Indeed, in output coordinates `(a,b,c)`, conjugation of the
third-coordinate action sends

```text
(a,b,c) |-> (c^(-1) g c a,b,c).
```

Averaging over `g` is therefore averaging left translation on
the first coordinate, proving (13). Both `p_B` and `p_P`
act identically on the first tensor factor, so

```text
Alg(p_B,p_P) <= I_(ell^2(G)) tensor B(ell^2(G^2)).
```

The nontrivial proper first-coordinate projection `p_Q` is not
in this algebra. Consequently

```text
Ad(T)(Alg(p_B,p_P)) is not contained in Alg(p_B,p_P).   (14)
```

This example extends to the full exact admissible finite-packet
domain. Inside

```text
mathcal B=GL_6(F_2) x G
```

the subgroup `J_0=G_Q x A x B_0` is the indicated product
of three copies of `G`: the first two are the two disjoint
three-coordinate blocks in `GL_6`, and the third is the
external factor. The regular representation of `mathcal B`
restricts to

```text
[mathcal B:J_0]=|GL_6(F_2)|/168^2=714240
```

copies of the regular representation of `G^3`. Identify these
copies with the space used in (11), and apply its permutation
unitary separately on every copy. Equations (12)--(13) then hold
in dimension `d=|mathcal B|`, while the entire `mathcal B`
table is exact. The head survives in this regular representation.

For the other finite packet
`mathcal C=GL_5(F_2) x GL_3(F_2)`, take `2016` copies of
its regular representation. Both this representation and the
fixed regular `mathcal B` representation restrict on the full
shared subgroup

```text
Z=GL_5(F_2) x GL_2(F_2)
```

to `56448=2016*28` copies of its regular representation.
Conjugate only the `mathcal C` representation by a unitary
intertwiner of these restrictions. This makes both finite packet
tables and their full intersection exact, and leaves the chosen
`mathcal B` representation and `T` unchanged. It therefore
preserves the entire exact `F` intertwining in (12).

The failure (14) also persists: after the chosen restriction
identification, its algebra acts identically on each first
`ell^2(G)` tensor factor and on the copy multiplicity space,
whereas `p_Q` is a nontrivial projection on the first factor.
Thus (14) is a counterexample on the actual admissible domain
with the head retained. No smallness of the four remaining word
errors is claimed. In particular, this still does not construct
an approximate representation with small relator defects for
`Gamma_triangle`.

## 4. Exact diagonal covariance can have no invariant corner at all

The invariant corner `p_B` need not detect a surviving mark
under the reduced `A x B_0` and diagonal-covariance conditions.
There are finite-dimensional examples in which `A` and `B_0`
are faithful, `rho_P` and `rho_(B_0)` are equivalent, and

```text
p_B=p_P=0.                                           (15)
```

The following construction proves this without selecting only
one favorable irreducible type. It applies to any finite simple
group with at least two nontrivial complex irreducible types,
including `GL_3(F_2)`.

Let `I` be its set of nontrivial irreducibles. For each
`tau in I`, choose an irreducible `sigma(tau) in I` different
from `bar(tau)`. Write `N_(sigma,tau)^lambda` for the tensor
product multiplicity of `lambda` in `sigma tensor tau`.
The chosen tensor product has no trivial constituent. Thus

```text
P_(tau,lambda)
 =N_(sigma(tau),tau)^lambda d_lambda
    /(d_(sigma(tau)) d_tau),            tau,lambda in I
```

is a matrix of nonnegative rational numbers whose row sums are
one, by the tensor-product dimension formula.

Choose a rational stationary probability vector `p` for this
finite stochastic matrix. Such a vector exists: the usual
Cesaro averages of iterates of any probability vector have a
stationary accumulation point, and the resulting nonempty
stationary simplex is defined by rational linear equations and
inequalities, so it has a rational vertex.

Choose a positive integer `M` clearing all denominators in

```text
m_tau=M p_tau/(d_(sigma(tau)) d_tau),
```

and put

```text
V=directSum_(tau in I)
      (V_(sigma(tau)) tensor V_tau)^(directSum m_tau). (16)
```

Let `A` act on the first tensor factors and `B_0` on the
second. The multiplicity of `lambda in I` in the `B_0`
action is

```text
m_lambda d_(sigma(lambda))=M p_lambda/d_lambda.
```

Its multiplicity in the diagonal action is

```text
sum_tau m_tau N_(sigma(tau),tau)^lambda
 =(M/d_lambda) sum_tau p_tau P_(tau,lambda)
 =M p_lambda/d_lambda.                               (17)
```

Neither action has a trivial constituent. Therefore they are
unitarily equivalent, and a unitary `T` satisfying (1) exists.
Equation (15) follows. At least one summand in (16) is present.
Every active first-factor and second-factor irreducible is
nontrivial, hence faithful because the finite group is simple.
Thus both `A` and `B_0` are faithful, and in particular every
nonidentity involution in `A` survives.

One can also define `rho_Q(g)=T^*rho_A(g)T`. It commutes
with `rho_P(G)` because `A` commutes with `B_0`, and
then both equalities in (12) hold. This retains a `G_Q` mark
while satisfying the reduced exact `F` intertwining. It does
not establish the required commutation of `G_Q` with `A`,
or an extension to the large `GL_6` packet. Those additional
relations are outside this construction.

## 5. Finitary cuts have explicitly matched defects in every representation

There is a stronger obstruction for projections in the group algebra
of the finitary normal subgroup `L`. This includes noncentral cuts
of local `GL_6` groups. It does not include every projection of the
large packet `mathcal B`, whose tail factor is not finitary.

Use the literal shift and finitary subgroup authenticated in
[the ascending-corner description](jacobson-coherent-group-is-an-ascending-corner-extension-2026-09-08.md).
Let `p` be a projection in `C[L]` and set

```text
q=t^* p t.
```

The finitely many group elements in the support of `p` are
supported on a finite set of binary coordinates `E`. Extend the
shift bijection `E -> E-1` to a permutation of the finite union
`E union (E-1)`, acting identically outside it. This gives an
element `a in L` whose conjugation agrees with `t^*(-)t` on
that entire coordinate subgroup. Consequently `q=a p a^*`.
Local finiteness places `a` and all the group elements in the
supports of `p,q` inside one finite subgroup `F<=L`.

In the finite-dimensional algebra `A=C[F]`, let

```text
v=polar(qp).
```

Then `v^*v<=p` and `vv^*<=q`. In each simple matrix block
of `A`, the projections `p,q` have equal rank because they
are conjugate by `a`. The supports `v^*v,vv^*` also have
equal rank. Their complementary projections therefore have
equal rank in each block. Choosing an isometry between their
ranges, separately in each block, gives `y in A` with

```text
y^*y=p-v^*v,             yy^*=q-vv^*.                 (18)
```

The initial supports and the final supports of `v,y` are
orthogonal. Thus `v+y` is a partial isometry with initial
projection `p` and final projection `q`. Since `tqt^*=p`,

```text
t(v+y) is a unitary in the p corner.                  (19)
```

On the other hand `ptp=tqp`, so its polar partial isometry
is `tv`. This assertion is valid under every unitary group
representation: `qp` belongs to a finite-dimensional algebra,
and its polar factor and support projections are obtained by
functional calculus on a finite spectrum, preserved by every
star homomorphism. Equation (19) is an explicit unitary extension
of this polar factor. Its two missing supports are

```text
p-v^*v,             t(q-vv^*)t^*,                     (20)
```

and the partial isometry `ty` matches them. Either both images
in any representation vanish or both are nonzero. This is
stronger than a comparison of total finite-dimensional ranks.

Finite sums, products, adjoints, and finite-dimensional functional
calculus on finitely many elements of `C[L]` remain in one
finite group algebra. Finitely many conjugations by the second
local packet or the coherent `GL_3` also remain in `C[L]`,
because `L` is normal. Thus those operations on a finitary
isotypic cut cannot escape (18)--(20).

An arbitrary matrix-dependent projection in a multiplicity space
is outside this assertion. If a finite group `F` acts as
`directSum_k V_k tensor M_k`, group-algebra cuts act on `V_k`
and identically on `M_k`. A unitary implementing the same
finite-core conjugation as `t` differs from it by a unitary
in `directSum_k I_(V_k) tensor B(M_k)`. Branching multiplicities
alone do not control this relative commutant or the images of
projections chosen within the spaces `M_k`. No one-sided
containment for those projections is proved here.

## 6. The consequence for this proposed decoder

The explicit central-cut occurrence `S=C T C` is completely
decoded by (3)--(4). Its missing term is the second defect,
which is a projection rather than an uncontrolled small error.
For the invariant cut it is the transported nontrivial diagonal
invariant sector described in (9). The regular admissible domain
retains that term, and the reduced fusion model shows that the
chosen invariant corner can also vanish despite a faithful mark.

Accordingly, a proper-isometry argument cannot follow by dropping
the extra diagonal invariants, changing to the complementary
augmentation cut, or treating one transported projection pair as
an invariant algebra. An argument using a different occurrence
must actually prove the needed containment or eliminate the
opposite defect using additional relations. This artifact proves
no such elimination and adds no alternative open gap criterion.
