# The whole-column normalizer cover has marked LEF models

2026-09-08. Let `A` be an elementary abelian `2`-group, regarded as
an `F_2`-vector space, and let

```text
K=H_1 * ... * H_m * F_r,
```

where every `H_i` is finite and `F_r` is a finitely generated free
group. For **every** linear action of `K` on `A`, the semidirect
product `A semidirect K` is LEF. Countability of `A`, as in the
application below, is not needed for this finite-local assertion.

There is a direct finite-vector-space proof. It avoids rationalizing
orbit frequencies or matching several probability distributions.
The resulting models can be represented by permutation matrices, or
after a finite Fourier transform by signed permutation matrices.

Applied to the Jacobson ring, the theorem supplies marked LEF models
for the entire abelian root column and its mixed involution, with
the acting group kept as the abstract free product
`GL_2(F_2) * C_2`. This is a proper cover of the corresponding literal
normalizer subgroup, with an explicit nontrivial actor kernel below.
It is not an identification with that subgroup,
and is not a model of all the coherent Jacobson relations.

This particular cover is finitely generated. Its finite residual
and its finite-dimensional unitary residual are both exactly
`(JQJ) directSum (JQJ)` inside the additive column. Thus its head
survives the LEF models while every exact finite-dimensional unitary
representation kills it. In particular the cover is not finitely
presented.

## 1. Extending finite portions of a linear action

Fix a finite-dimensional subspace `A_0<=A`. For each finite factor
put

```text
V_i=span_(F_2){h a : h in H_i, a in A_0}.
```

It is finite-dimensional, contains `A_0`, and is invariant under
`H_i`. Choose one finite-dimensional vector space `W` containing a
fixed copy of `A_0`, with

```text
dim W >= max(dim A_0, dim V_1, ..., dim V_m).
```

For each `i` independently, choose a linear embedding
`j_i:V_i->W` that is the identity on the fixed `A_0`. Transport
the given `H_i` action to `j_i(V_i)` and extend it by the identity
on a chosen complementary subspace of `W`. This gives a genuine
homomorphism

```text
rho_i:H_i -> GL(W).
```

In particular, whenever `a,h a in A_0`,

```text
rho_i(h)a=h a.                                         (1)
```

The embeddings and complementary subspaces for distinct factors need
not agree away from `A_0`. A free product imposes no relation
requiring such agreement.

For each free generator `s` of `F_r`, the original action gives
the partial linear isomorphism

```text
s:A_0 intersect s^(-1)A_0 -> A_0 intersect s A_0.       (2)
```

Its domain and range have equal dimension. Extend it, by completing
bases, to some `rho(s) in GL(W)`. This also realizes the
prescribed inverse action whenever both endpoints lie in `A_0`.

The universal property of the free product now gives one exact
homomorphism

```text
rho:K -> GL(W)                                        (3)
```

extending all these choices. For a word `k=s_1 ... s_l`, if
`a` and all its successive images

```text
s_l a, s_(l-1)s_l a, ..., s_1 ... s_l a
```

belong to `A_0`, equations (1)--(2) imply

```text
rho(k)a=k a.                                         (4)
```

Here each letter is either an element of one finite factor or a
free generator or its inverse. For any prescribed finite collection
of pairs `(k,a)`, enlarging `A_0` to include these finitely many
intermediate images makes (4) hold for all those pairs.

## 2. An elementary finite quotient separating actor words

For completeness, the needed finite quotients of `K` can be built
by the same extension argument on finite sets.

Given finitely many nonidentity actor words, let `P` be a finite
subset of `K` containing `1` and all intermediate points obtained
by applying each chosen word, from right to left, to `1`. For
each finite factor the finite set

```text
H_i P={h p:h in H_i,p in P}
```

contains `P` and is invariant under left multiplication by
`H_i`. Embed these sets independently into one sufficiently large
finite set `Omega`, fixing their common subset `P`. Extend each
factor action by fixing the complement of its embedded set.

For every free generator `s`, the partial bijection

```text
P intersect s^(-1)P -> P intersect s P,
p |-> s p,
```

extends to a permutation of `Omega`. Universality gives
`pi:K->Sym(Omega)`. Every chosen word carries the distinguished
point `1` to its distinct endpoint in `P`, so none of those words
is killed. Applying this to pairwise differences separates any
prescribed finite subset of `K` in a single finite quotient.

This proof uses actual finite-factor actions. It does not assume
that permutations chosen for generators of a finite factor will
automatically satisfy that factor's relations.

## 3. The LEF embedding on an arbitrary finite test set

Write the semidirect-product law as

```text
(a,k)(b,l)=(a+k b,k l).                               (5)
```

Let `E` be any finite subset of `A semidirect K`. Choose a word
for every actor coordinate occurring in `E`. Choose `A_0` to
contain all additive coordinates of `E` and all intermediate
images required to evaluate every such actor word on every such
additive coordinate. Section 1 gives `W` and `rho` with (4)
for all these tests.

Choose a linear retraction `r:A->A_0`; it exists by extending a
basis of `A_0` to a basis of `A`. Regard its values as vectors
in `W`. Section 2 gives a finite quotient `pi(K)` separating
the actor coordinates occurring in `E`.

Define, on `E`,

```text
f(a,k)=((r(a),rho(k)),pi(k))
       in (W semidirect rho(K)) x pi(K).              (6)
```

The target is a finite group. If `(a,k)(b,l)=(c,n)` and all
three elements lie in `E`, then `n=k l` and `c=a+k b`.
All the relevant vectors lie in `A_0`, so (4) gives

```text
r(c)=r(a)+rho(k)r(b).
```

Together with the two exact actor homomorphisms, this proves
`f(a,k)f(b,l)=f(c,n)`.

The map is injective on `E`. Different actor coordinates are
separated by `pi`; with the same actor coordinate, different
additive coordinates are separated because `r` is the identity
on `A_0`. Thus (6) is an injective multiplication-preserving
map on every prescribed finite test set, proving the LEF theorem.

Although `r` is a genuine additive homomorphism on all of `A`,
it is not asserted to intertwine the `K` action on all of `A`.
Only the finitely many required coefficient paths are intertwined.
This distinction is exactly why this construction does not give a
finite quotient of the whole semidirect product with the mark retained.

The group `W semidirect rho(K)` acts faithfully by affine
permutations of the finite set `W`. Tensoring this permutation
representation with the regular permutation representation of
`pi(K)` realizes (6) by permutation matrices. In the Fourier
basis of the additive group `W`, translations become diagonal
sign matrices and `rho(K)` permutes the characters, giving the
equivalent signed-permutation realization. Every retained nonzero
additive element is an involution at operator-norm distance `2`
from identity.

For a countable group, exhausting finite test sets gives an embedding
into a norm matrix corona. Indeed these finite permutation models
have a dimension-independent separation for every nonidentity
image: a nontrivial permutation has a cycle of length at least two,
and the norm of that cycle minus identity is at least `sqrt(3)`.
Thus the theorem also gives MF models, with the additive mark
separated by `2` throughout sufficiently large tests.

## 4. Application to the whole Jacobson root column

Let

```text
J=F_2<S,T | TS=1>,            Q=1-ST,
N=(J,+) directSum (J,+),
K=GL_2(F_2) * <eta | eta^2=1>.                       (7)
```

The constant `GL_2(F_2)` factor acts in the standard way on
the two coordinates of `N`. Define the second factor's action by

```text
eta(a,b)=(Q a+S b,T a).                              (8)
```

The identities

```text
Q^2=Q,     Q S=0,     T Q=0,     TS=1,     Q+ST=1
```

give `eta^2(a,b)=(a,b)`. Thus (7)--(8) define a genuine
linear action of the abstract free product, and the theorem proves

```text
N semidirect (GL_2(F_2) * C_2) is LEF and MF.          (9)
```

The marked additive element `(Q,0)` is nonzero. For example,
in the faithful unilateral shift representation of `J`, `Q`
projects onto level zero. The finite models in Section 3 retain
this mark at distance `2`.

This realizes the distinction between pointwise and uniform covariance
inside a genuine group with finite local models.
It includes a genuine additive map on the entire two-coordinate
column, the entire constant `GL_2(F_2)` table, the mixed
involution, and every fixed covariance equation for (8). At each
finite stage all prescribed tests are exact.

## 5. An explicit increasing sequence of Jacobson windows

The following version fixes the finite linear spaces without using
the separate factor embeddings of Section 1. For `n>=2`, put

```text
A_n=span{(S^i T^j,0),(0,S^i T^j):0<=i,j<n},
F(a,b)=(Q a+S b,T a),
W_n=A_n+F(A_n).                                      (11)
```

The normal monomials `S^i T^j` form a basis of `J`, as
verified by the faithful unilateral shift calculation in the
[ascending corner extension](jacobson-coherent-group-is-an-ascending-corner-extension-2026-09-08.md).
Thus `dim A_n=2n^2`. The involution identity `F^2=1`
makes `W_n` invariant under `F`, and

```text
dim W_n<=4n^2,             W_n<=A_(n+1).              (12)
```

For the last inclusion, left multiplication by `S` or `T`
changes a normal-monomial index by at most one. Moreover
`Q S^i T^j=0` for `i>=1`, while
`Q T^j=T^j+S T^(j+1)`.

Choose a complement `W_n=A_n directSum D_n`. On `W_n`
let the involution actor act by the actual map `F|W_n`, and
let the constant `GL_2(F_2)` act by its natural action on
`A_n` and by the identity on `D_n`. Both factor tables are
exact, so they define

```text
rho_n:K -> GL(W_n).
```

Choose any linear retraction `r_n:N->W_n`. It can be obtained
entirely from finite choices: first truncate to `A_(n+1)`,
then project onto `W_n` along a complementary subspace. Define
the additive model by translation through `r_n(a,b)` on the
finite vector space `W_n`.

For every `c in A_n`, covariance under the involution is exact:

```text
rho_n(eta)r_n(c)=F(c)=r_n(F(c)).                      (13)
```

The same identity holds for every constant group element, since
that factor preserves `A_n`. Every fixed coefficient and all
intermediate coefficients of any fixed actor word lie in `A_n`
for all sufficiently large `n`. Thus every fixed covariance
test is eventually exact. The additive map is genuine on all of
`N` at each stage, but its kernel is not asserted to be invariant
under the actors on all of `N`.

Since `(Q,0) in A_n` for `n>=2`, its translation is always
nonzero and its permutation unitary has distance `2` from identity.
Taking a direct product with finite quotients of `K` that separate
successively larger finite sets of actor words turns these explicit
windows into the marked LEF sequence of (9).

## 6. Finite generation and the exact finite-dimensional residual

Write `H_col=N semidirect K` for the group in (9), and let

```text
I=JQJ.
```

The usual matrix-unit calculation identifies `I` with the
finitary ideal, spanned by `S^i Q T^j`, and gives

```text
J/I ~= F_2[z,z^(-1)],       S |-> z, T |-> z^(-1).     (14)
```

These ring identities are proved in the
[ascending corner extension](jacobson-coherent-group-is-an-ascending-corner-extension-2026-09-08.md).

First, `H_col` is finitely generated. Let `M` be the
`F_2`-span of the `K`-orbit of `(1,0)` in `N`.
It is invariant under the constant shears and coordinate swap.
Subtracting a vector from its image under a shear, and then
swapping coordinates, shows that whenever `(a,b) in M`, each
of `(a,0),(0,a),(b,0),(0,b)` lies in `M`. The equations

```text
F(0,a)=(S a,0),          F(a,0)=(Q a,T a)
```

therefore show that the coefficients occurring in `M` are closed
under left multiplication by `S` and `T`. They contain `1`
and are closed under addition, hence contain all of `J`.
Thus `M=N`. A finite generating set of `K`, together with
the single translation `(1,0)`, generates `H_col`.

Now consider any exact homomorphism `rho:H_col->U(d)`.
The additive group `N` has exponent two, so its commuting
unitaries are simultaneously diagonalizable. They have only
finitely many joint characters, a set

```text
Omega subset J^* x J^*,
J^*=Hom_(F_2)(J,F_2),
```

where `(lambda,mu)` denotes the sign character
`(a,b)|->(-1)^(lambda(a)+mu(b))`. Normalization by `K`
permutes this finite set. The dual of (8) is

```text
F^*(lambda,mu)=(lambda Q+mu T,lambda S),              (15)
```

where `lambda S` means `a|->lambda(Sa)`, and likewise
for the other coefficients.

Let `V` be the finite-dimensional `F_2`-span of `Omega`.
The constant shears and swap, by the same coordinate-extraction
argument used above, imply

```text
V=W directSum W
```

for a finite-dimensional subspace `W<=J^*`. Applying (15)
to `(lambda,0)` and `(0,lambda)` shows that `W` is
invariant under precomposition by left multiplication by `S`
and by `T`. On `W` their compositions satisfy

```text
(lambda T)S=lambda,
```

because `TS=1`. Finite dimensionality makes the two linear
endomorphisms inverse in both orders. Hence

```text
lambda Q=lambda-lambda ST=0       for every lambda in W.
```

The space `W` is invariant under precomposition by every left
coefficient `b in J`, since `S,T` generate the ring. Apply
the last equation to `lambda b`, and evaluate at `a in J`:

```text
lambda(b Q a)=0             for every a,b in J.        (16)
```

Thus all joint characters kill `I directSum I`. Every exact
finite-dimensional unitary representation of `H_col` kills
that subgroup.

Conversely, every element outside `I directSum I` survives
in a finite group. If its actor coordinate is nonidentity, use
the quotient `H_col->K` and Section 2. Otherwise it is a
pure translation with at least one nonzero Laurent coordinate
under (14). Choose a nonzero element `z_0` in a sufficiently
large finite extension of `F_2` where that Laurent polynomial
does not vanish. This is possible after clearing its negative
powers, since a nonzero polynomial has at most its degree many
roots.

The ring homomorphism `J->F_(2^f)` given by

```text
S |-> z_0,       T |-> z_0^(-1),       Q |-> 0
```

maps the column to `F_(2^f)^2`. Let constant actors act
naturally and let `eta` act by

```text
[ 0          z_0 ]
[ z_0^(-1)   0   ].
```

This is a genuine finite affine quotient of the whole semidirect
product, and it detects the chosen translation. Consequently

```text
intersection of kernels of all finite-group homomorphisms
 = intersection of kernels of all finite-dimensional unitary maps
 = I directSum I.                                    (17)
```

The middle equality also follows because every finite group has
a faithful finite-dimensional unitary representation.

In particular `(Q,0)` dies in every exact finite-dimensional
representation despite surviving the LEF models at distance `2`.
The group `H_col` is therefore not residually finite. A finitely
presented LEF group is residually finite: put the identity, all
generators and their inverses, and all prefixes of a finite
presentation's relators and of a chosen nonidentity word into the
test set; an injective partial multiplication map then
extends on the generators to a finite quotient retaining that word.
Together with finite generation and (9), this proves that
`H_col` is not finitely presented.

## 7. Relation to the coherent Jacobson group, and the missing relations

In the faithful coherent group
[identified as an ascending corner extension](jacobson-coherent-group-is-an-ascending-corner-extension-2026-09-08.md),
write

```text
Z(a,b)=x_13(a)x_23(b),

      [ Q  S  0 ]
h  =  [ T  0  0 ].
      [ 0  0  1 ]
```

The column roots commute, so `Z` embeds the additive group
`N`. Direct multiplication gives the full, all-coefficient
normalization identity

```text
h Z(a,b) h=Z(Q a+S b,T a).                            (18)
```

The constant `GL_2(F_2)` acting on coordinates `1,2`
normalizes the same column. Therefore sending the two actor factors
of (7) to this constant group and to `h` gives a surjection
from the LEF group in (9) onto the subgroup generated by the
column and these actors in `Gamma_triangle`. Its restriction to
`N` is injective.

The actual actor subgroup is not the abstract free product. Here
is an explicit missing actor relation. In the constant `GL_2`
factor let `u=x_12(1), v=x_21(1)`, and write `h=eta`
when discussing the abstract free product. Set

```text
r=[u,h v h]=u h v h u h v h.                         (19)
```

In the literal two-coordinate Jacobson matrices, direct multiplication
gives

```text
    [ S Q  S^2 ]
B = [  0    0  ],           h v h=I+B,
E_12 B=0,          B E_12=E_12 S Q.
```

Both `E_12` and `B` square to zero, and the higher products
in their commutator vanish. Thus the literal image is

```text
r=x_12(SQ),                  r^2=1.                 (20)
```

It is nonidentity: `SQ` sends level zero to level one in the
unilateral model. In the abstract free product, (19) is a
cyclically reduced alternating word of length eight. Every positive
power remains reduced, so `r` has infinite order there and
`r^2!=1`. The natural actor map therefore has a nontrivial kernel.
The faithful LEF models of the cover eventually retain this very
word `r^2`; they do not impose (20).

Thus even this explicit actor relation is missing, in addition to
the third-coordinate relations described next. LEF and MF do not
pass to arbitrary quotients, so (9) does not establish either
property for the image subgroup or for `Gamma_triangle`.

The full coherent finite `GL_3(F_2)` packet also requires the
Weyl element `b=w_23` and roots into the third row. They lie
outside the displayed normalizer interface: conjugation by `b`
sends

```text
x_23(a) |-> x_32(a),
x_13(a) |-> x_12(a),
```

so it does not preserve `N`. In particular no images for all
`x_31(a),x_32(a)` and their cross-column Steinberg relations
have been supplied here. Nor have the complete third-packet
relations involving `b`, including `(h b)^3=1` and the
coherence transport, been imposed on the finite models.

This is consequently an obstruction to deriving marked collapse
from the whole-column normalizer equations alone. It does not
remove those missing relations or settle the four-error matrix
gap. The uniformity requirement in
[the root-kernel theorem](../uniform-root-kernel-invariance-kills-one-sided-defect.md)
still cannot be obtained merely by replacing its partial column
model with this larger exact-on-every-fixed-test normalizer cover.
