# An explicit 4608-dimensional seed from the projective plane over F8

2026-09-08. Self-contained finite-dimensional character calculation.
No code, build, finite-group enumeration, or numerical experiment
was run. The seed satisfies the first displayed Leavitt `24k`
relation and fails two further coefficient relations explicitly.
It is a reusable exact control, not a model of the full group.

## 1. The marked finite-field assignment

Work over

```text
F=F_8=F_2[alpha]/(alpha^3+alpha+1).
```

The cubic has no root in `F_2` and is irreducible. It gives
`alpha^(-1)=alpha^2+1`, and `1,alpha,alpha^(-1)` are a basis
over `F_2`. In `SL_3(F)` set

```text
c=(123),
b_1=x_12(alpha), b_2=x_12(alpha^(-1)), b_3=x_12(1),
B={x_12(t):t in F}.
```

Thus `B=<b_1,b_2,b_3>` has order eight and is `C_2^3`, while
`c` has order three. Conjugation by `c` cyclically permutes
the indices of the elementary roots. It follows that these
marked elements generate all root subgroups: cyclic conjugation
first gives the roots `12,23,31`, and their commutators give
`13,21,32`. Elementary row reduction over a field then gives
all of `SL_3(F)`. The construction below is in fact a
representation of `GL_3(F)`, so this generation observation
is not needed for its validity.

Use the commutator convention `[x,y]=xyx^(-1)y^(-1)`.
The elementary matrix identity
`[x_ij(t),x_jk(s)]=x_ik(ts)` gives the first relation:

```text
d=[b_2,c b_1 c^(-1)]=x_13(1),
h=c^2 d c^(-2)=x_32(1),
a=[d,h]=x_12(1),
b=c d c^(-1)=x_21(1),
z=a b a^(-1)=(12),
r_*=z c z c=((12)c)^2=I.                              (PI1)
```

This is the same assignment as in
`leavitt-24k-first-relation-has-exact-finite-model`. The gain
here is a much smaller complex representation having exactly
regular restrictions to the two marked finite subgroups.

## 2. Explicit projective permutation spaces

Let `P` be the set of one-dimensional subspaces of `F^3`,
and let `L` be its set of two-dimensional subspaces. Call
these projective points and lines. Every point has seven
nonzero vectors, so

```text
|P|=(8^3-1)/(8-1)=73.
```

Duality gives `|L|=73`. Each line has
`(8^2-1)/(8-1)=9` points. Therefore the incident pairs form
a set `E` of size `73*9=657`.

All three sets have explicit coordinate descriptions:

- Represent a point by its vector whose first nonzero
  coordinate is one.
- Represent a line by a similarly normalized nonzero row
  covector, whose kernel is the line.
- A pair is incident exactly when that covector evaluates
  to zero on that vector.

For `g in GL_3(F)`, act on points by `v -> gv` and on
lines by `ell -> ell g^(-1)`, renormalizing the chosen
representatives. This also permutes the incident pairs.
Hence `C[P]`, `C[L]`, and `C[E]` are explicit unitary
permutation spaces, with no enumeration of group elements.

Let

```text
V={sum_p a_p e_p : sum_p a_p=0} <= C[P].
```

This invariant augmentation space has dimension 72. Its
character is

```text
chi_V(g)=#Fix_P(g)-1.                                 (PI2)
```

We use ordinary, unnormalized characters until Section 5.

## 3. The 512-dimensional incidence-cycle representation

Form the bipartite graph with vertices `P` and `L` and
edges `E`. It is connected: any two distinct points lie
on their unique joining line, and every line contains a
point. Orient each edge from its point to its line, and
define the equivariant boundary map

```text
partial:C[E] -> C[P] direct-sum C[L],
partial(e_(p,ell))=e_ell-e_p.
```

Because the graph is connected, the image of `partial`
is the hyperplane of vertex coefficient sum zero. For a
direct proof, fix a vertex `v_0`; boundaries of paths
produce every `e_v-e_(v_0)`, and these span that hyperplane.
Thus `partial` has rank 145, and its invariant kernel

```text
J=ker(partial)
```

has dimension `657-145=512`. With the inherited inner
product this is a unitary representation. The equivariant
exact sequence

```text
0 -> J -> C[E] -> C[P] direct-sum C[L] -> C -> 0
```

implies its character formula

```text
chi_J(g)=#Fix_E(g)-#Fix_P(g)-#Fix_L(g)+1.             (PI3)
```

Indeed invariant orthogonal complements split each kernel
and image, so traces add. This cycle-space model is enough
for the proof; no irreducibility or representation-theoretic
classification is required.

For a concrete matrix recipe, choose a spanning tree of
the finite incidence graph. Each of its 512 remaining
edges gives a fundamental cycle, producing an explicit
integer basis of `J`. Orthonormalize with its positive
Gram matrix. This supplies unitary matrices from the
657-point edge permutations without a finite-group
regular representation.

## 4. Exact fixed-point counts on the two marked subgroups

First take a nonidentity `u=x_12(t)`, with `t!=0`.
Then `u=I+N`, `N^2=0`, and `N` has rank one. Write
`A=im(N)` and `K=ker(N)`, so `dim A=1`, `dim K=2`,
and `A<=K`.

A projective point is fixed exactly when it lies in `K`:
the only eigenvalue of `u` is one. There are nine such
points. An invariant plane must contain `A`. To verify
necessity, if a plane contains a vector outside `K`, its
image under `N` is a nonzero vector of `A`, which must
also lie in that invariant plane. Otherwise the plane
equals `K`, which also contains `A`. Conversely every
plane containing `A` is invariant. There are nine of
them, corresponding to the points of `F^3/A`.

Among the fixed flags, the line `K` is incident with all
nine fixed points. Each of the eight other invariant
planes intersects `K` in exactly `A`, giving just one
fixed incident point. Consequently

```text
#Fix_P(u)=9,    #Fix_L(u)=9,    #Fix_E(u)=9+8=17.
chi_V(u)=8,    chi_J(u)=0.                             (PI4)
```

This argument applies to all seven nonidentity elements
of `B`, without any conjugacy-class enumeration.

Next consider `c` and `c^2`. The polynomial
`X^3-1=(X-1)(X^2+X+1)` is separable in characteristic two.
The quadratic factor is irreducible over `F_8`: a root
would have multiplicative order three, which does not
divide `|F_8^*|=7`. Thus the coordinate space decomposes
as a one-dimensional eigenspace `A_c` and an irreducible
two-dimensional invariant space `K_c`.

These are the only invariant subspaces of dimensions one
and two. For example, the coprime polynomial spectral
projections split any invariant subspace across them,
and the quadratic part has no invariant line. They have
zero intersection, so the unique fixed projective point
and line are nonincident. The same decomposition works
for `c^2`. Hence

```text
#Fix_P(c^j)=1, #Fix_L(c^j)=1, #Fix_E(c^j)=0,
chi_V(c^j)=0, chi_J(c^j)=-1,      j=1,2.              (PI5)
```

## 5. Character cancellation in dimension 4608

For any finite-dimensional complex representation `V`,
its exterior square obeys

```text
chi_(Lambda^2 V)(g)=(chi_V(g)^2-chi_V(g^2))/2.         (PI6)
```

This follows by writing the eigenvalues as `lambda_i`:
the exterior-square eigenvalues are `lambda_i lambda_j`
for `i<j`. Here its dimension is
`72*71/2=2556`.

For a nonidentity element `u` of `B`, we have `u^2=I`,
so `(PI4)` and `(PI6)` give

```text
chi_(Lambda^2 V)(u)=(8^2-72)/2=-4.
```

For `c` and `c^2`, both relevant characters of `V`
are zero, so the exterior-square character is zero.
Now define the genuine direct-sum representation

```text
W=Lambda^2 V direct-sum 4(J direct-sum 1).             (PI7)
```

Its dimension and the two marked traces are

```text
dim W=2556+4(512+1)=4608=24*192,
chi_W(u)=-4+4(0+1)=0       (u in B, u!=1),
chi_W(c^j)=0+4(-1+1)=0     (j=1,2).                  (PI8)
```

For a finite abelian group `A`, the multiplicity of a
character `theta` in a representation with character
`chi` is

```text
(1/|A|) sum_(a in A) conjugate(theta(a)) chi(a).
```

Applying this to `(PI8)` shows that every character of
`C_3` occurs `4608/3=1536` times and every character of
`B=C_2^3` occurs `4608/8=576` times. These are exactly
regular multiplicities, not asymptotic ones.

Since `(PI7)` is a representation of the finite matrix
group, equation `(PI1)` remains exact on it. Thus it is
the requested small exact seed for the first relation.

## 6. Producing the frozen relative unitary

The criterion `binary-leavitt-hyperlinear-iff-24k-feasible`
uses `C_k` regular for `C_3` with multiplicity `8k`, and
`D_(i,k)` jointly regular for `C_2^3` with multiplicity
`3k`, in dimension `24k`. For `k=192` these multiplicities
are precisely 1536 and 576 from Section 5.

Choose orthonormal eigenbases for `rho(c)` to conjugate
it to `C_192`. In this basis the three commuting root
involutions still have all eight joint characters with
multiplicity 576, so one further relative unitary `U`
satisfies

```text
rho(c)=C_192,
rho(b_i)=U D_(i,192) U^*       (i=1,2,3).              (PI9)
```

The second unitary is used only to express the root
operators; it does not simultaneously conjugate the
already fixed `C_192`. This is the one-relative-unitary
format of the criterion.

Both basis choices are explicit linear algebra. The
spectral projectors for `c` are three-term Fourier sums;
the joint root projectors are the eight-term sums

```text
(1/8) sum_(t in F_8) (-1)^(theta(t)) rho(x_12(t)),
```

where `theta:F_8->F_2` ranges over linear functionals
in the marked basis `alpha,alpha^(-1),1`. Select bases
from their images and orthonormalize. All starting
permutations have entries zero or one, exterior powers
use integer signs, and the Gram matrices have algebraic
entries. Thus this is an exact algebraic matrix recipe.
No numerical feasibility search or enumeration of
`GL_3(F_8)` is part of the construction.

## 7. A simpler point-only control in dimension 5184

The incidence-cycle space can be omitted if a slightly
larger model is convenient. Put

```text
W_simple=V direct-sum 2 Lambda^2 V.
```

Then

```text
dim W_simple=72+2*2556=5184=24*216,
chi_(W_simple)(u)=8+2(-4)=0,
chi_(W_simple)(c^j)=0       (j=1,2).
```

Its restrictions are 1728 regular copies for `C_3` and
648 regular copies for `C_2^3`. This alternative uses
only permutations of the 73 projective points and
their exterior powers. It gives the same first-relation
identity and the same additional-relator failures below.

Neither construction is asserted to have minimal
dimension among finite-group or relative-unitary models.

## 8. The two additional coefficient relations fail exactly

The finite-field assignment must not be mistaken for
a representation of the full Leavitt unit group. To
record the failure on concrete words, put `gamma=Ad(c)`
and retain `d,h,a` from `(PI1)`. Define

```text
u=[b_2,gamma(b_3)],
w=[gamma^2(b_1),a],
R_0=[u,w],
R_sum=[[b_1,gamma(b_2)],h]
      [[b_3,gamma(b_1)],gamma^2(u)] a^(-1).            (PI10)
```

In the finite-field assignment, elementary commutators give

```text
u=x_13(alpha^(-1)),
w=x_32(alpha),
R_0=x_12(alpha^(-1)alpha)=x_12(1).                    (PI11)
```

For the first factor of `R_sum`,

```text
[b_1,gamma(b_2)]=x_13(alpha alpha^(-1))=x_13(1),
[[b_1,gamma(b_2)],h]=x_12(1).
```

For the second factor,

```text
[b_3,gamma(b_1)]=x_13(alpha),
gamma^2(u)=x_32(alpha^(-1)),
[[b_3,gamma(b_1)],gamma^2(u)]=x_12(1).
```

Finally `a^(-1)=x_12(1)`, since these roots are
involutions. Therefore

```text
R_sum=x_12(1)^3=x_12(1).                              (PI12)
```

This is a nonidentity element of the marked root group
`B`, so its normalized trace in both `W` and
`W_simple` is zero. For a unitary `T`,
`||T-I||_2^2=2-2 Re tr(T)`. Consequently

```text
||rho(R_0)-I||_2=||rho(R_sum)-I||_2=sqrt(2).           (PI13)
```

The involution-coefficient control
`[b_3,gamma(b_3)]d^(-1)` does evaluate to identity here;
the failures `(PI11)`--`(PI13)` are additional, concrete
tests that the first-relation seed does not pass.

Thus this model is useful for exact seed generation,
normalization checks, and distinguishing coefficient
constraints. It establishes no vanishing of the full
relation exhaustion and decides neither hyperlinearity
nor nonhyperlinearity of the Leavitt unit group.
