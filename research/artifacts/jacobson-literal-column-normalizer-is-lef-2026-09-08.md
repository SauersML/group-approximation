# The actual Jacobson column normalizer is LEF

2026-09-08. Let

```text
J=F_2<S,T | TS=1>,          Q=1-ST,
N=(J,+) directSum (J,+),

     [ 1  1 ]        [ 0  1 ]        [ Q  S ]
u  = [ 0  1 ],   w = [ 1  0 ],   h = [ T  0 ],

K_lit=<u,w,h> <= GL_2(J).
```

Then the actual semidirect product

```text
P=N semidirect K_lit                                  (1)
```

is LEF, and therefore MF. This statement concerns the literal actor
group, with all of its relations, rather than its abstract
`GL_2(F_2)*C_2` cover.

The proof uses even cyclic coordinate spaces. One end reproduces
the literal actor representation, and the other reproduces its
inverse transpose. This makes every fixed actor identity eventually
exact. Finite natural-module column evaluations then provide the
additive part of (1) and its covariance.

The group `P` is finitely generated. Its finite residual and its
finite-dimensional unitary residual are both exactly
`((JQJ) directSum (JQJ)) semidirect GL_fin(F_2^(Z))`,
with the finitary group in its actual actor embedding. This residual
is locally finite and perfect. In particular `P` is not residually
finite and is not finitely presented.

The group in (1) embeds as the actual whole-column subgroup of the
faithful coherent Jacobson group. Its third-coordinate Weyl element
is absent from (1). Thus this theorem does not prove that the full
Jacobson group is MF or settle its four-error matrix gap. No
infinite-group invariant-vector estimate is used.

## 1. The faithful literal actor representation

Let `V_+=directSum_(j>=0) F_2 e_j`, with the unilateral shift
action

```text
S e_j=e_(j+1),
T e_0=0,          T e_j=e_(j-1) for j>=1.
```

This represents `J` faithfully, as proved by the normal-monomial
partial-sum calculation in the
[ascending corner extension](jacobson-coherent-group-is-an-ascending-corner-extension-2026-09-08.md).
Consequently the matrix action of `K_lit` on `V_+^2` is
faithful as well.

Relabel its basis by all integers:

```text
f_k=(e_k,0)                    for k>=0,
f_k=(0,e_(-k-1))               for k<=-1.
```

Write `v=wuw=x_21(1)`. Direct substitution gives

```text
u f_k = f_k+f_(-k-1)           for k<0,
u f_k = f_k                    for k>=0,

v f_k = f_k                    for k<0,
v f_k = f_k+f_(-k-1)           for k>=0,

w f_k=f_(-k-1),                h f_k=f_(-k).           (2)
```

In particular `a=hw` shifts `f_k` to `f_(k+1)`. All of
`u,v,w,h` are involutions, and every nonzero matrix entry in
one of their columns has an output index `j` satisfying

```text
|j|<=|k|+1.                                          (3)
```

Products of these matrices and their inverses have finite rows and
columns. The inverse-transpose operation therefore gives a second
well-defined representation on the same direct-sum space:

```text
g |-> (g^(-1))^transpose.
```

It is a homomorphism, and it sends the chosen generators by

```text
u |-> v,             w |-> w,             h |-> h.    (4)
```

Thus every literal identity in `u,w,h` remains an identity
after the substitutions (4). The substituted generators satisfy
the same support bound (3).

## 2. Exact finite actors on an even cycle

For `n>=1`, let

```text
E_n=F_2^(Z/(2n)Z)
```

with basis `bar(f)_k`. Use representatives `-n,...,n-1`
when referring to signs. Define invertible linear maps by

```text
U_n bar(f)_k=bar(f)_k+bar(f)_(-k-1)    for -n<=k<0,
U_n bar(f)_k=bar(f)_k                  for 0<=k<n,

W_n bar(f)_k=bar(f)_(-k-1),
H_n bar(f)_k=bar(f)_(-k).                             (5)
```

All subscripts on the right are read modulo `2n`.

The reflection `k|->-k-1` has no fixed point on this even
cycle. Its `n` pairs have one negative and one nonnegative
representative. On each pair, `U_n,W_n` are the natural
two-dimensional matrices `u,w` of `GL_2(F_2)`. Hence the
entire constant `GL_2(F_2)` table is exact, in particular

```text
U_n^2=W_n^2=(U_n W_n)^3=I.
```

Also `H_n^2=I`. Thus (5) defines a homomorphism from the
abstract free product `GL_2(F_2)*C_2` to `GL(E_n)`.
At a fixed `n` it is not asserted to factor through `K_lit`.
The necessary statement about its relations is proved next.

## 3. The two coordinate charts handle every fixed actor word

Use the following two local identifications of integer-indexed
basis vectors with the cycle:

```text
o_n(f_j)=bar(f)_j,
c_n(f_j)=bar(f)_(n+j).                               (6)
```

Restrict either chart to a finite interval contained in `(-n,n)`.
It is injective there. Whenever an input and its one-step outputs
stay in that interval, (2) and (5) give

```text
U_n o_n=o_n u,        W_n o_n=o_n w,        H_n o_n=o_n h,
U_n c_n=c_n v,        W_n c_n=c_n w,        H_n c_n=c_n h. (7)
```

For the second line, a local coordinate `j>=0` near the center
`n` has negative global representative `-n+j`. Hence the
finite shear acts on these inputs, and sends the added coordinate
to `-j-1` in that chart. For local `j<0` it fixes the
input. This is exactly `v`, not `u`. The two reflections
have the same formulas in both charts. This verifies the boundary
orientation in (7).

Let `R` be a word of length `L` in `u,w,h`. Since these
generators are involutions, inverse letters can use the same
alphabet. Every cycle coordinate is within cyclic distance at most
`n/2` of one of the centers `0,n`. Choose the corresponding
chart (6). By (3), every branch of every intermediate vector
obtained while applying `R` remains at local distance at most

```text
n/2+L
```

from that center. If `n>2L+2`, this is less than `n-1`,
so all the required one-step identities (7) apply without reaching
a chart endpoint.

Consequently, on each basis vector, the finite word evaluation is
exactly either its literal word evaluation or its inverse-transpose
word evaluation inside the chosen chart. If `R=1` in `K_lit`,
both evaluations are identity by (4). We have proved

```text
R=1 in K_lit  ==>  R(U_n,W_n,H_n)=I
                  for every n>2 length(R)+2.          (8)
```

This controls every basis vector, including those at the other
boundary. It is stronger than agreement on a growing interior
subspace.

Conversely, if `R!=1` in `K_lit`, faithfulness supplies
some `f_j` that it moves. The branching support of its literal
evaluation lies within `|k|<=|j|+L`. For all sufficiently
large `n`, the origin chart is injective on that support and
the first line of (7) applies throughout. Thus

```text
R!=1 in K_lit  ==>  R(U_n,W_n,H_n)!=I
                   for all sufficiently large n.     (9)
```

Equations (8)--(9) do not require a presentation or a separate
verification of the kernel of the abstract actor map.

For clarity, they already prove that `K_lit` is LEF. Given
a finite set of actor elements, choose a representative word for
each. Different representative choices agree for all sufficiently
large `n` by (8). For every product that stays in the test set,
the corresponding representative-word identity is eventually exact.
Distinct elements are eventually separated by (9). Since there are
only finitely many such checks, a single sufficiently large `n`
gives the required injective partial multiplication map into the
finite group `GL(E_n)`.

## 4. Finite columns supply the entire additive group and covariance

For `j>=0`, define the physical-column evaluation

```text
ev_j:N -> V_+^2,
ev_j(a,b)=(a e_j,b e_j).                              (10)
```

It is additive, and matrix multiplication gives the exact literal
equivariance

```text
ev_j(g c)=g ev_j(c)           for g in K_lit, c in N.  (11)
```

Let `P_n:V_+^2->E_n` send `f_k` to `bar(f)_k` for
`-n<=k<n`, and to zero for other indices. For `n>=4` put

```text
m_n=floor(n/4),
B_n=E_n^(directSum m_n),
q_n(c)=(P_n ev_j(c))_(0<=j<m_n).                     (12)
```

This is a genuine additive homomorphism on all of `N` at each
stage. Actors act diagonally on the `m_n` copies of `E_n`.

Every fixed coefficient pair `c=(a,b)` admits a constant `C`
such that

```text
support(ev_j(c)) subset {f_k: |k|<=j+C}
                         for every j>=0.             (13)
```

Indeed each normal monomial `S^p T^q` either kills `e_j`
or sends it to `e_(j-q+p)`, and each coefficient is a finite
linear combination of such monomials. The labeling of the second
ray adds only one to the absolute-index bound.

Fix also an actor `g` and a representative word of length `L`.
For `0<=j<m_n`, all intermediate supports when it acts on
`ev_j(c)` lie within

```text
|k|<=m_n-1+C+L.
```

For all sufficiently large `n` this is less than `n-1`.
Thus these evaluations all stay in the origin chart, uniformly over
the selected columns. Applying (7) and (11) proves exact eventual
covariance:

```text
g(U_n,W_n,H_n) q_n(c)=q_n(g c)
                  for every sufficiently large n.   (14)
```

No uniformity over all coefficients at a fixed stage is asserted.
Only the finite coefficient and actor tests at issue are used.

The additive maps also separate every nonzero element eventually.
If `c!=0`, faithfulness of the unilateral ring representation
gives some column `j` with `ev_j(c)!=0`. Eventually this
column is among those in (12), and its finite support is preserved
by `P_n`, so `q_n(c)!=0`.

For the particular mark `c_Q=(Q,0)`, the zeroth column is
`f_0`. Therefore

```text
q_n(c_Q)!=0                    for every n>=4.        (15)
```

As a permutation of the finite additive set `B_n`, translation
by any nonzero `q_n(c)` is a fixed-point-free involution. Its
complex permutation unitary has norm distance exactly `2` from
identity.

## 5. An injective finite model on every finite test set of P

The semidirect-product law is

```text
(c,g)(d,k)=(c+g d,g k).
```

Fix a finite test set in `P`. For every actor coordinate in it,
choose one word in `u,w,h`, choosing the empty word for identity
if it occurs. Evaluate that word at (5), and denote its value
by `g_n`. Define on the test set

```text
f_n(c,g)=(q_n(c),g_n)
       in B_n semidirect GL(E_n),                   (16)
```

where `GL(E_n)` acts diagonally on `B_n`.

For sufficiently large `n`, every tested actor product is exact
by (8). Additivity of `q_n` and the finitely many covariance
identities (14) then show that (16) preserves every product whose
three elements lie in the test set.

It is injective there for sufficiently large `n` as well.
Different actor coordinates are distinguished by (9). With equal
actor coordinates, different translations are distinguished by the
eventual separation following (14). Taking the maximum of these
finitely many thresholds proves that (16) is an injective partial
multiplication map into a finite group. This proves that the actual
group `P` is LEF.

The finite target in (16) acts faithfully by affine permutations
of `B_n`, since `m_n>=1`. Thus these are also concrete finite
permutation models. On a countable group, exhaustion of finite test
sets produces a faithful homomorphism into a norm matrix corona:
every nontrivial finite permutation has norm distance at least
`sqrt(3)` from identity, by one of its nontrivial cycles. The
translations retained in (15) have distance exactly `2`. Hence
`P` is MF, with its head retained.

The word-choice argument is essential: the finite matrices in (5)
need not give homomorphisms from the whole actor group at individual
stages. They give eventual exactness for every fixed relation, which
is precisely what the finite-test argument consumes.

## 6. Finite generation and the exact finite-dimensional residual

Let `M` be the `F_2`-span of the `K_lit`-orbit of
`(1,0)` inside `N`. It is invariant under the constant
shears and the coordinate swap. Adding a vector to its image
under a shear, then swapping coordinates as needed, extracts each
of `(a,0),(0,a),(b,0),(0,b)` from any `(a,b) in M`.
The identities

```text
h(0,a)=(S a,0),          h(a,0)=(Q a,T a)
```

show that the extracted coefficients are closed under left
multiplication by `S` and `T`. They contain `1` and are
closed under addition, so they contain all of `J`. Therefore
`M=N`. The three actors `u,w,h` and the single translation
`(1,0)` generate `P`.

We next identify the full finitary actor subgroup. In the integer
coordinates (2), write `E_(p,q)` for the matrix unit sending
`f_q` to `f_p`, and put

```text
r=[u,a u a^(-1)],       a=hw,
r_j=a^j r a^(-j).
```

The shear `u` has sources `k<=-1` and targets `-k-1`.
Its shift by `a` has sources `k<=0` and targets `1-k`.
Their two square-zero parts multiply to zero in one order, and
in the other order only the path `-1 -> 0 -> 1` survives.
Therefore

```text
r=I+E_(1,-1),          r_j=I+E_(j+1,j-1).            (17)
```

Conjugating these roots by `w` supplies their reverse directions.
Iterated third-index commutators supply every elementary root
between two coordinates of the same parity. These also supply
every finite permutation within each parity class, since a
coordinate swap is the product of three elementary roots.

There are roots in both directions between the parity classes:

```text
[u,r_2]=I+E_(3,-2),
w [u,r_2] w=I+E_(-4,1).                              (18)
```

For the first identity, the only nonzero mixed product is the
path `-2 -> 1 -> 3`; the other order is zero. Independent
finite permutations within the two parity classes transport these
two roots to every ordered pair of opposite parity. Thus

```text
L=GL_fin(F_2^(Z)) <= K_lit.                          (19)
```

Here `GL_fin` consists of all invertible matrices equal to
identity outside a finite coordinate set. Row reduction over
`F_2` proves that the roots just obtained generate it.

Put `I=JQJ`. The faithful shift calculation identifies its
matrix units `S^i Q T^j` with all finite matrices on the
unilateral ray and gives

```text
J/I ~= R=F_2[z,z^(-1)].                              (20)
```

Consequently `M_2(I)` is exactly the space of finitary
endomorphisms of `V_+^2`, equivalently of the integer-coordinate
space. The kernel of the entrywise symbol homomorphism
`K_lit->GL_2(R)` is therefore exactly `L`, by (19).
In particular `L` is normal in the actor group. No claim that
the symbol image is all of `GL_2(R)` is needed.

Inside `P`, the column commutators satisfy

```text
[L,N]=I directSum I.                                (21)
```

Indeed an element of `L` differs from identity by a matrix in
`M_2(I)`, so its displacement of any column lies in the direct
sum of two copies of `I`.
Conversely, for `b in I`, the actor `x_12(b)` belongs to
`L`, and its commutator with the translation `(0,1)` is
the translation `(b,0)`. The other elementary position gives
`(0,b)`.

The group `L` is infinite and simple. An elementary proof is
included in the
[finitary-kernel calculation](jacobson-recursive-head-dies-in-amenable-targets-2026-09-08.md):
if a nontrivial normal subgroup contains `g`, choose a vector
`v` with `gv!=v` and a fresh coordinate functional `epsilon_j`
outside the supports involved. Then

```text
[g,I+v epsilon_j]=I+(gv+v)epsilon_j
```

is a nontrivial transvection in that normal subgroup. Finite
changes of basis and coordinate permutations give all elementary
transvections, which generate `L`.

Every homomorphism `L->U(d)` is trivial. Otherwise simplicity
would make it injective. But `L` contains an elementary abelian
subgroup `(C_2)^(d+1)`, whereas commuting involutions in `U(d)`
are simultaneously diagonalizable and have at most `2^d`
distinct values. This excludes injectivity. Thus every exact
finite-dimensional unitary representation of `P` kills `L`
and, by (21), also kills `I directSum I`.

Conversely, the entrywise symbol map sends `P` into the affine
linear group

```text
R^2 semidirect GL_2(R) <= GL_3(R)
```

with kernel precisely

```text
R_0=(I directSum I) semidirect L.                    (22)
```

Every subgroup of `GL_3(R)` is residually finite here. Given
a nonidentity Laurent matrix, choose a nonzero entry of its
difference from identity. After clearing negative powers this is
a nonzero polynomial. A sufficiently large finite extension of
`F_2` contains a nonzero evaluation point where it does not
vanish. Evaluation preserves invertibility, because the inverse
matrix also has entries in `R`, and detects the chosen element
in a finite general linear group.

Thus every element outside (22) survives in a finite quotient.
Since every finite group has a faithful finite-dimensional unitary
representation, both residuals are exactly

```text
Res_fin(P)=Res_fd(P)=R_0.                            (23)
```

This kernel is locally finite. A finite set of its actor parts
generates a finite subgroup of `L`; the span of the orbits of
its finitely many translation parts under that finite group is
a finite-dimensional vector space over `F_2`.
It is also perfect. The simple nonabelian group `L` is perfect,
and `[L,I directSum I]=I directSum I`: for `b in I`,
choose a finite diagonal projection `e in I` with `be=b`.
The commutator of `x_12(b)` with `(0,e)` is `(b,0)`,
and the other position gives `(0,b)`.

In particular the nonzero mark `(Q,0)` dies in every exact
finite-dimensional unitary representation and every finite quotient,
so `P` is not residually finite.

A finitely presented LEF group is residually finite: include the
identity, generators, inverse letters, and prefixes of all defining
relators and of a chosen nonidentity word in one finite test set.
A suitable LEF map then defines a genuine finite quotient on the
generators, satisfying the relators and retaining that word.
Therefore the finitely generated LEF group `P` is not finitely
presented.

## 7. The actual embedding and the boundary of this result

Embed `K_lit` into `GL_3(J)` as the upper-left two-by-two
block, with last diagonal entry `1`, and embed `N` by

```text
Z(a,b)=x_13(a)x_23(b).
```

These column roots commute, their parameterization is injective,
and their subgroup has trivial intersection with the actor block.
Conjugation is exactly the left action on the column `(a,b)`.
Thus this is a faithful embedding of the actual semidirect product
(1), not just a map from the free-product cover.

All these elements lie in `EL_3(J)`: the constant actors are
elementary, all the column roots are elementary, and

```text
h=x_12(S)x_21(T)x_12(S).
```

The
[ascending corner extension](jacobson-coherent-group-is-an-ascending-corner-extension-2026-09-08.md)
identifies `EL_3(J)` with the base subgroup of the faithful
coherent Jacobson group `Gamma_triangle` (the rank-three candidate).
This places the LEF subgroup proved here inside that actual group.

The third-coordinate Weyl element `w_23` is not in this subgroup.
It does not preserve the column-normalizer form: it conjugates
`x_23(a)` to `x_32(a)` and `x_13(a)` to `x_12(a)`.
The complete finite `GL_3` packet and its opposite-column
relations therefore lie beyond the construction above.

The actual column normalizer, including every actor relation and
every fixed column covariance identity, consequently cannot supply
marked norm-corona collapse: its mark survives the finite models
constructed here. No conclusion about MF or non-MF of the full
coherent group follows.
