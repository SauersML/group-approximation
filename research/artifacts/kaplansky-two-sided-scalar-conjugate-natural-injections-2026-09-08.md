# Two simultaneous chart choices have injective auxiliary natural maps

Date: 2026-09-08. Exact support proof, without computation.
The conclusion is natural-module injectivity only. No full
exterior injection, Leavitt inverse, group-ring split, or
Kaplansky counterexample is constructed.

Subsequent status: the [period-four exterior kernel](kaplansky-two-sided-omega-square-period-four-kernel-2026-09-08.md)
excludes the actual z=omega^2 candidate, despite its natural
injectivity proved here. The z=omega candidate remains unresolved.

Use the literal deletion blocks

```
a=[[1,s_0],[t_0,0]],       b=[[1,s_1],[t_1,0]].
```

For a nonzero field element `z`, let `m_z` be multiplication
by `z` on a binary field-coordinate pair. Define the auxiliary
linear map

```
H_z=a+m_z^-1 b m_z.
```

The natural-kernel transfer in
[the right-coefficient artifact](kaplansky-right-chart-coefficient-natural-kernel-transfer-2026-09-08.md)
cannot exclude a normalized exterior map through `H_z` if
`H_z` is injective. This artifact proves that injectivity for
`z=omega,omega^2` on the actual free binary boundary module.

## Explicit matrices

In the binary basis `1,omega`,

```
m_omega=[[0,1],[1,1]],
m_(omega^2)=[[1,1],[1,0]].
```

Direct multiplication gives

```
H_omega=
  [[1+s_1,1+s_0+s_1+t_1],
   [t_0+s_1,1+s_1]],

H_(omega^2)=
  [[1+t_1,s_0+t_1],
   [1+t_0+s_1+t_1,1+t_1]].                         (1)
```

Let `Omega={0,1}^N` be the set of actual infinite binary
sequences, and let `B=k^(Omega)` be the free vector space,
where `k=F_2` or `F_4`. Each vector has finite support. The
operator `s_i` prepends `i`; `t_i` deletes that digit if it
matches and is zero otherwise.

**Theorem.** Both matrices in (1) are injective on `B^2`.

## Tail classes and a height on aperiodic classes

Let `S` delete the first digit of a sequence. Two tails are
equivalent if

```
S^m xi=S^n eta       for some m,n>=0.
```

All prefix and deletion operators preserve each equivalence
class. A finite kernel vector can therefore be considered
one class at a time.

First consider a class with no eventually periodic sequence.
Fix a base tail `xi_0`. For a tail `eta` in its class, choose
`m,n` with `S^m eta=S^n xi_0` and define

```
h(eta)=m-n.
```

This is well-defined. If another pair `m',n'` gave a different
difference, applying further shifts would give equality of
two distinct shifts of `xi_0`; that would make `xi_0`
eventually periodic. By construction,

```
h(i eta)=h(eta)+1,       h(S eta)=h(eta)-1.
```

The creator parts of the two matrices are

```
C_omega(U,V)
  =(s_1(U+V)+s_0V, s_1(U+V)),

C_(omega^2)(U,V)
  =(s_0V,s_1U).                                    (2)
```

Each map in (2) is injective. For the first, its second
coordinate forces `U=V`, and its first then forces `V=0`.
For the second, the two injective prefix maps force both
coordinates to vanish.

Suppose a nonzero finite vector were killed by either matrix.
Take the largest height in the support of its two coordinates,
and restrict to the vector at that height. In the image at
height one larger, only its creator part contributes: constants
preserve height and deletions lower it. Equation (2) forces
the entire highest-height vector to vanish, a contradiction.
Thus there is no kernel in an aperiodic class.

## Removing nonperiodic tails in an eventually periodic class

An eventually periodic class has a finite periodic core `P`:
the distinct cyclic shifts of one primitive periodic word.
The shift `S` is a cyclic permutation of `P`. Define

```
d(eta)=min{n>=0 : S^n eta is in P}.
```

Depth zero means that the tail itself is purely periodic.
If `d(eta)>0`, then prepending either digit increases depth
by one, while deleting the first digit decreases depth by
one. A prefix of a depth-zero tail has depth zero or one.

If a finite kernel vector had a positive largest depth `D`,
its image at depth `D+1` would again be exactly the creator
map (2) applied to its depth-`D` part. Lower depths, constants,
and deletions cannot reach that level. Injectivity of (2)
rules this out. Hence every remaining kernel vector must be
supported entirely on the periodic core.

## The periodic equations for H_omega

Enumerate the distinct tails of the core as

```
xi_i=S^i xi_0,       i modulo n,
```

where `n` is the primitive period, and let `b_i` be the first
bit of `xi_i`. The unique prefix of `xi_i` that stays in the
core is `b_(i-1) xi_i=xi_(i-1)`; the other prefix has depth
one. These statements concern actual sequences, with no
identification of the constant zero and constant one tails.

Write the input coefficients at `xi_i` as `(U_i,V_i)`.
For `H_omega`, wrong-prefix outputs from (2) force

```
V_i=(1+b_(i-1))U_i.
```

Indeed a wrong `s_1` output forces `U_i+V_i=0` when the
preceding bit is zero; a wrong `s_0` output forces `V_i=0`
when the preceding bit is one. Put `c_i=U_i`.

The two coefficients in the image at `xi_i` are

```
b_(i-1)c_i+c_(i+1)
  +b_(i-1)(1+b_(i-2))c_(i-1)=0,

(1+b_(i-1))(c_i+c_(i-1))+b_i c_(i+1)=0.             (3)
```

For example, the two creator terms in the first row together
contribute `c_(i+1)`, regardless of the current bit. The
deletion `t_1V` contributes the last term of the first row.

If `b_(i-1)=0`, equations (3) force

```
c_(i+1)=0,       c_i=c_(i-1).
```

If `b_(i-1)=1`, the second equation forces
`b_i c_(i+1)=0`. Consequently, any nonzero `c_j` would require
its preceding two bits to be

```
b_(j-2)=1,       b_(j-1)=0.
```

But the zero preceding bit also forces `c_j=c_(j-1)`.
Nonzeroness of `c_(j-1)` would require `b_(j-2)=0`, a
contradiction. Thus all coefficients vanish.

## The periodic equations for H_(omega^2)

For the second matrix, wrong-prefix outputs force `U_i=0`
when the preceding bit is zero and `V_i=0` when it is one.
Write

```
U_i=b_(i-1)c_i,
V_i=(1+b_(i-1))c_i.
```

The two core equations are

```
b_(i-1)(c_i+c_(i-1))+(1+b_i)c_(i+1)=0,

c_i+[b_(i-1)+(1+b_(i-1))b_(i-2)]c_(i-1)
  +b_i c_(i+1)=0.                                  (4)
```

If `b_(i-1)=1`, adding the two equations gives
`c_(i+1)=0`, and then `c_i=c_(i-1)`. If `b_(i-1)=0`, the
first equation gives `(1+b_i)c_(i+1)=0`. Therefore a nonzero
`c_j` would require

```
b_(j-2)=0,       b_(j-1)=1.
```

The preceding one bit forces `c_j=c_(j-1)`. Nonzeroness of
`c_(j-1)` would require `b_(j-2)=1`, a contradiction.
This proves that all coefficients vanish in this case too.

The equations hold also for primitive periods one and two,
with indices read cyclically. An artificially longer period
for the same sequence introduces no extra basis elements.
Together with the preceding reductions, this proves the
theorem on every tail class, and hence on the full free module.

## The exact simultaneous chart choices

Let `Phi_g`, `Psi_b`, and the input scaling `D_z` be as in
the right-coefficient artifact. Write `E_z` for scaling the
two target sectors by `(z,z^sigma)`. The exterior source map
of the auxiliary linear pair `diag(H_z,b)` is

```
Phi_g+E_(z^-1) Psi_b D_z.                           (5)
```

These maps arise from genuine simultaneous chart choices.
For `z=omega,omega^2`, take

```
ell_z=[[1,0],[0,z^-1]],
n_z=[[0,z^-1],[1,0]],
T_z=P_0[ell_z][g][n_z]f_0.
```

Both constant matrices belong to `K`. The complete map of
`T_z`, precomposed by the invertible source map `tau D_z`
and postcomposed by `E_z`, is exactly (5). Indeed the right
matrix has `(alpha,beta,gamma)=(0,z^-1,1)`, while the left
target coefficients are `(0,z^-1,z^-2)`.

Thus these are concrete simultaneous choices for which the
auxiliary first natural block is injective. The natural-kernel
transfer theorem cannot exclude them by producing a kernel
of that block. This is a proved limitation of that mechanism,
not a claim that their full exterior maps are injective.

The next unresolved test is the complete exterior source map
in (5), including both central sectors and arbitrary finite
tensors. No conclusion about a literal group-ring split follows
from the natural injectivity proved here.

## Bounded exterior probe, separate from the proof

A single-core MSI probe on acn112 tested (5) for both z values
and completed in 1.169 seconds. Closing the seed (01)^infinity
under at most three prefix prepends gives 12 source tails;
the full two-sector source restriction had rank 288 on its
288 columns. Using both constant zero and constant one tails
with the same prefix depth gives 16 source tails and rank 512
on 512 columns. The target included every image tail, rather
than truncating outputs to the source set. Conjugation weights
were applied separately to input and target sectors as in (5).

These four finite restrictions had no kernel. This observation
does not prove injectivity on larger supports or on the full
exterior module. No further compute was left running.

## The literal actor and chart do not generate a virtually free group

Let H=<K,g> for the literal actor used above. This group contains
an explicit copy of Z^2. The proof uses actual unit identities
and the boundary action, with no assumed presentation for H.

Write p=s_0, r=t_0, q=s_1, and s=t_1, so rp=sq=1, and set

```
a=[[1,p],[r,0]],       b=[[1,q],[s,0]],
g=diag(a,b).
```

Direct multiplication in characteristic two gives

```
a^2=[[1+pr,p],[r,1]],       a^3=I,
b^3=I.
```

Let Omega=[[0,1],[1,1]] be multiplication by omega on a binary
field-coordinate pair. Both

```
k=diag(Omega,I_2)
```

and the matrix S exchanging the two field-coordinate pairs
belong to K=GL_2(F_4). Now

```
a Omega=[[p,1+p],[0,r]],
h=(gk)^3=diag(u,I_2),       u=(a Omega)^3.
```

The unit u has infinite order. On a vector (v,0) in its binary
pair, u^n acts as (p^(3n)v,0) for every positive integer n.
In the free boundary module, choose v to be the basis ray
111.... Prefix addition p^(3n) sends it to 0^(3n)111..., a
different ray. Thus no positive power of u is identity.

Conjugating by the constant swap gives

```
h'=ShS^-1=diag(I_2,u).
```

The elements h and h' commute, and
h^m(h')^n=I implies u^m=u^n=I. Infinite order forces m=n=0,
so <h,h'> is isomorphic to Z^2.

If H had a free subgroup of finite index, its intersection with
this Z^2 would still have finite index in Z^2. That intersection
is an abelian group of rank two, whereas every abelian subgroup
of a free group is cyclic. This contradiction proves H is not
virtually free.

This excludes a virtually-free classification as a blanket
reason to reject all chart-coefficient attempts. It does not
exclude amenability or membership in another class with directly
finite group algebras, and it does not establish generation of
the full Leavitt unit group. The projective comparison remains
unresolved.

## A leading exterior cancellation prevents a direct height argument

The natural height proof does not immediately extend to the
complete exterior map. There is an exact nonzero kernel in
its contribution with a creator in each tensor factor.

Use the two-sector source `(X,Y)` from the right-coefficient
artifact. The character blocks of `H_z` are

```
A_z=A+C,
B_z=B+z^2 D,
```

where `A,B` are the blocks of `a` and `C,D` those of `b`.
Their creator parts, and those of the second block, are

```
A_z,cre=s_0+s_1,
B_z,cre=omega^2 s_0+omega^2 z^2 s_1,
C_cre=s_1,
D_cre=omega^2 s_1.
```

Set

```
M=alt(s_1 tensor s_0),
Q=alt(s_1 tensor s_1),
Z=X+omega^2 Y.
```

Retaining exactly the terms with a prefix creator in both
tensor factors gives

```
L_z,+(X,Y)=MZ+Q(X+omega^2 zY),
L_z,-(X,Y)=omega MZ+Q(omega z^2 X+Y).               (6)
```

These identities hold on the full finite tensor source. In
a filtration by aperiodic prefix heights, they are the terms
of largest creator degree.

The ranges of `M` and `Q` lie in disjoint components of the
target exterior square:

```
im M=(s_1 B_4) wedge (s_0 B_4),
im Q=Lambda^2(s_1 B_4).
```

The map `M` is injective, since the two prefix ranges are
disjoint and each prefix map is injective. Also
`Q=(Lambda^2 s_1) alt`, so

```
ker Q={Y : tau Y=Y}.
```

The last equality includes diagonal tensors in characteristic
two, as well as off-diagonal symmetric tensors.

If the plus coordinate of (6) vanishes, the disjoint target
components force `Z=0` and `Q(X+omega^2 zY)=0`. Substituting
`X=omega^2Y`, and using `z!=1`, gives `QY=0`. Conversely,
these conditions also kill the minus coordinate. Therefore
for both `z=omega,omega^2` the joint kernel is exactly

```
ker(L_z,+,L_z,-)
  ={(X,Y) : X=omega^2Y and tau Y=Y}.                (7)
```

For example `(X,Y)=(omega^2 xi tensor xi,xi tensor xi)`
is a nonzero kernel of this creator contribution for any
nonzero tail vector `xi`. For a binary basis tail, multiplying
this source by `omega^2` gives a Frobenius-fixed source as well.

Equation (7) is a cancellation in the leading contribution,
not a kernel of the complete exterior map. Lower creator,
constant, and deletion terms can act nontrivially on it. Thus
the injective-creator argument used for the natural module
cannot simply remove the highest exterior source layer; those
remaining terms require a separate argument.
