# Complete exterior formulas for lower changes and constant left charts

Date: 2026-09-08. Exact source formulas and kernel obstructions,
including every left chart coefficient for the literal deletion
pair. All proofs below are algebraic identities. A bounded MSI
probe suggested several of the short witnesses; an independent
analytic factorization also gives the `v=omega^2` case. These
statements concern the natural boundary exterior representation
and do not
construct a group-ring split or resolve Kaplansky's conjecture.

Use the binary encoding of `K=GL_2(F_4)` and reduced projectors
`f_0,P_0` from
[the first-field-coordinate artifact](kaplansky-first-field-coordinate-transporter-kernel-2026-09-08.md),
and the complete source identification from
[the two-sector artifact](kaplansky-full-two-sector-relative-transporter-obstruction-2026-09-08.md).
Let `B_4` be the scalar extension of the free binary boundary
module, and let `sigma` conjugate `F_4` coefficients while fixing
the binary boundary basis.

## Notation and the complete source

Write `g=diag(a,b)`, where `a,b` are invertible binary-linear
operators on the two binary roots of each field coordinate.
Their character blocks are

```
a u_+(eta)=u_+(A eta)+u_-(B eta),
b v_+(xi) =v_+(C xi) +v_-(D xi).
```

The conjugate source sectors have blocks `B^sigma,A^sigma` and
`D^sigma,C^sigma`, respectively. Superscript `sigma` means
coefficient conjugation, not transpose or inverse.

The entire source `im(f_0)` in the exterior square is parametrized
by pairs

```
(X,Y) in (B_4 tensor B_4) direct_sum (B_4 tensor B_4)
```

through the forms
`k_+(xi,eta)=(u_+(xi)+v_+(xi)) wedge u_+(eta)` and their
conjugates. Each target sector is identified with `Lambda^2 B_4`
through `J_+,J_-`. In these identifications the original complete
map is

```
Phi_g,+(X,Y)=alt((C tensor A)X+(D^sigma tensor B^sigma)Y),
Phi_g,-(X,Y)=alt((D tensor B)X+(C^sigma tensor A^sigma)Y).
```

We also use the complete map

```
Psi_a,+(X,Y)=alt((A tensor A)X+(B^sigma tensor B^sigma)Y),
Psi_a,-(X,Y)=alt((B tensor B)X+(A^sigma tensor A^sigma)Y).
```

All formulas below act on the entire source, including diagonal
tensors and both central sectors.

## An arbitrary lower binary block

Let `k` be any binary-linear operator on a field-coordinate
pair, with character blocks `E,F`:

```
k u_+=u_+ E+u_- F,
k u_-=u_+ F^sigma+u_- E^sigma.
```

Set

```
M_k=[[I,0],[k,I]],
Q=EA+F^sigma B,       R=FA+E^sigma B.
```

Products denote composition in the displayed order. For three
tail operators define a map on tensors by

```
T(a,c,q)=alt((q+c) tensor a+(a+q+c) tensor q).
```

Then the complete exterior source map for `M_k g` is

```
Phi_Mkg,+(X,Y)
  =T(A,C,Q)X+T(B^sigma,D^sigma,R^sigma)Y,

Phi_Mkg,-(X,Y)
  =T(B,D,R)X+T(A^sigma,C^sigma,Q^sigma)Y.             (1)
```

For verification in the plus-to-plus block, the actor sends
the two factors of `k_+(xi,eta)` to

```
u_+(A xi)+v_+((Q+C)xi),
u_+(A eta)+v_+(Q eta),
```

with other characters treated separately. The established
projector identities are

```
P_0(u_+(xi) wedge u_+(eta))=0,
P_0(v_+(xi) wedge u_+(eta))=J_+(xi,eta),
P_0(v_+(xi) wedge v_+(eta))=J_+(xi,eta).
```

Together with symmetry of `J_+`, they give
`J_+((Q+C)xi,A eta)+J_+((A+Q+C)xi,Q eta)`, which is the first
term of (1). The other three blocks follow identically or by
conjugation. Mixed-character wedges are killed by `P_0`.

## The constant lower transvection always has a kernel

Take

```
U=[[I,0],[I,I]] in K.
```

Then `E=I,F=0`, so `Q=A,R=B`. Formula (1) simplifies to

```
Phi_Ug=Psi_a.                                       (2)
```

Indeed `T(A,C,A)=alt(A tensor A)`; all terms involving `C`
cancel, and the other three blocks behave the same way.
Consequently every diagonal source `k_+(eta,eta)` is killed:
its target coordinates are
`A eta wedge A eta=0` and `B eta wedge B eta=0`.
For every nonzero `eta`, this source is nonzero and fixed by
`f_0`.

There is also an explicit binary certificate. For any actual
boundary tail `eta`, put `a_i=e_i eta` and

```
w_eta=a_1 wedge a_3+a_2 wedge a_4
     =omega^2 k_+(eta,eta)+omega k_-(eta,eta).
```

Its two displayed binary wedge terms are independent, and hence

```
f_0 w_eta=w_eta!=0,
P_0[U diag(a,b)]f_0 w_eta=0.                         (3)
```

This holds for every invertible binary-linear `a,b`, without
any restriction on character mixing or creation/deletion
coefficients. It is a complete-source obstruction, not an
inference from testing the earlier two-tail source vector.

## Constant left K changes reduce to five parameters

Let

```
m=[[p,q],[r,s]] in GL_2(F_4),
alpha=r^2,       beta=ps+rq+rs.
```

For any block-diagonal actor `g`, its complete source map after
this constant left multiplication is

```
Phi_mg,+=beta Phi_g,+ +alpha Psi_a,+,
Phi_mg,-=beta^sigma Phi_g,- +alpha^sigma Psi_a,-.     (4)
```

One direct derivation uses the target bilinear coefficient
matrix

```
R_0=[[0,1],[1,1]],
m^transpose R_0 m=[[r^2,ps+rq+rs],[ps+rq+rs,s^2]].
```

In a plus source tensor after `g`, the two field-coordinate
vectors are `(A xi,C xi)` and `(A eta,0)`. Thus only the first
column of this matrix contributes: it gives
`alpha A tensor A+beta C tensor A`. The other source and target
sectors give the remaining terms of (4).

The pair `(alpha,beta)` cannot be zero. If `r=0`, invertibility
gives `beta=ps!=0`; if `beta=0`, then `r!=0`. Rescaling the two
target sectors by conjugate nonzero scalars does not change
the kernel. Hence the whole constant left `K` family reduces
to at most five source tests, parametrized by

```
v=alpha/beta in P^1(F_4):

v finite: (Phi_g,+ +v Psi_a,+,
           Phi_g,- +v^sigma Psi_a,-),

v=infinity: Psi_a.
```

All five parameter values occur: `m=I` realizes zero, `m=U`
realizes infinity, and for nonzero finite `v` the matrix
`[[0,v^-1],[1,0]]` realizes `v`. For a particular actor some
of these tests may have coincident kernels.

In particular, a source is killed by **every** left `K` change
if and only if

```
Phi_g(X,Y)=0       and       Psi_a(X,Y)=0.            (5)
```

Necessity follows already from `m=I,U`; sufficiency follows
from (4). The same criterion describes the common kernel for
all left coefficients in `F_2[K]`, because these coefficients
are linear combinations of group elements. The statement
holds over the binary module as well as after scalar extension.

## All five pencils have kernels for the literal deletion pair

Specialize to

```
a=[[1,s_0],[t_0,0]],       b=[[1,s_1],[t_1,0]],
g=diag(a,b).
```

The character blocks are

```
A=omega^2+s_0+t_0,       B=omega+omega^2 s_0+t_0,
C=omega^2+s_1+t_1,       D=omega+omega^2 s_1+t_1.
```

Denote the finite-parameter test by

```
P_v=(Phi_g,+ +v Psi_a,+,
     Phi_g,- +v^sigma Psi_a,-).
```

The conjugate parameter in the second coordinate is essential.
The following are exact nonzero source kernels in the actual
binary boundary module after scalar extension.

For `v=0`, put `zeta=(01)^infinity`, `eta=(10)^infinity`.
The earlier
[four-term certificate](kaplansky-deletion-shear-period-two-exterior-kernel-2026-09-08.md)
gives

```
X=omega^2 zeta tensor eta,
Y=omega zeta tensor eta.
```

For `v=infinity`, any `X=eta tensor eta`, `Y=0`, with nonzero
`eta`, is a kernel by (2).

### The parameter one

Let `p=(01)^infinity`, `q=(10)^infinity`, `r=0p`, and take

```
X=p tensor (p+omega^2 q),
Y=p tensor (omega^2 p+q).
```

The literal prefix/deletion identities give

```
(C+A)p=r,
(D^sigma+B^sigma)p=omega r+omega^2 q,
A(p+omega^2 q)=r+omega^2 q,
B^sigma(omega^2 p+q)=r.
```

Thus the plus output is

```
r wedge (r+omega^2 q)+(omega r+omega^2 q) wedge r=0.
```

On the minus side, the corresponding four identities give

```
(omega^2 r+omega q) wedge (omega^2 r)
  +r wedge (omega^2 r+q)=0.
```

Explicitly, the left factors are `(D+B)p=omega^2 r+omega q`
and `(C^sigma+A^sigma)p=r`, and the right factors are
`B(p+omega^2 q)=omega^2 r` and
`A^sigma(omega^2 p+q)=omega^2 r+q`.
The source is nonzero. Multiplying this pair by `omega^2`
makes its source vector fixed by binary Frobenius conjugation.

### The parameter omega

Set

```
u=0^infinity,       v=010^infinity,       w=10^infinity,
z=0v,
x=omega u+omega^2 v+omega^2 w,
X=u tensor x,       Y=u tensor v.
```

Here `010^infinity` means the prefix `01` followed by the
constant zero tail; thus `v=0w`. Define

```
f=omega u+w,       h=omega^2 u+w.
```

The two plus left factors are

```
(C+omega A)u=f,
(D^sigma+omega B^sigma)u=omega f,
```

and the two minus left factors are

```
(D+omega^2 B)u=omega^2 h,
(C^sigma+omega^2 A^sigma)u=h.
```

The right combinations satisfy

```
Ax+omega B^sigma v=u+omega^2 w,
omega^2 Bx+A^sigma v=0.
```

For a direct check, their individual values are

```
Ax=u+v+w+omega^2 z,
B^sigma v=omega^2 v+omega z+w,
Bx=omega^2 v+omega w+omega z,
A^sigma v=omega v+z+w.
```

The plus output is `f wedge (u+omega^2 w)=0`, since
`f=omega(u+omega^2 w)`, and the minus output is zero. The
source is nonzero because the three displayed tails are
distinct.

### The parameter omega squared

Set

```
h=1^infinity,       p=01^infinity,       q=001^infinity,
x=omega^2 p,       y=p,
X=h tensor x,       Y=h tensor y.
```

Equivalently `p=0h` and `q=00h`; these are distinct actual tails.
Put `f=h+omega^2 p` and `j=h+omega p`. The left factors are

```
(C+omega^2 A)h=f,
(D^sigma+omega^2 B^sigma)h=omega f,
(D+omega B)h=omega^2 j,
(C^sigma+omega A^sigma)h=j.
```

Direct expansion gives

```
A p=omega^2 p+q+h,
B^sigma p=omega^2 p+omega q+h,
B p=omega p+omega^2 q+h,
A^sigma p=omega p+q+h.
```

Consequently

```
Ax+omega B^sigma y=f,
omega^2 Bx+A^sigma y=omega^2 j.
```

The plus output is `f wedge f=0`; the minus output is
`j wedge (omega^2 j)=0`. This is an exact nonzero source kernel.

The factorization behind this construction is that the matrix
of the last two right combinations is

```
[[A,omega B^sigma],[omega^2 B,A^sigma]]
  =diag(1,omega^2) a_character diag(1,omega).
```

It is invertible. Applying its finite inverse to any pair of
scalar multiples of `(f,j)` produces a source whose two wedge
outputs vanish. The displayed short witness corresponds to
the right-hand side `(f,omega^2 j)`.
Multiplying the source by `omega^2` gives the nonzero
Frobenius-fixed pair

```
X_binary=omega h tensor p,
Y_binary=omega^2 h tensor p.
```

In binary root vectors `a_i=e_i h`, `b_i=e_i p`, this is

```
w=(a_1+a_3) wedge (b_1+b_2)+(a_2+a_4) wedge b_1.
```

It has six binary wedge terms and is nonzero, fixed by `f_0`,
and killed by the `v=omega^2` test.

## Every left chart coefficient is excluded for this actor

Let `c` be an arbitrary element of `F_2[K]`. By linearity of
(4), the complete source map of `P_0 c [g]f_0` has the form

```
(beta Phi_g,+ +alpha Psi_a,+,
 beta^sigma Phi_g,- +alpha^sigma Psi_a,-)
```

for some `alpha,beta` in `F_4`. They are the sums of the
displayed coefficients for the group elements occurring in
`c`. If both vanish, the source map is zero. Otherwise its
kernel is one of the five pencils just proved to have nonzero
kernels. Therefore

```
For every c in F_2[K],
there is no L with L P_0 c [g]f_0=f_0.               (6)
```

The nonzero scalar-extended source vectors already contradict
an identity over `F_2`: the binary group algebra acts on this
scalar-extended representation. The generated subgroup is
`H=〈K,g〉`; conditional expectation onto `F_2[H]` also excludes
an ambient left multiplier `L`.

The kernel in this argument may depend on `c`. No common
kernel of all left modifications is required for (6).

## Consequence and remaining question

When the actors are genuine ambient units, the nonzero source
in (3) excludes `L P_0[U g]f_0=f_0` in the group algebra of the
generated subgroup. Conditional expectation excludes an
ambient left multiplier as well.

Formula (1) does not assert a kernel for every lower block `k`.
The all-coefficient conclusion (6) concerns the literal
`(s_0,t_0),(s_1,t_1)` deletion pair. It does not assert the same
result for every incomparable word pair or for arbitrary right
coefficients between `[g]` and `f_0`.

The later [right-coefficient theorem](kaplansky-right-chart-coefficient-natural-kernel-transfer-2026-09-08.md)
separately excludes every `P_0[g]d f_0`, `d in F_2[K]`, with
the left projector fixed. Neither result implies the same
conclusion for simultaneous independent left and right
coefficients in `P_0 c[g]d f_0`.

Formula (5) still leaves open whether this actor has a nonzero
common kernel for all left `K` changes; the individual pencil
kernels do not establish that stronger statement. Even an
injective complete exterior map would supply only a necessary
representation test for a literal group-ring split.
