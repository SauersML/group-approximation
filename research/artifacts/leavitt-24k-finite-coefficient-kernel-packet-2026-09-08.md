# A finite coefficient packet for the 24k Leavitt problem

2026-09-08. Exact handwritten matrix and group-word calculations. No
code, search, numerical job, or build was run. The four words below are
an explicit finite subset of the marked kernel. They reject the earlier
F8 model and the specified scalar-field elementary ansatz. They are not
claimed to present the target group or establish a uniform gap.

## 1. Ring identities and the marked free product

Let `R=L_(F_2)(1,2)`, with

```text
t_i s_j=delta_ij,       s_0t_0+s_1t_1=1.
```

Set `s=s_0`, `t=t_0`, and `v=s_0t_1+s_1t_0`. Direct multiplication
gives

```text
ts=1,       v^2=1,       tvs=0,       st+vstv=1.       (1)
```

Indeed `vs=s_1` and `tv=t_1`, so `tvs=t_0s_1=0`, while
`vstv=(vs)(tv)=s_1t_1`. Expanding `v^2` leaves exactly
`s_0t_0+s_1t_1=1`.

In `EL_3(R)` write `x_ij(r)=I+rE_ij`, let `c` be the coordinate
cycle `(123)`, and set

```text
b_1=x_12(s),       b_2=x_12(t),       b_3=x_12(v).
```

The established generating-pair claim gives the marked epimorphism

```text
q:P=C_3*C_2^3 -> EL_3(R).
```

The word calculations only require this marked map and the displayed
matrix realization. They do not assume that its kernel is finitely
normally generated.

## 2. The elementary identities with their indices authenticated

Use `[A,B]=ABA^(-1)B^(-1)`. If `i,j,k` are pairwise distinct, put
`X=rE_ij` and `Y=qE_jk`. Then

```text
X^2=Y^2=YX=XYX=XYY=0,       XY=rqE_ik.
```

Multiplying the four factors proves

```text
[x_ij(r),x_jk(q)]=x_ik(rq).                          (2)
```

The order of the ring coefficients is the displayed order; the ring
need not be commutative. On one root, the same zero-square calculation
gives

```text
x_ij(r)x_ij(q)=x_ij(r+q),
x_ij(r)^(-1)=x_ij(-r)=x_ij(r) in characteristic two.   (3)
```

Conjugation by `c` sends `x_ij(r)` to `x_(c(i),c(j))(r)`.
Consequently its cyclic root orbits are

```text
12 -> 23 -> 31 -> 12,
13 -> 21 -> 32 -> 13.                               (4)
```

Equations (2)--(4) justify every multiplication and addition below.
They are identities in the literal elementary-matrix realization, not
an assumption that arbitrary group commutators carry ring coefficients.

## 3. Shared straight-line words and the four relations

Define inside `P`, without adding generators,

```text
gamma(W)=c W c^(-1),
d=[b_2,gamma(b_1)],       h=gamma^2(d),
a=[d,h],                 e=gamma(d),
j=a e a^(-1),
u=[b_2,gamma(b_3)],       w=[gamma^2(b_1),a].          (5)
```

The native images, with intermediate indices retained, are

```text
d=[x_12(t),x_23(s)] = x_13(ts) = x_13(1),
h=x_32(1),
a=[x_13(1),x_32(1)] = x_12(1),
e=x_21(1),
j=x_12(1)x_21(1)x_12(1) = the transposition (12),
u=[x_12(t),x_23(v)] = x_13(tv),
w=[x_31(s),x_12(1)] = x_32(s).                      (6)
```

Now take the finite packet

```text
r_* = j c j c,
R_v = [b_3,gamma(b_3)] d^(-1),
R_0 = [u,w],
R_sum = [[b_1,gamma(b_2)],h]
        [[b_3,gamma(b_1)],gamma^2(u)] a^(-1).         (7)
```

The first word is the previously recorded relation: `(12)c=(23)`
has order two, so `q(r_*)=1`. For the other three words,

```text
q(R_v)=x_13(v^2)x_13(1)=x_13(v^2+1)=1,

q(R_0)=[x_13(tv),x_32(s)]=x_12(tvs)=1,

q([[b_1,gamma(b_2)],h])
  =[x_13(st),x_32(1)]=x_12(st),

q([[b_3,gamma(b_1)],gamma^2(u)])
  =[x_13(vs),x_32(tv)]=x_12(vstv),

q(R_sum)=x_12(st)x_12(vstv)x_12(1)
         =x_12(st+vstv+1)=1.                         (8)
```

Every commutator in (6)--(8) has three distinct indices. In particular
no opposite-root commutator has been treated as multiplication of ring
coefficients. The zero-product identity `tvs=0` is tested at indices
`13,32`, not at the invalid opposite pair `13,31`.

The identity `ts=1` constructs the constant root `d` in (6).
Writing `[b_2,gamma(b_1)]d^(-1)` would give a tautological word,
not an additional independent relation. The other constant roots in
this packet are derived from this construction. This observation does
not assert that arbitrary group models of the packet have an underlying
ring in which the construction forces `ts=1`.

## 4. Finite word-length bounds

Count letters in `c,c^(-1),b_1,b_2,b_3`. Since `c^3=1` in `P`,
write `gamma^2(W)=c^(-1)Wc`; either nontrivial cyclic conjugation
therefore adds at most two letters. Inverses have the same length,
and a commutator has length at most twice the sum of its input lengths.

Straight-line accounting from (5) gives

| Shared word | Length bound |
|---|---:|
| `d` | 8 |
| `h`, `e` | 10 |
| `a` | 36 |
| `j` | 82 |
| `u` | 8 |
| `w` | 78 |

Thus the packet has the following bounds without any large expansion:

| Relation | Length bound |
|---|---:|
| `r_*` | 166 |
| `R_v` | 16 |
| `R_0` | 172 |
| `R_sum` | 108 |

For the last row, each displayed double commutator has length at most
`36`, and the terminal `a^(-1)` has length at most `36`. These are
upper bounds; cancellations could shorten the words. In particular
the finite packet can be inserted into the enumerable kernel
exhaustion of the 24k criterion, or tested directly with the same
finite-factor model. No numerical enumeration is needed to specify it.

## 5. Exact rejection of the displayed F8 model

Let `F_8=F_2[alpha]/(alpha^3+alpha+1)` and use the same coordinate
cycle, with

```text
s=alpha,       t=alpha^(-1),       v=1.               (9)
```

Here `ts=1`, so all the constant roots in (6) have the same values
as in the native model. The evaluations are exactly

```text
r_*=I,       R_v=I,
R_0=x_12(1),       R_sum=x_12(1).                    (10)
```

For `R_sum`, the three coefficients in (8) are `1,1,1`, whose
sum is one in characteristic two. Thus both later words reject the
model which satisfies the first relation.

In the left regular representation `lambda` of the finite group
`GL_3(F_8)`, every nonidentity group element has normalized trace zero.
For such an element `g`,

```text
||lambda(g)-I||_2^2=2-2 Re tr(lambda(g))=2.            (11)
```

Consequently the two failed relations in (10) each have defect
exactly `sqrt(2)`. The subgroup representations of `C_3` and `C_2^3`
are regular multiples: `1,alpha,alpha^(-1)` are linearly independent
over `F_2`, and the cycle has order three. Hence the basis changes
which put this regular representation into the frozen `24k` form do
not change these defects. Its dimension is the previously recorded
`115379712=24*4807488`. No assertion about all other relative unitaries
is inferred from (11).

## 6. The zero-product word excludes every literal scalar-field model

Let `K` be any field of characteristic two. Keep the standard coordinate
cycle in `GL_3(K)` and choose arbitrary coefficients `s,t,v` for the
three transvections. For this calculation do not assume any of (1).
Set `z=ts`. Equations (2)--(5) instead give

```text
d=x_13(z),       h=x_32(z),       a=x_12(z^2),
u=x_13(tv),      w=x_32(sz^2),
R_0=x_12(tvs z^2).                                  (12)
```

All three assigned `b_i` are nonidentity exactly when `s,t,v` are
all nonzero. In a field their product `tvs(ts)^2` is then nonzero,
so `R_0!=I`. Neither `r_*=I` nor `R_v=I` was assumed in this
argument. It excludes all literal scalar-field assignments with
three nonidentity transvections on this one root, and in particular
all those in which the elementary abelian factor is faithful.

This is a statement about that specified matrix ansatz. It does not
classify abstract finite-group representations of `P`, prove an
obstruction for general matrix-valued coefficients, or justify assigning
ring coefficients to arbitrary unitaries.

## 7. Endpoint boundary

The set `{r_*,R_v,R_0,R_sum}` is an authenticated finite subset of
`ker q`. No assertion here identifies its normal closure with the
whole kernel. Rejecting the displayed finite model and the literal
scalar-field ansatz supplies no dimension-uniform normalized-HS lower
bound for all frozen-factor representations.

The existence of other exact models of this packet, and its possible
approximate models in unbounded dimension, require separate arguments.
Neither hyperlinearity nor nonhyperlinearity of the Leavitt unit group
is concluded. The unrestricted 24k feasibility branches remain open.
