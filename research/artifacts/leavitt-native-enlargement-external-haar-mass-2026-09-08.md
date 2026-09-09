# Native enlargement requires mass outside the canonical group factor

2026-09-08. Written finite-trace and Hilbert-space proof. No
execution, build, search, or new Lean verification is used.

The canonical backward-lamp subgroup algebras have a fixed forward
Haar boundary. Here an internal Kazhdan estimate excludes all
finite-dimensional algebras inside the native group factor under
exact capture and commutation, and gives a quantitative requirement
on any enlargement in a larger finite tracial algebra. Property
`(T)` is an explicit input. An asymptotic extension permits approximate
capture and Haar commutation. The result is not a nonhyperlinearity
argument and does not rule out external matrix-algebra constructions.

## 1. Native data and the convention for the gap

Let `R=L_(F_2)(1,2)`, with

```text
s=s_0, t=t_0, a=s_1, b=t_1,
ts=ba=1, ta=bs=0, st+ab=1.
```

Use `H=GL_4(R)=EL_4(R)`, `L=diag(GL_3(R),1)`, and
the compressor `u` and finite subgroup

```text
k_+=diag(I_3,1+a t^3),
k_-=diag(I_3,1+s^3 b),        F_0=<k_+,k_->≅S_3.
```

The committed native setup and identities are in
[[native-s3-algebra-enlargement-obstructs-scalar-commutants]].
The particular identities needed below are

```text
y_+=u k_+ u^(-1)=x_14(a),
y_-=u k_- u^(-1)=x_41(b),
H=<L,uF_0u^(-1)>.
```

For every `r in R`, put `g_r=x_21(r b) in L`. The
three-distinct-index commutator formula and `ba=1` give

```text
g_r y_+ g_r^(-1)=x_24(r)y_+.                        (1)
```

These elements are distinct as `r` varies through the infinite
ring `R`.

Let `N=L(H)` with canonical normalized trace `tau`. The group
`H` is infinite simple by
[[binary-leavitt-elementary-group-is-simple]]. It is ICC: any
finite conjugacy orbit would give an action of the infinite simple
group on a finite set, which must be trivial, and the center of a
nonabelian simple group is trivial. Thus the invariant vectors for
conjugation on `L^2(N)` are precisely the scalar vectors.

The property `(T)` consequence of
[[binary-leavitt-unit-group-has-tt-mod-t]] supplies an internal
conjugation gap. Fix a finite generating list `S_L` of `L` and
put `S=S_L union {u,k_+,k_-}`. The displayed generation identity
shows that `S` generates `H`. Choose `0<kappa_H<=1` so that

```text
kappa_H ||x||_2
 <=max_(g in S)||lambda(g)x-xlambda(g)||_2
for every x in L^2(N) with tau(x)=0.                (2)
```

This is a maximum convention, not a sum-of-squares convention.
A usual Kazhdan pair gives such a constant for this finite generating
set by fixed-word telescoping; reducing the constant to at most
one is harmless. No numerical value for `kappa_H` is asserted.

Let `Q` be any finite tracial von Neumann algebra containing `N`
unitally and trace-preservingly. Suppress `lambda` on the native
group unitaries. Let `A subset Q` be a unital finite-dimensional
subalgebra satisfying exactly

```text
[A,L]=0,        k_+,k_- in A.                       (3)
```

Set `B=uAu*`, write `E_D` for the trace-preserving expectation
onto a subalgebra `D`, and define

```text
alpha=integral_(v in U(A)) ||v-E_B(v)||_2^2 dv,
eta_A=integral_(v in U(A)) ||v-E_N(v)||_2^2 dv,
c_*=1-exp(-1/16).                                   (4)
```

All Haar measures have mass one. All `L^2` norms use the same
normalized ambient trace.

**Theorem.** If `alpha<=1/4`, then

```text
eta_A>=1/128-alpha/(kappa_H^2 c_*).                  (5)
```

If `A subset N`, without any restriction on `alpha`, then

```text
alpha>=kappa_H^2 c_*/128.                           (6)
```

## 2. A Haar supremum-to-mean bound in an arbitrary finite extension

We need a form that does not assume the ambient algebra is a full
matrix algebra. Let `D subset Q` be any unital von Neumann
subalgebra. For every contraction `z in A`,

```text
||z-E_D(z)||_2^2
 <=2 integral_(v in U(A))||v-E_D(v)||_2^2 dv.        (7)
```

Here is a finite-algebra proof. The map
`P=E_A E_D|_A:A->A` is unital completely positive and
trace-preserving. Form the Hilbert-space completion of `A tensor A`
after quotienting its null space for the positive form

```text
<a tensor b,c tensor d>=tau(b* P(a*c)d).
```

Complete positivity gives positivity of this form. The formula

```text
pi(v)(a tensor b)=v a tensor b v*,       v in U(A),
```

defines a unitary representation: its inner products are unchanged
by the trace identity. For `xi=1 tensor 1`, one has `||xi||=1`
and

```text
<xi,pi(v)xi>=tau(P(v)v*)=||E_D(v)||_2^2.
```

In particular, with `Pi` the Haar projection onto the invariant
vectors,

```text
||v-E_D(v)||_2^2=(1/2)||pi(v)xi-xi||^2,
integral ||v-E_D(v)||_2^2 dv=||xi-Pi xi||^2.
```

Because `pi(v)` fixes `Pi xi`, its displacement of `xi` has
norm at most `2||xi-Pi xi||`. This proves (7) for unitaries.
The unit ball of a finite-dimensional unital algebra is the convex
hull of its unitaries, so the linearity of `I-E_D` and convexity
of the squared norm extend (7) to all contractions. In particular
(7) applies to the central self-adjoint contraction used below.

## 3. Canonicality and exact commutation make the reverse defect one

For every `x in A`, (3) and trace cyclicity imply

```text
<x,g_r y_+ g_r^(-1)>=<x,y_+>.
```

Thus `E_A(g_r y_+g_r^(-1))=E_A(y_+)`. Average over `M`
distinct choices of `r`. By (1) their group unitaries are
orthonormal in the canonical trace, also in the extension `Q`.
The average has `L^2` norm `1/sqrt(M)`. Conditional expectation
is contractive, so `||E_A(y_+)||_2<=1/sqrt(M)` for every `M`.
It follows that

```text
E_A(y_+)=0.                                         (8)
```

Exact capture puts `y_+` in `B`, so the reverse supremum
leakage of `B` into `A` is exactly one. The upper bound is one
because expectations are `L^2` contractions on contractions.
By (7), the reverse Haar mean satisfies

```text
beta:=integral_(v in U(B))||v-E_A(v)||_2^2 dv>=1/2.  (9)
```

This argument applies to the actual external algebra `A`; it
does not identify the external `L`-commutant with the native
complementary group algebra.

## 4. The finite central-height calculation still works in Q

We reproduce the finite-trace part of the native height argument
to make its ambient scope explicit. Let `p_i` be the central atoms
of `A`, of simple degrees `a_i`, and put

```text
q_i=u p_i u*,       t_i=tau(p_i),
w_i=t_i/a_i^2,      h_i=log(w_i),
m_ij=tau(p_i q_j).
```

Let `P_i,Q_j` be the Hilbert projections onto `p_i A,q_j B`
inside `L^2(Q)`, and let `H_ij=Tr_(Hilbert)(P_i Q_j)`.
These are finite-rank Hilbert projections, even if `Q` is infinite
dimensional. Haar matrix-entry covariance and `L^2` contractivity
give

```text
w_i H_ij<=m_ij,       w_j H_ij<=m_ij,
alpha=sum_ij(m_ij-w_i H_ij),
beta =sum_ij(m_ij-w_j H_ij).                         (10)
```

For example, the covariance of a Haar unitary in the block `p_i A`
is `w_i P_i`; its projected squared norm onto `q_j B` is at
most `||q_j v||_2^2=tau(q_j p_i)`. This proves the first
bound, and the other follows by interchanging the blocks.
The matrix `m` is nonnegative and has row and column marginals
`t_i`.

Define its upward and downward weighted movements by

```text
up=sum_(h_j>h_i)m_ij(1-exp(-(h_j-h_i))),
down=sum_(h_i>h_j)m_ij(1-exp(-(h_i-h_j))).
```

Equation (10) implies

```text
up<=alpha,       down>=beta-alpha.
```

For the latter bound, the positive part of
`sum_ij(w_i-w_j)H_ij=beta-alpha` occurs when `h_i>h_j`,
and its summands are at most those of `down`. Under
`alpha<=1/4`, (9) therefore gives `down>=1/4`.
The rest of this calculation needs only `beta-alpha>=1/4`,
so it also applies whenever that inequality is supplied directly.

Choose a median `c` for the heights under weights `t_i`, and
put `r=1/16`. If `T=sum_(|h_i-c|>=r)t_i`, the contribution
to `down` from edges with both endpoints inside this interval
is at most `2r`; all other edges have mass at most `2T`.
Hence `T>=1/16`. One tail has mass at least `1/32`, and
the opposite median side has mass at least `1/2`.

Choose the increasing ramp of width `r` between that tail and
the opposite median side, clipped to `[0,1]`. Call it `f`.
Its two endpoint level sets have the indicated masses, so
`Var_t(f)>=1/64`. Stationarity of `m`, monotonicity, and

```text
min(x/r,1)<=(1-exp(-x))/(1-exp(-r)),       x>=0,
```

give

```text
sum_ij m_ij |f(h_i)-f(h_j)|^2
 <=2up/(1-exp(-r))<=2alpha/c_*.
```

Indeed the squared difference is at most the absolute difference;
stationarity equates the positive and negative total differences,
and the positive part is bounded by `up/(1-exp(-r))`.
Consequently

```text
z=sum_i (f(h_i)-sum_j t_j f(h_j))p_i in Z(A)
```

satisfies

```text
z=z*, tau(z)=0, ||z||_op<=1, ||z||_2^2>=1/64,
||[u,z]||_2^2<=2alpha/c_*.                           (11)
```

The last commutator square equals the displayed balanced-flow sum.
Only the ambient finite trace and finite-dimensionality of `A`
were used, not integrality of multiplicities in an ambient matrix.

## 5. The internal projection loses almost all of the height

Since `z in Z(A)`, (3) gives

```text
[z,g]=0 for every g in S_L union {k_+,k_-}.
```

The trace-preserving expectation `E_N:Q->N` is an `N`-bimodule
map and an `L^2` contraction. It preserves trace zero and the
displayed exact commutators. Apply (2) to `E_N(z)`. The only
possibly nonzero generator commutator is the one with `u`, so
(11) gives

```text
||E_N(z)||_2^2
 <=kappa_H^(-2)||[u,E_N(z)]||_2^2
 <=2alpha/(kappa_H^2 c_*).                          (12)
```

Orthogonality of conditional expectation, followed by (7), yields

```text
2eta_A >= ||z-E_N(z)||_2^2
         =||z||_2^2-||E_N(z)||_2^2
         >=1/64-2alpha/(kappa_H^2 c_*).
```

This proves (5), including the claimed inline Haar-mean control
for the central contraction. If `A subset N`, then `eta_A=0`.
Thus (6) follows when `alpha<=1/4`. When `alpha>1/4`, it
holds automatically because `kappa_H<=1` and `0<c_*<1`.

## 6. Approximate capture and commutation have the same mass obstruction

The ambient algebra may now vary. Let `Q_n` be finite tracial
von Neumann algebras, each containing a trace-preserving copy of
the fixed canonical factor `N`. Use the same native group notation
in each copy. Let `A_n subset Q_n` be unital finite-dimensional
subalgebras and put

```text
e_n=sum_(s in S_L) integral_(v in U(A_n))||[s,v]||_2^2 dv,
kappa_n=max_(sign=+,-)||k_sign-E_(A_n)(k_sign)||_2,
alpha_n=integral_(v in U(A_n))||v-E_(uA_nu*)(v)||_2^2 dv.
```

Assume `e_n,kappa_n,alpha_n ->0`. Define `eta_(A_n)` as
in (4), using the expectation onto that copy of `N`. Then

```text
liminf_n eta_(A_n)>=1/128.                          (13)
```

No exact representation of `F_0` inside `A_n` is required.
All native group relations already hold in its ambient copy of `N`.

First, Haar averaging by `U(A_n)` is the expectation onto
`A_n' intersect Q_n`. For every `s in S_L`,

```text
integral ||[s,v]||_2^2 dv
 =2||s-E_(A_n' intersect Q_n)(s)||_2^2.
```

Every contraction `x in A_n` therefore satisfies

```text
||[s,x]||_2<=sqrt(2e_n).                            (14)
```

For a fixed word `g in L` of length `ell` in `S_L` and
its inverses, telescoping gives `||[g,x]||_2<=ell sqrt(2e_n)`.

Set `Y=y_+` and `X_n=E_(A_n)(Y)`, a contraction. Fix `M`
distinct conjugates from (1); let `L_M` bound the word lengths
of their conjugating elements in `S_L` and its inverses, and put

```text
T_M=(1/M)sum_(j=1)^M g_j Y g_j*.
```

The trace is canonical in every `Q_n`, so `||T_M||_2=1/sqrt(M)`.
Using (14) and the identity `||X_n||_2^2=<Y,X_n>` gives

```text
||X_n||_2^2
 <=|<T_M,X_n>|+L_M sqrt(2e_n)
 <=1/sqrt(M)+L_M sqrt(2e_n).                        (15)
```

Take the limit in `n` at fixed `M`, and then let `M` grow.
This proves `||E_(A_n)(Y)||_2->0`, without a uniform bound
on the growing conjugator lengths.

Let `B_n=uA_nu*`. Capture gives
`||Y-E_(B_n)(Y)||_2<=kappa_n`. Since `E_(B_n)(Y)` is a
contraction, the reverse supremum leakage `rho_n` obeys

```text
1>=rho_n
 >=sqrt(1-||E_(A_n)(Y)||_2^2)-kappa_n ->1.
```

By (7), its reverse Haar mean `beta_n` satisfies
`beta_n>=rho_n^2/2`. Hence `beta_n-alpha_n>=1/4` for all
sufficiently large `n`. Section 4 supplies central self-adjoint
contractions `z_n in A_n` with the trace and norm bounds (11)
and `||[u,z_n]||_2^2<=2alpha_n/c_*`.

Their other generator commutators satisfy

```text
max_(s in S_L)||[s,z_n]||_2^2<=2e_n,
max_(sign=+,-)||[k_sign,z_n]||_2^2<=4kappa_n^2.       (16)
```

The second estimate follows because `z_n` commutes with
`E_(A_n)(k_sign)`. Projecting into `N` and using (2) proves

```text
||E_N(z_n)||_2^2
 <=kappa_H^(-2) max{2e_n,4kappa_n^2,2alpha_n/c_*}
 ->0.                                               (17)
```

Finally (7) and orthogonality give, at these sufficiently large
indices,

```text
eta_(A_n)
 >=1/128-(1/(2kappa_H^2))
              max{2e_n,4kappa_n^2,2alpha_n/c_*}.
```

This proves (13), including for varying `Q_n`. The proof uses
only the fixed-word order of limits in (15), not finite-group
exactification or an unproved uniform approximation of a growing
native word set.

## 7. What this rules out and what remains possible

The internal conclusion concerns arbitrary finite-dimensional
subalgebras of `N` meeting (3), irrespective of whether they are
group algebras or have regular central weights. In particular,
replacing the finite backward subgroup algebras by other finite
algebras inside the canonical amenable lamp-compressor algebra
cannot meet (3) and make the forward leakage vanish.

The same internal impossibility holds with capture and commutation
tending to zero as in Section 6. External algebras instead must
have the positive asymptotic mass (13) outside `N`; algebras with
that mass remain possible under this result.
The projection in (12) is always the expectation onto the canonical
native factor. It is not an expectation onto the full external
commutant, and no equality between those spaces is assumed.

Both versions require actual canonical copies of `N` in their
finite tracial ambient algebras. They do not silently identify
varying coordinate matrix algebras with subalgebras of the native
factor or give uniform transfer to growing microstate word sets.
Nor does amenability of the lamp-compressor subgroup supply such
an identification. A matrix enlargement would need genuinely
external algebraic mass and its own approximation estimates.
General enlargement, heat rounding, and hyperlinearity remain
unresolved by this result.
