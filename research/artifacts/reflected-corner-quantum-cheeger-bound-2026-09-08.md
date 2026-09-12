# Reflected-corner defective quantum Cheeger estimate

2026-09-08. Self-contained finite-dimensional proof. No script,
numerical search, build, job, or new Lean verification is used.

## 1. Statement and trace convention

Let `tau=Tr/d` on `M_d(C)` and `||x||_2^2=tau(x*x)`. Let
`K:M_d->M_d` be unital, trace-preserving, completely positive,
and self-adjoint on `L^2(M_d,tau)`. Define

```text
E_K(x)=<x,(I-K)x>=tau(x*(x-K(x))).
```

This is a nonnegative quadratic form: `K` is an `L^2` contraction
by Schwarz and trace preservation, and is self-adjoint. Its square
root is a seminorm. The proof allows negative `L^2` eigenvalues of
`K`.

Let `p` be a projection with `t=tau(p)>0`. Suppose `c>0` and
`kappa>=0` satisfy

```text
E_K(q)>=c tau(q)-kappa
for every projection q<=p with tau(q)<=t/2.          (1)
```

Write `epsilon=E_K(p)`. For every self-adjoint `x=pxp`, with
`M=||x||_op`, the corner variance obeys

```text
Var_p(x):=||x-(tau(x)/t)p||_2^2
 <= (2/c^2)E_K(x)+(8M^2/c)(kappa+epsilon).           (2)
```

A second estimate, useful when the exterior energy is particularly
small, is

```text
Var_p(x)
 <= (2/c^2)(sqrt(E_K(x))+M sqrt(epsilon))^2
    +(8 kappa M^2/c)
 <= (4/c^2)(E_K(x)+M^2 epsilon)+(8 kappa M^2/c).     (3)
```

Every quantity uses the ambient normalized trace. If one instead uses
the normalized corner trace `tau/t`, the energies, squared norms,
and additive defect are all divided by `t`; multiplying the result
by `t` recovers (2)--(3). There is no implicit dimension or corner
trace factor in these formulas.

## 2. Reflecting the exterior mass

Put

```text
H=p-pK(p)p=pK(1-p)p>=0,
J(a)=pK(a)p+H^(1/2)aH^(1/2),       a in pM_dp.       (4)
```

Both summands are completely positive. The compressed first map is
self-adjoint for the restricted trace because `K` is, and the second
map is self-adjoint because `H^(1/2)` is self-adjoint. Also

```text
J(p)=pK(p)p+H=p.
```

Thus `J` is unital on the corner and trace-preserving there, by
self-adjointness. It is an `L^2` contraction for either ambient or
normalized corner trace. Its energy will be denoted `E_J`.

For self-adjoint `a=pap`, cyclicity gives

```text
E_J(a)=E_K(a)-tau(aH^(1/2)aH^(1/2))
      =E_K(a)-||H^(1/4)aH^(1/4)||_2^2
      <=E_K(a).                                    (5)
```

For a projection `q<=p`, the subtracted term is at most `tau(qH)`:
compression cannot increase the Hilbert--Schmidt norm of `H^(1/2)q`.
Since `tau(H)=tau(p)-tau(pK(p))=epsilon`, (1) therefore yields

```text
E_J(q)>=E_K(q)-epsilon
       >=c tau(q)-(kappa+epsilon),      tau(q)<=t/2. (6)
```

The purpose of reflection is that `p` is an exact fixed point of
`J`, so centering inside this corner costs no `J`-energy.

## 3. Spectral coarea in the corner

Let `J` be any self-adjoint bistochastic completely positive map on
`pM_dp`, and let `y>=0` be supported on a projection of trace at
most `t/2`. Write its spectral decomposition inside the corner as

```text
y=sum_i lambda_i e_i,       lambda_i>=0,       sum_i e_i=p.
```

Include the zero eigenspace when present. Define

```text
w_ij=tau(e_i J(e_j)).
```

Positivity gives `w_ij>=0`, self-adjointness gives `w_ij=w_ji`,
and unitality gives `sum_j w_ij=tau(e_i)`. Therefore

```text
E_J(y)=(1/2)sum_ij w_ij(lambda_i-lambda_j)^2.        (7)
```

For `q_s=1_(y>s)`, spectral coarea and Cauchy--Schwarz give

```text
integral_0^infinity 2s E_J(q_s) ds
 =(1/2)sum_ij w_ij|lambda_i^2-lambda_j^2|
 <=sqrt(E_J(y) * (1/2)sum_ij w_ij(lambda_i+lambda_j)^2)
 <=sqrt(2 E_J(y) tau(y^2)).                         (8)
```

The final inequality follows from
`(lambda_i+lambda_j)^2<=2(lambda_i^2+lambda_j^2)` and the row
and column marginals. All sums and integrals are finite.

Suppose the projection expansion for this map has additive defect
`b>=0`, meaning `E_J(q)>=c tau(q)-b` for the half-trace
projections. Every nonzero `q_s` is eligible. Integrating only over
`0<s<||y||_op`, and using
`integral 2s tau(q_s)ds=tau(y^2)`, gives

```text
c tau(y^2)-b||y||_op^2<=sqrt(2 E_J(y)tau(y^2)).      (9)
```

This proof uses the actual spectral projections, with no commutation
assumption between those projections and the channel.

## 4. Median split and the constants

Choose a median `m` of the spectral measure of the self-adjoint
matrix `x` inside `p`, using physical trace. It can be chosen in
`[-M,M]` so that both strict spectral sets `x>m` and `x<m` have
trace at most `t/2`. Put

```text
y_+=(x-mp)_+,       y_-=(mp-x)_+,
sigma=tau(y_+^2)+tau(y_-^2)=||x-mp||_2^2.
```

Then

```text
||y_+||_op^2+||y_-||_op^2
 <=(M-m)^2+(M+m)^2<=4M^2.                          (10)
```

Using the spectral weights of `x-mp`, the elementary inequality

```text
(r_+-s_+)^2+(r_--s_-)^2<=(r-s)^2
```

for real numbers `r,s` proves

```text
E_J(y_+)+E_J(y_-)<=E_J(x-mp)=E_J(x).               (11)
```

The last equality uses `J(p)=p` and self-adjointness. Add (9) for
the two parts, then apply Cauchy--Schwarz to the two resulting terms.
Equations (10)--(11) give

```text
c sigma-4bM^2<=sqrt(2 E_J(x) sigma)
              <=(c/2)sigma+E_J(x)/c.
```

Consequently

```text
sigma<=(2/c^2)E_J(x)+(8bM^2/c).                     (12)
```

The scalar `tau(x)/t` minimizes the squared distance to scalar
multiples of `p`, so `Var_p(x)<=sigma`. Apply (12) to (4), with
`b=kappa+epsilon`, and then use (5). This proves (2).

For (3), apply the same spectral coarea proof directly to the original
map `K` on `M_d`, using the zero eigenvalue on `1-p` as needed.
The two positive parts are still supported on half-trace subprojections
of `p`, so (1) applies. The energy comparison in (11) becomes

```text
E_K(y_+)+E_K(y_-)<=E_K(x-mp),
sqrt(E_K(x-mp))<=sqrt(E_K(x))+|m|sqrt(E_K(p)).
```

The second inequality is the triangle inequality for the energy
seminorm. Use `|m|<=M` in (12), now with `b=kappa`. This gives
the first line of (3); `(a+b)^2<=2a^2+2b^2` gives its second line.

## 5. Exterior boundary is necessary, already in M4

Use normalized trace `tau=Tr/4`. Set

```text
P=diag(1,1,0,0),       R=I-P,
K(a)=(Tr(Pa)/2)P+(Tr(Ra)/2)R,
p=diag(1,1,1,0),       x=P.                         (13)
```

Here `K` is the trace-preserving conditional expectation onto
`span{P,R}`, so it has all the required properties. Since `tau(p)=3/4`,
every nonzero projection `q<=p` with `tau(q)<=tau(p)/2=3/8`
has rank one. Put `a=Tr(Pq)`, so `0<=a<=1` and `Tr(Rq)=1-a`.
Then

```text
E_K(q)=1/4-(a^2+(1-a)^2)/8
      >=1/8=(1/2)tau(q).                           (14)
```

This verifies every eligible quantum projection, including those with
off-diagonal entries. Thus (1) holds with `c=1/2` and `kappa=0`.
However `K(x)=x`, while

```text
Var_p(x)=tau(P)-tau(P)^2/tau(p)
        =1/2-(1/4)/(3/4)=1/6,
E_K(x)=0,       E_K(p)=1/8.                         (15)
```

Hence an estimate forcing corner variance to zero from `E_K(x)=0`
and `kappa=0` alone is false. The boundary of the physical corner
must be included unless additional hypotheses control it.

## 6. Scope

Equations (2)--(3) establish a variance estimate for one supplied
corner under its small-projection expansion assumption. They do not
show that arbitrary channels admit a partition into such corners,
bound the boundary created by a decomposition, or produce a uniformly
close conditional expectation. Those are separate possible steps in
a quantum decomposition argument and are not asserted here.
