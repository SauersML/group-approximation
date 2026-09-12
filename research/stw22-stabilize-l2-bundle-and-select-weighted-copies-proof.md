---
rg: 2
id: stw22-stabilize-l2-bundle-and-select-weighted-copies-proof
kind: route
title: Stabilize the intrinsic L2 bundle and select exact weighted copies
target: stw22-dim1-factor-bundles-have-uniform-traces
requires:
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-stabilized-l2-selection-audit-2026-08-30.md
---

Write `H` for the Hilbert `C(K)`-module in the claim and `H_x` for its
Hilbert-space fibre.  The canonical map identifies

```text
H_x=L^2(M_x,tau_x).
```

We use the maximum metric on finite tuples.

## 1. One complete ambient Hilbert space

By stabilization of countably generated Hilbert modules, there is a
`C(K)`-linear isometry

```text
V:H -> C(K,ell^2)
```

whose range is the range of an adjointable projection `P` on the standard
module.  Fibrewise, `V_x:H_x -> ell^2` is an isometry.  If `x_i -> x`,
`xi_i in P_xi(ell^2)`, and `xi_i -> xi` in `ell^2`, then `P_x xi=xi`:
strong continuity of the fibre projections gives

```text
||P_x xi-xi||
 <=||P_x(xi-xi_i)||+||(P_x-P_xi)xi_i||+||xi_i-xi|| ->0,
```

where the middle term is split once more at the fixed vector `xi`.
Thus the total fibre range is closed in `K times ell^2`.

We also need to recover operator-bounded sections after making a selection
in `H`.  The following identity is decisive:

```text
M_1={xi in H: xi_x belongs to (M_x)_1 for every x in K}.       (OB)
```

Only the reverse inclusion needs proof.  Approximate such a `xi` in `H`
by `b_n in M`.  Let

```text
r(b)=u min(|b|,1),                 b=u|b|
```

be spectral clipping into `M_1`.  In each finite-factor `L^2` space,
`r(b_x)` is the metric projection of `b_x` onto the operator-norm unit
ball.  Indeed, with `h=(|b_x|-1)_+`, the variational inequality follows
from `Re(u*y)<=1` for every contraction `y`:

```text
Re tau_x((b_x-r(b_x))^*(y-r(b_x)))<=0.
```

Consequently

```text
||r(b_n)_x-xi_x||_2<=||b_n(x)-xi_x||_2
```

uniformly in `x`.  Hence `r(b_n)` converges to `xi` in uniform `2`-norm.
Tracial completeness says that `M_1` is complete for this metric, proving
`(OB)`.  Thus an `H`-section selected fibrewise inside the operator unit
balls is automatically an element of `M_1`.

## 2. The weighted-copy multifunction

Fix `m>=1`, `gamma>0`, and a positive contraction `a in M` such that

```text
m tau_x(supp(a_x)) <= 1-gamma                 (x in K). (S1)
```

For each `x`, let `F_x(a)` be the set of tuples `(v_1,...,v_m)` in
`(M_x)_1^m` satisfying

```text
v_j^*v_j=a_x,
(v_i v_i^*)(v_j v_j^*)=0                    (i!=j).    (S2)
```

Finite-factor comparison and `(S1)` make every value nonempty.  Regard
the values, through `V_x^m`, as subsets of the fixed complete metric space
`(ell^2)^m`.

Every `F_x(a)` is closed there.  The operator unit ball is `L^2`-closed;
on bounded sets, `L^2` convergence makes `v_n^*v_n` converge in `L^1`,
and similarly preserves the orthogonality relations in `(S2)`.

The multifunction `x |-> F_x(a)` is lower semicontinuous.  We record the
uniform finite-factor estimate which proves this, since this is the step at
which a qualitative polar-decomposition argument would not be enough.

Fix `epsilon>0`.  There is a `delta>0`, depending only on
`m,gamma,epsilon`, such that the following holds in every finite factor
`(N,tau)`.  If `0<=a<=1` satisfies `(S1)`, the elements `b_j` have norm at
most two, and

```text
max_j ||b_j^*b_j-a||_2 < delta,
max_(i!=j) ||(b_i b_i^*)(b_j b_j^*)||_2 < delta,       (S2a)
```

then there is a tuple in `F(a)` within `epsilon` of `(b_j)` in maximum
`2`-norm.

To prove the estimate, first choose `eta>0`, to be fixed from `epsilon`, and
put

```text
p=supp(a),       q=1_[eta,1](a),       r=p-q,
d_j=b_j a^(-1/2)q,                    C=2 eta^(-1/2).
```

Thus `d_j=d_jq`, `||d_j||<=C`, and, writing `B_j=b_jb_j^*`,

```text
rho:=max_j ||d_j^*d_j-q||_1 <= eta^(-1)delta.          (S2b)
```

Moreover, if `A_j=d_jd_j^*`, then `A_j<=eta^(-1)B_j`.
Using the positive functionals `z |-> tau(A_j^(1/2)zA_j^(1/2))`
and `z |-> tau(B_i^(1/2)zB_i^(1/2))` gives

```text
||d_i^*d_j||_2^2=tau(A_iA_j)
 <=eta^(-2)tau(B_iB_j)
 <=eta^(-2)delta.
```

Set `kappa=eta^(-1)delta^(1/2)`.

We now construct partial isometries `s_1,...,s_m` with common initial
projection `q` and orthogonal ranges.  Suppose `s_1,...,s_(j-1)` have been
chosen and set

```text
e_j=1-sum_(i<j)s_i s_i^*,       z_j=e_jd_j.
```

If `E_i=||s_i-d_i||_2`, then

```text
||(1-e_j)d_j||_2^2
 =sum_(i<j)||s_i^*d_j||_2^2
 <=sum_(i<j)(C E_i+kappa)^2,

||z_j^*z_j-q||_1
 <=rho+sum_(i<j)(C E_i+kappa)^2=:sigma_j.              (S2c)
```

Here we used
`||s_i^*d_j||_2<=C||s_i-d_i||_2+||d_i^*d_j||_2`.
Let `z_j=w_j|z_j|` be the polar decomposition, with
`f_j=w_j^*w_j<=q`.  Since

```text
tau(q-f_j)<=sigma_j,
tau((f_j-|z_j|)^2)<=tau(|q-z_j^*z_j|)<=sigma_j,        (S2d)
```

the second inequality following from
`(1-sqrt(t))^2<=|1-t|`, the polar part is within
`sqrt(2sigma_j)` of `z_j` after filling its missing initial projection.
Indeed, `(S1)` gives

```text
tau(e_j)=1-(j-1)tau(q)>=tau(q)+gamma,
```

so finite-factor comparison supplies a partial isometry from `q-f_j` into
`e_j-w_jw_j^*`.  Adding it to `w_j` gives `s_j^*s_j=q`, with range under
`e_j`, and

```text
||s_j-z_j||_2<=sqrt(2sigma_j),
E_j<=sqrt(2sigma_j)+sqrt(sum_(i<j)(C E_i+kappa)^2).    (S2e)
```

Starting with the empty sum, `(S2c)`--`(S2e)` are a finite recurrence.
For fixed `m` and `eta`, they imply

```text
max_(j<=m) E_j ->0                    as delta->0,       (S2f)
```

uniformly over the factor and over `a`.

The complement of the `m` high ranges has trace `1-m tau(q)`.  Since

```text
m tau(r)<=1-gamma-m tau(q),
```

comparison supplies partial isometries `t_1,...,t_m` with common initial
projection `r`, mutually orthogonal ranges, and ranges orthogonal to all
the high ranges.  Define

```text
v_j=(s_j+t_j)a^(1/2).
```

Then `(v_j)` satisfies `(S2)` exactly.  The three right-support pieces
`q,r,1-p` give

```text
||v_j-b_j||_2
 <=E_j+||t_j a^(1/2)r||_2+||b_jr||_2+||b_j(1-p)||_2
 <=E_j+sqrt(eta)+sqrt(eta+delta)+sqrt(delta).           (S2g)
```

Choose `eta` so that `2sqrt(eta)<epsilon/2`, and then choose `delta`
so that `(S2f)` and the last two error terms make the right side of
`(S2g)` smaller than `epsilon`.  This proves the uniform estimate.

Now fix an exact tuple `v in F_x(a)` and an ambient ball
`B(V_x^m(v),R)`.  Fibre density gives sections whose values at `x`
approximate the components of `v` in `2`-norm.  Clipping those sections as
in `(OB)` does not increase their distance from the fibre contractions
`v_j`; hence we may take a tuple `b in M_1^m` with

```text
max_j ||b_j(x)-v_j||_2 < zeta,                          (S2h)
```

where `zeta>0` is arbitrary.  On the operator unit ball, the source and
range-overlap defects are uniformly Lipschitz in `2`-norm.  For example,

```text
||b_j^*b_j-v_j^*v_j||_2 <=2||b_j-v_j||_2,
||B_iB_j-(v_iv_i^*)(v_jv_j^*)||_2
 <=2||b_i-v_i||_2+2||b_j-v_j||_2.                      (S2i)
```

Choose the correction tolerance in the uniform estimate smaller than
`R/4`, and then choose `zeta` so that `(S2i)` makes all defects at `x`
smaller than half of its corresponding `delta`.  The embedded section
`V^m(b)` and all defect functions are continuous.  After shrinking to a
neighbourhood `U` of `x`, the defects remain below `delta` and

```text
||V_y^m(b(y))-V_x^m(v)|| < R/2                 (y in U).
```

For every `y in U`, the uniform estimate supplies `w(y) in F_y(a)` with
`||w(y)-b(y)||_2<R/4`.  Therefore

```text
||V_y^m(w(y))-V_x^m(v)|| <3R/4,
```

so the prescribed ambient ball meets every nearby value.  This is exactly
lower semicontinuity.

The values form a uniformly equi-locally-path-connected family, with a
modulus independent of the factor and of `a`.  If `v,w in F_x(a)`, take
their polar frames.  The sum of the partial isometries mapping the `m`
orthogonal range projections of `v` to those of `w` extends to a unitary
`u in M_x`, since the complementary projections have equal trace.  Thus
`uv_j=w_j` for every `j`.  If `u=exp(ih)` is the principal logarithm and
`u_t=exp(ith)`, scalar functional calculus gives

```text
(u_t-1)^*(u_t-1) <= (u-1)^*(u-1).
```

Therefore the path `(u_t v_1,...,u_t v_m)` remains in `F_x(a)` and

```text
||u_t v_j-v_j||_2 <= ||w_j-v_j||_2.                    (S3)
```

In particular every value is path connected.  If `v,w` both lie in a
`delta`-ball about an ambient point, `(S3)` joins them inside the concentric
`3delta`-ball.  This is the uniform ambient equi-`LC^0` condition.

The one-dimensional finite-selection theorem for lower-semicontinuous
maps with nonempty closed, path-connected, equi-`LC^0` values now gives a
continuous selection

```text
x |-> (v_1(x),...,v_m(x)) in F_x(a).                   (S4)
```

Via the complemented embedding, `(S4)` is an element of `H^m`; by `(OB)`
its components belong to `M_1`.  Hence `(S2)` holds globally in `M`.

## 3. Gap traces vanish

Fix `x_0 in K`, a positive contraction `b in K_x0`, `epsilon>0`, and
`m>=1`.  Set `c=(b-epsilon)_+`.  Since
`tau_x0(b^2)=0`, continuity and Chebyshev's inequality give a neighbourhood
`U` of `x_0` such that

```text
tau_y(supp(c_y))<1/(2m)                         (y in U).
```

Choose `h in C(K)_+` equal to one near `x_0` and supported in `U`, and put
`d=hc`.  Then `[d]=[c]` in `K_x0/J_x0`, and `(S1)` holds globally for `d`
with `gamma=1/2`.  Apply `(S4)` to obtain `m` exact weighted copies with
orthogonal ranges.  Each `v_j` belongs to `K_x0` because
`v_j^*v_j=d in K_x0`.  If `sigma` is a bounded positive trace on the gap,
then

```text
m sigma([c])
 =sum_j sigma([v_j^*v_j])
 =sigma(sum_j [v_jv_j^*])
 <=||sigma||.
```

Letting `m` tend to infinity and then `epsilon` decrease to zero proves
that `sigma([b])=0`.  Every gap is therefore bounded-trace-free.  The exact
fibre-gap criterion gives the asserted trace formula and uniform
`2`-continuity.

Finally, if `M_1` is the uniform-`2` completion of the unit ball of a
separable C-star algebra, a countable norm-dense subset of that unit ball
is uniform-`2` dense.  Its linear span generates `H`, proving the last
assertion of the claim.
