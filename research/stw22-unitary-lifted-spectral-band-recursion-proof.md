---
rg: 2
id: stw22-unitary-lifted-spectral-band-recursion-proof
kind: route
title: Lift the high filling by unitaries and recursively trivialize every low spectral-band complement
target: stw22-all-finite-factor-weighted-copy-uniform-loop-fillings
requires:
  - stw22-matrix-weighted-copy-uniform-loop-fillings
  - stw22-diffuse-stiefel-uniform-loop-fillings
artifacts:
  - research/artifacts/stw22-diffuse-weighted-loop-extension-audit-2026-08-30.md
---

All continuity below is operator-norm continuity in a fixed matrix factor
and `2`-norm (equivalently strong continuity on bounded sets) in a `II_1`
factor.

## 1. The needed Stiefel fillings admit unitary lifts

Let `P` be a projection in a finite factor and let `Q<P`.  Identify the
Stiefel space of frames with initial projection `Q` and range below `P`
with

```text
St(Q,P)={v in PNP:v^*v=Q}.
```

Two facts will be used.

First, every loop in `St(Q,P)` fills, and a filling can be chosen together
with a continuous `U:D^2->U(PNP)` satisfying `U(y)Q=V(y)`.  In matrices,
`St(Q,P)=U(rank P)/U(rank(P-Q))` is simply connected because `P-Q` has
positive rank.  The pullback over the contractible disk of the principal
bundle `U(PNP)->St(Q,P)` is trivial, so the filling has a unitary lift.  In
a `II_1` factor, the one-dimensional unitary-selection theorem lifts the
boundary loop to `L:S^1->U(PNP)`: first select `u_z` carrying `Q` to the
final projection `v_zv_z^*`; then `u_z^*v_z` is a continuous unitary in
`Q N Q`, and `L_z=u_z(u_z^*v_z+P-Q)` satisfies `L_zQ=v_z`.  Jekel's
strong contraction of the unitary group extends `L` over the disk.
Projecting the extension gives the claimed lifted filling.  This use is
nonquantitative.

Second, the *small* Stiefel fillings in the two required predecessor
theorems can also be chosen with unitary lifts.  This is automatic in the
matrix case by the same pullback argument.  In the diffuse proof, the
controlled direct-rotation annulus has the form

```text
H(z,t)=D(z,t)v(z),       D(z,t) in U(N),
```

and its inner loop has the form

```text
q-e_z+w_z,
e_z=a_z e_0 a_z^*,       w_z=a_z c_z w_0 a_z^*.
```

Put `f_0=q-e_0` and extend `w_0` inside `(1-f_0)N(1-f_0)` to a unitary
`R_0`.  During the Jekel fillings of `a_z` and `c_z`, the displayed frame
is the image of `q` under the unitary

```text
B=a (f_0+cR_0) a^*.
```

Indeed `(f_0+cR_0)q=f_0+cw_0`, so `Bq` is exactly the localized frame.
Thus the inner disk has an explicit lift.  On its boundary define the lift
of the annulus by

```text
C(z,t)=D(z,t)D(z,1)^*B(z).
```

Then `C(z,1)=B(z)` and `C(z,t)q=H(z,t)`, so the two lifts glue on the whole
disk.  The projected frames are exactly those of the predecessor proof;
introducing `B` and `C` changes no metric estimate.  If spectral capture
returns the whole source, use instead the lifted nonquantitative filling
from the first fact: every frame in that Stiefel space is within
`2sqrt(tau(q))` of `q`, which is precisely the diameter estimate used in
that case.  Hence Jekel's contraction is never required to be metrically
controlled.

For an `m`-frame with common source `r`, choose a fixed reference frame
`s_1,...,s_m` and put `Q=sum_j s_js_j^*`.  The correspondence

```text
(t_1,...,t_m) <-> sum_j t_js_j^* in St(Q,P)             (UL1)
```

is an isometry for the Hilbert-sum metric.  Hence both lifted-filling facts
apply verbatim to multicopy frames.

## 2. Relative extension of one bounded spectral band

Suppose

```text
g(y)=U(y)g_0U(y)^*,       y in D^2,                     (UL2)
```

where `U:D^2->U(N)` is continuous.  On the boundary let
`xi_1,...,xi_m` be an orthogonal frame with common source `r`, ranges below
`g(z)`, and assume

```text
m tau(r)<tau(g_0).                                      (UL3)
```

Conjugating by `U(z)^*` puts the boundary frame in the fixed corner
`g_0Ng_0`.  Choose a fixed reference frame there and use `(UL1)`.  The
first fact of Step 1 fills the resulting Stiefel loop and supplies a unitary
lift `W:D^2->U(g_0Ng_0)`.  Extend every such corner unitary by `1-g_0`
when multiplying it in `N`.  Then

```text
Xi_j(y)=U(y)W(y)s_j
```

is the required exact boundary-preserving extension.  More importantly,
its remaining complement is explicitly trivialized:

```text
g(y)-sum_j Xi_j(y)Xi_j(y)^*
 =U(y)W(y)(g_0-sum_j s_js_j^*)W(y)^*U(y)^*.             (UL4)
```

This formula, rather than a selection theorem for arbitrary projection
fields over a disk, is what makes iteration possible.

## 3. Countably many low spectral bands

Let `0<=b<=eta`, put `p=supp(b)`, and assume a boundary weighted
`m`-frame `x_j(z)` lies in a moving complement having a trivialization
`(UL2)`, with strict unused trace after all `m` copies.  Define

```text
r_n=1_((eta 2^(-(n+1)),eta 2^(-n)] )(b).
```

After discarding zero bands, the bounded inverses on `r_n` make

```text
xi_(j,n)(z)=x_j(z)b^(-1/2)r_n                           (UL5)
```

continuous.  They are orthogonal `m`-frames.  Apply Step 2 to the first
band.  Formula `(UL4)` supplies a unitary trivialization of the new
complement, so Step 2 applies to the next band, and so on.  The strict
unused trace after the full support implies `(UL3)` at every finite stage.

Write the extensions as `Xi_(j,n)`.  The sums

```text
X_(j,k)(y)=sum_(n<=k) Xi_(j,n)(y)b^(1/2)r_n             (UL6)
```

converge uniformly in `2`-norm because orthogonality gives

```text
sum_j ||X_(j,l)-X_(j,k)||_2^2
 =m sum_(k<n<=l) tau(br_n).                             (UL7)
```

For fixed `j`, the polar sum behind `X_(j,k)` is a partial isometry, so
`||X_(j,k)||<=sqrt(eta)`.  An operator-norm-bounded `L^2`-Cauchy sequence in
a finite von Neumann algebra has its limit in the same operator-norm ball
of `N`; denote the limit by `X_j`.  On finite sums,

```text
X_(j,k)^*X_(j,k)=b sum_(n<=k)r_n,
X_(i,k)^*X_(j,k)=0             (i!=j).
```

Bounded `L^2` convergence implies `L^1` convergence of products, since

```text
||x_k^*y_k-x^*y||_1
 <=||x_k-x||_2||y_k||_2+||x||_2||y_k-y||_2.
```

It follows that `X_j^*X_j=b` and `X_i^*X_j=0` for `i!=j`; the latter gives
`(X_iX_i^*)(X_jX_j^*)=0`.  Multiplication by the moving complement is
`L^2`-continuous on bounded sets, so the limits remain in it.  On the
boundary, `X_(j,k)(z)=x_j(z)sum_(n<=k)r_n`, whose squared tail norm is
`tau(b sum_(n>k)r_n)`, independent of `z`; hence the boundary is exact.
Thus the limits belong to `N`, have source `b`, have pairwise orthogonal
ranges, stay in the prescribed moving complement, and equal the original
tuple on `S^1`.  No unitary trivializations are required to converge; only
the weighted sums `(UL6)` are taken to a limit.  For any other exact
`b`-weighted `m`-frame `(x_(0,j))`, the crude but uniform estimate is

```text
(sum_j||X_j(y)-x_(0,j)||_2^2)^(1/2)
 <=2 sqrt(m tau(b)).                                    (UL8)
```

## 4. High-low transfer with the universal constants

Let a loop `(v_j)` in `F_(N,m)(a)` be `delta`-close in Hilbert-sum metric
to `(v_(0,j))`.  Write `v_j=s_ja^(1/2)` and put

```text
epsilon_0=min(epsilon,1),       eta=(epsilon_0/12)^2,
p_h=1_[eta,1](a),               p_l=supp(a)-p_h.
```

On the high part,

```text
(sum_j||s_jp_h-s_(0,j)p_h||_2^2)^(1/2)
 <=eta^(-1/2)delta.                                    (UL9)
```

The combined high source has strict complement because
`m tau(supp(a))<=1-gamma`.  Apply the matrix or diffuse Stiefel theorem,
with output radius `epsilon_0/3`.  By Step 1 choose its filling with a
unitary lift.  The high filling exists provided

```text
delta <=sqrt(eta) rho_St(epsilon_0/3)
       =epsilon_0^3/276480.                            (UL10)
```

Its range complement is therefore unitarily trivialized.  Step 3 extends
the boundary low tuple in that moving complement.  Recombine high and low
weighted pieces.  The high contribution costs at most `epsilon_0/3`, while
`(UL8)` and `m tau(ap_l)<=eta m tau(p_l)<=eta` bound the low contribution
by

```text
2sqrt(eta)=epsilon_0/6.                                (UL11)
```

The two source pieces are orthogonal in `L^2`; in particular their sum is
less than `epsilon`.  This proves the claim with `(UL10)`.  The argument
covers `p_h=0`, `p_l=0`, zero spectral bands, and both matrix and diffuse
corners.  In a matrix corner, strict positive complementary trace means
positive complementary rank, exactly the hypothesis used in Step 1.
Finally, global simple connectivity is a direct application of Step 3:
take `b=a`, `eta=1`, `g(y)=1`, and `U(y)=1`.  The strict inequality
`m tau(supp(a))<1` supplies `(UL3)` at every finite stage, and the bands
cover `(0,1]`.  Hence Step 3 fills the original arbitrary weighted loop
with the exact prescribed boundary.  (For `a=0` the fibre is a point.)
This proves the global assertion without making a high/low cut or invoking
the quantitative part of Step 4.
