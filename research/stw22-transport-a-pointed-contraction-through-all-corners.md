---
rg: 2
id: stw22-transport-a-pointed-contraction-through-all-corners
kind: route
title: Transport one pointed Jekel contraction through all corners and iterate Michael lifting
target: stw22-full-fundamental-group-weighted-copy-all-sphere-fillings
requires:
  - stw22-all-finite-factor-weighted-copy-uniform-loop-fillings
artifacts:
  - research/artifacts/stw22-full-fundamental-group-all-degree-audit-2026-08-30.md
---

All topology and estimates below use the `2`-norm.  Fix a Jekel
contraction of `U(N)` and point it as in
`stw22-pointed-jekel-contraction-fills-fixed-factor-s2`:

```text
K_N:U(N) times [0,1]->U(N),
K_N(u,0)=u,       K_N(u,1)=1,       K_N(1,t)=1.        (FG1)
```

For every `eta>0`, compactness of `{1} times [0,1]` gives
`lambda_N(eta)>0` such that

```text
||u-1||_(2,N)<lambda_N(eta)
 => sup_t||K_N(u,t)-1||_(2,N)<eta.                    (FG2)
```

No uniformity in `N` is asserted.

## 1. One modulus for every corner unitary group and every degree

Let `r in N` have trace `t>0`.  Choose a trace-preserving isomorphism

```text
theta_r:(rNr,tau/t)->(N,tau),                         (FG3)
```

which exists by the full-fundamental-group hypothesis.  Transport `(FG1)`
through `theta_r`.  This contracts `U(rNr)` to `r`, fixes `r` throughout,
and is continuous in the normalized corner `2`-norm.  The choice of
`theta_r` need not depend continuously on `r`: it is used to fill one map
inside one fixed corner.

Here is a modulus independent of `r` and of the sphere degree.  Put

```text
epsilon_0=min(epsilon,1),
c=(epsilon_0/4)^2,
sigma_N(epsilon)=(epsilon_0/4)lambda_N(epsilon_0/2).   (FG4)
```

If `t<c`, the ambient diameter of `U(rNr)` is at most
`2sqrt(t)<epsilon_0/2`; its transported contraction fills every sphere
inside that ball.  If `t>=c`, translate a sphere by one of its points.  An
ambient `sigma_N(epsilon)`-ball becomes, after `(FG3)`, a normalized ball
of radius at most `lambda_N(epsilon_0/2)`.  Equations `(FG1)--(FG2)` fill
the translated sphere in normalized radius `epsilon_0/2`, hence in ambient
radius at most `epsilon_0/2`.  Left translation returns the filling.

Thus the family

```text
{U(rNr):r a projection in N}
```

is uniformly equi-`LC^j` for every finite `j`, with the same local modulus
`(FG4)` for all `j`; every value is contractible.  The zero corner is a
singleton.  For Michael's ambient-centred convention, halve the output
radius and input radius in the usual way.

## 2. All-degree Stiefel lifting

Fix a source frame `v_0` with final projection `q_0`.  The conjugator
multifunction for a variable frame `v` is

```text
G(v_0,v)={u in U(N):uv_0=v}
         =u_v(q_0+U((1-q_0)N(1-q_0))).                (FG5)
```

It is nonempty, closed and lower semicontinuous, and the established polar
correction gives

```text
dist(1,G(v_0,v))<13||v-v_0||_2.                       (FG6)
```

By Step 1 the values in `(FG5)` are uniformly equi-`LC^j` and globally
`j`-connected for every finite `j`.  For a fixed `k>=1`, Gutev's
controlled Michael theorem with `n=k-1` applies over `S^k`.  Equations
`(FG4)--(FG6)` give a number `Gamma_(N,k)(s)>0`, independent of the source
projection, such that every sufficiently small Stiefel `S^k` has a lift

```text
u:S^k->U(N),       uv_0=v,       sup||u-1||_2<s.       (FG7)
```

Choose `s=lambda_N(epsilon)` and cone `(FG7)` through `(FG1)`.  Projecting
the cone by multiplication with `v_0` gives a small Stiefel filling and
retains a unitary lift on the whole ball.  The uncontrolled Michael theorem
applied to `(FG5)`, followed by Jekel contraction, fills every Stiefel
`S^k`.  The case `k=0` is the established direct polar path argument.

For an `m`-frame with common source `p`, fix a reference frame
`s_1,...,s_m`, put `Q=sum_j s_js_j^*`, and use the isometry

```text
(t_1,...,t_m) |-> sum_j t_js_j^* in St_N(Q).          (FG8)
```

Thus no matrix amplification, and no modulus depending on `m`, occurs.

## 3. Arbitrary positive weights

Fix `k` and cut `a` at a small scalar `eta`.  The high polar `m`-frame is
continuous and its Hilbert-sum displacement is at most
`eta^(-1/2)` times the weighted displacement.  Step 2 fills it with a
unitary lift over `B^(k+1)`.

For the low part, use the unitary-lifted band recursion from
`stw22-unitary-lifted-spectral-band-recursion-proof`, with `S^1,B^2`
replaced by `S^k,B^(k+1)`.  At each finite stage the moving complement is
unitarily trivialized.  After conjugating to its fixed reference corner,
the next bounded band is one Stiefel `S^k`; the uncontrolled lifting in
Step 2 fills it with a unitary and explicitly trivializes the next
complement.  Strict total support slack guarantees a nonzero complement at
every finite stage.

The orthogonal weighted band sums converge uniformly in `2`-norm.  They
are uniformly operator bounded, hence their limits lie in `N`; `L^1`
continuity of products preserves the exact sources and range
orthogonality.  The low displacement is at most `2sqrt(eta)`.  Choosing
`eta` from the requested output radius and then the high input radius gives
`rho_(N,k)(epsilon)`, independent of `m,a,gamma`.  Running the same band
recursion directly with weight `a` and constant initial complement `1`
fills an arbitrary weighted `S^k`, proving global `k`-connectivity.

## 4. Why the argument stops for a general fixed factor

For an arbitrary fixed `N`, `(FG1)--(FG2)` control only `U(N)`.  Lifting an
`S^k` through `(FG5)` requires a local filling modulus through degree
`k-1` simultaneously for every complement corner.  The universal diffuse
Stiefel theorem supplies this through degree one, which is exactly why the
unconditional fixed-factor result reaches `S^2`.  A collection of separate
Jekel contractions of the corners supplies global contractibility but no
positive infimum of their local moduli.  Therefore the pointed-Jekel/Michael
mechanism alone does not justify `k>=3` for a general fixed factor.  The
full-fundamental-group hypothesis repairs precisely this missing uniformity
by transporting the single contraction `(FG1)` to every normalized corner.
