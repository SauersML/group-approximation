---
rg: 2
id: stw22-pointed-jekel-contraction-fills-fixed-factor-s2
kind: route
title: Lift two-spheres through uniformly loop-connected conjugator fibres and apply a pointed Jekel contraction
target: stw22-fixed-factor-weighted-copy-uniform-s2-fillings
requires:
  - stw22-diffuse-stiefel-uniform-loop-fillings
  - stw22-all-finite-factor-weighted-copy-uniform-loop-fillings
artifacts:
  - research/artifacts/stw22-fixed-factor-s2-filling-audit-2026-08-30.md
---

All topology is the `2`-norm topology.  We first treat projection-weight
Stiefel spaces, retaining a unitary lift of every filling, and then run the
unitary-lifted spectral-band recursion.

## 1. Corner unitary groups are uniformly equi-LC1

Let `r in N` have trace `t>0`, and put the normalized trace on `rNr`.
The diffuse Stiefel loop theorem applied inside `rNr` with source equal to
its unit says that `U(rNr)` has the normalized quadratic loop modulus

```text
rho_St(epsilon)=min(epsilon,1)^2/2560.
```

After converting back to the ambient trace, one universal, deliberately
conservative modulus is

```text
sigma(epsilon)=min(epsilon,1)^2/10240.                 (S2-1)
```

Indeed, if `2sqrt(t)<=epsilon/2`, the entire corner unitary group has
ambient diameter at most `epsilon/2` and Jekel contractibility fills any
loop.  Otherwise apply the normalized theorem with output radius
`min(epsilon/(2sqrt(t)),1)`.  Multiplication by `sqrt(t)` shows that the
ambient input radius in both cases is at least `(S2-1)`, and the output
radius is at most `epsilon/2`.

Consequently the conjugator fibres

```text
G(v_0,v)={u in U(N):uv_0=v}
```

form a uniformly equi-`LC^1` family, independent of all source and range
traces.  Each is a left coset of

```text
q_0+U((1-q_0)N(1-q_0)),       q_0=v_0v_0^*,           (S2-2)
```

and left translation is an ambient `2`-isometry.  The zero-complement case
is a singleton.  Every value is simply connected (indeed contractible) by
Jekel's theorem.  The pointwise `13`-estimate and lower semicontinuity from
`stw22-lift-and-contract-small-stiefel-loops-proof` use only finite-factor
polar decomposition and remain valid in `N`:

```text
dist(1,G(v_0,v))<13||v-v_0||_2.                       (S2-3)
```

For the ambient-centred form of equi-`LC^1`, halve the output radius and
the input modulus: a loop in `G intersect B(c,delta)` lies in the
`2delta`-ball about any one of its points, and a filling near that point
stays near `c`.  This adjustment is universal and is absorbed into the
control function below.

## 2. Controlled two-sphere lifts

Apply Gutev's controlled Michael theorem with `n=1` to `(S2-2)`.  By
`(S2-1)`, its control number depends only on the requested output radius;
write it as `Gamma_2(s)>0`.  Equations `(S2-3)` then imply:

```text
sup_z||v(z)-v_0||_2<Gamma_2(s)/13
```

for a map `v:S^2->St_N(p)` guarantees a continuous lift

```text
u:S^2->U(N),       u(z)v_0=v(z),       sup_z||u(z)-1||_2<s.   (S2-4)
```

The uncontrolled Michael theorem gives a unitary lift for every, not
necessarily small, two-sphere: the values `(S2-2)` are nonempty, closed,
simply connected and equi-`LC^1`.  This observation will be used for the
low spectral bands.

## 3. A fixed factor supplies the missing local contraction modulus

Choose a Jekel contraction

```text
H_N:U(N) times [0,1]->U(N),       H_N(u,0)=u,
H_N(u,1)=1.
```

Replace it by

```text
K_N(u,t)=H_N(u,t)H_N(1,t)^*.
```

Then `K_N(1,t)=1` for all `t`.  Joint continuity and compactness of
`{1} times [0,1]` imply that for every `epsilon>0` there is
`lambda_N(epsilon)>0` such that

```text
||u-1||_2<lambda_N(epsilon)
 => sup_t||K_N(u,t)-1||_2<epsilon.                    (S2-5)
```

Take `s=lambda_N(epsilon)` in `(S2-4)` and cone the lifted sphere by
`K_N(u(z),t)v_0`.  This is a filling in the Stiefel fibre, it comes with
the unitary lift `K_N(u(z),t)`, and `(S2-5)` keeps it in the desired ball.
Thus all Stiefel spaces in the fixed `N` have one two-sphere modulus

```text
rho_(N,St)(epsilon)=Gamma_2(lambda_N(epsilon))/13,     (S2-6)
```

independent of the source projection.  The uncontrolled lift followed by
the same contraction also proves that every Stiefel space is `2`-connected.

## 4. Relative spectral bands over a three-ball

The unitary-lifted recursion in
`stw22-unitary-lifted-spectral-band-recursion-proof` is dimension-free once
the boundary frame in a fixed corner has a unitary lift and filling.  For an
`S^2` boundary, Step 2 supplies precisely that lift in every nonzero corner
of `N`; Jekel contracts it over `B^3`.  If the current complement is

```text
g(y)=U(y)g_0U(y)^*,
```

conjugate the next bounded spectral-band frame into `g_0Ng_0`, fill its
combined Stiefel sphere with a unitary `W:B^3->U(g_0Ng_0)`, and update the
trivialization to `U(W+1-g_0)`.  The new complement is exactly

```text
U W (g_0-Q) W^* U^*.
```

Strict final support slack makes `Q<g_0` at every finite stage.  The
orthogonal weighted sums converge uniformly in `2`-norm exactly as in the
loop proof; boundedness puts their limits in `N`, and `L^1` product
continuity preserves sources, range orthogonality, and the boundary.

## 5. Quantitative high-low transfer

Put

```text
epsilon_0=min(epsilon,1),       eta=(epsilon_0/12)^2.
```

Cut the weight at `eta`.  The high polar `m`-frame is an `S^2` in one
Stiefel space and is at most `eta^(-1/2)` times the weighted input radius
from its base point.  Fill it, with its unitary lift, using `(S2-6)` at
output radius `epsilon_0/3`.  Step 4 fills all low bands in the moving
complement.  Their total Hilbert-sum displacement is at most
`2sqrt(eta)=epsilon_0/6`.  Hence one valid modulus is

```text
rho_N(epsilon)=sqrt(eta) rho_(N,St)(epsilon_0/3).      (S2-7)
```

It is independent of `m,a,gamma`.  Applying Step 4 directly with `b=a`
and constant complement `1` fills an arbitrary weighted two-sphere, so the
fibres are globally `2`-connected.
