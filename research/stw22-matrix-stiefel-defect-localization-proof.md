---
rg: 2
id: stw22-matrix-stiefel-defect-localization-proof
kind: route
title: Localize matrix-frame defects to small rank and fill the residual Stiefel bundle
target: stw22-matrix-weighted-copy-uniform-loop-fillings
requires: []
artifacts:
  - research/artifacts/stw22-matrix-weighted-loop-filling-audit-2026-08-30.md
---

All traces below are normalized. We first prove the projection-weight
statement and then transfer it to positive weights and arbitrary copy
number.

## 1. A controlled direct rotation

We use the following standard finite-dimensional lemma. If `x,y in M_n`
are partial isometries with the same initial projection and

```text
||x-y|| < kappa < 1/20,
```

then there is a unitary `U`, depending continuously on `(x,y)`, such that

```text
Ux=y,       ||U-1|| <= 10 kappa.                       (MD1)
```

Indeed, the final projections differ in norm by at most `2kappa`. The
canonical direct-rotation unitary, obtained as the polar part of

```text
yy^*xx^*+(1-yy^*)(1-xx^*),
```

maps the first final projection to the second and is within `4kappa` of
the identity. Inside the common final corner, correct the remaining phase;
that correction is within `5kappa` of the identity. Their product gives
`(MD1)` with the harmless constant `10`. The polar and corner-phase
formulas are continuous while `2kappa<1`.

Since `||U-1||<1/2`, the principal logarithm is continuous. The path

```text
U_t=exp(t log(U))
```

satisfies `||U_t-1||<=||U-1||` by scalar functional calculus.

## 2. The dimension-free matrix Stiefel estimate

Fix a proper projection `q in M_n`, of rank `k`, and a loop

```text
v:S^1 -> St_n(q),       sup_z ||v(z)-q||_2 < delta.    (MD2)
```

The case `k=0` is trivial. Put `A_z=v(z)-q`. Fix `kappa<1/20` and set

```text
K=floor(4n delta^2/kappa^2).
```

### The small-total-source case

If `k<2K`, then

```text
k/n < 8 delta^2/kappa^2.                              (MD3)
```

The complex Stiefel manifold

```text
St_n(q) ~= U(n)/U(n-k)=V_k(C^n)
```

is simply connected because `n-k>=1`: in the homotopy exact sequence, the
block inclusion `U(n-k)->U(n)` induces the identity `Z->Z` on fundamental
groups. Thus the loop fills, and every point of any filling satisfies

```text
||w-q||_2 <= ||w||_2+||q||_2
            =2sqrt(k/n)<4sqrt(2) delta/kappa.          (MD4)
```

### A continuous small-rank defect carrier

Assume now `k>=2K`. In fixed matrix size, `2`-norm continuity is equivalent
to operator-norm continuity. Uniform continuity gives a cyclic subdivision
of the circle with vertices `z_i` such that on the doubled interval about
`z_i`,

```text
||A_z-A_(z_i)|| < kappa/4.                             (MD5)
```

Let `p_i` be the spectral projection of `|A_(z_i)|` for
`(kappa/2,infinity)`. Chebyshev's inequality and `(MD2)` give

```text
rank(p_i) kappa^2/4 < n delta^2,
rank(p_i)<=K.                                          (MD6)
```

Enlarge `p_i` inside `q` to rank exactly `K`. This is possible because
`K<=k/2`. On the doubled interval in `(MD5)`,

```text
||A_z(q-p_i)|| < 3kappa/4.                             (MD7)
```

Put `L=2K`. Choose a rank-`L` projection `E_i` containing
`p_i join p_(i+1)`. Between the constant pieces `E_(i-1)` and `E_i`, make
the transition in a small interval about `z_i` through rank-`L` projections
which all contain `p_i`. Such a path exists because this space is the
complex Grassmannian of `(L-K)`-planes in the complement of `p_i`, and
`k-K>=L-K`. The doubled intervals in `(MD5)` ensure that the transition is
made where `(MD7)` holds. This constructs a continuous projection loop

```text
e_z<=q,       rank(e_z)=L,
||A_z(q-e_z)||<kappa.                                  (MD8)
```

This also covers the cyclic closing transition. If `K=0`, take `e_z=0`;
then `(MD6)` and `(MD5)` give `(MD8)` directly. Thus no eigenprojection is
asserted to vary continuously: only the enlarged rank-`L` carriers are
interpolated, and every interpolation retains one fixed local spectral
projection `p_i`.

### Remove the good part

Put `f_z=q-e_z`, `x_z=v(z)f_z`, and `y_z=f_z`. These partial isometries have
common initial projection `f_z`, and `(MD8)` says `||x_z-y_z||<kappa`.
Apply `(MD1)` continuously to obtain `U_zx_z=y_z`. The principal-log paths
give a homotopy

```text
H(z,t)=U_(z,t)v(z)
```

inside `St_n(q)`, from `v` to a loop

```text
v'(z)=f_z+w_z,
w_z^*w_z=e_z,       w_zw_z^* orthogonal to f_z.        (MD9)
```

Throughout this homotopy,

```text
||H(z,t)-q||_2 < delta+10kappa.                        (MD10)
```

### Fill the localized defect

Let `c=n-k>=1`. The pairs in `(MD9)` lie in a fibre bundle `Z_L` over the
complex Grassmannian `Gr_L(C^k)`. Over a projection `e`, the fibre consists
of isometries from its `L`-dimensional range into `(q-e)^perp`, which has
dimension `L+c`. Hence the fibre is `V_L(C^(L+c))`. The bundle is locally
trivial by the ordinary local trivializations of the tautological bundle
and its orthogonal complement.

Both base and fibre are simply connected. For the base this is the standard
fundamental-group computation for a complex Grassmannian. For the fibre,
the exact sequence of

```text
U(c) -> U(L+c) -> V_L(C^(L+c))
```

again uses that `U(c)->U(L+c)` induces the identity on `pi_1`, since `c>=1`.
The edge case `L=0` is a point. The homotopy exact sequence of `Z_L` now
gives `pi_1(Z_L)=0`.

Fill the loop `(e_z,w_z)` in `Z_L`, say by `(e_y,w_y)`, and put

```text
F(y)=q-e_y+w_y.
```

This fills `v'` inside `St_n(q)`. Since `F(y)-q` has right support `e_y`,

```text
||F(y)-q||_2 <=2sqrt(L/n)
 <=4sqrt(2) delta/kappa.                               (MD11)
```

The same computation includes the edge case `L=k`; then the base
Grassmannian is a point.

Combining `(MD4)`, `(MD10)`, and `(MD11)`, choose, for
`epsilon_0=min(epsilon,1)`,

```text
kappa=epsilon_0/40,
delta=epsilon_0^2/2560.
```

Then `kappa<1/20`, `delta+10kappa<epsilon`, and
`4sqrt(2)delta/kappa<epsilon`. This proves the Stiefel estimate for loops
based near `q`. For a ball about arbitrary `v_0 in St_n(q)`, extend the
partial isometry carrying `v_0` to `q` to a unitary and left-translate the
loop; left translation is an exact `2`-isometry.

## 3. Projection-copy tuples are exactly one Stiefel space

Let `p` be a projection and fix an exact base tuple `s_1,...,s_m`, with
common initial projection `p` and orthogonal ranges. Put

```text
q=sum_j s_js_j^*.
```

For another exact tuple `(t_j)`, define `V=sum_j t_js_j^*`. Then `V^*V=q`,
and conversely `t_j=Vs_j` recovers every exact tuple from a unique
`V in St_n(q)`. Orthogonality of the right supports gives the exact identity

```text
||V-V'||_2^2=sum_j||t_j-t'_j||_2^2.                   (MD12)
```

Thus replication number introduces no extra topology in the Hilbert-sum
metric.

## 4. High-low transfer to arbitrary positive weights

Let `a` satisfy the claim, let `p=supp(a)`, and let a loop
`v=(v_1,...,v_m)` in `F_(n,m)(a)` lie within `delta_w` of a base tuple
`v_0`. Write uniquely

```text
v_j=s_ja^(1/2),       v_(0,j)=s_(0,j)a^(1/2),
```

where the `s_j` and `s_(0,j)` are polar frames with initial projection `p`.
Fix

```text
epsilon_0=min(epsilon,1),
eta=(epsilon_0/12)^2,
p_h=1_[eta,1](a),       p_l=p-p_h.
```

On the high part,

```text
(sum_j||s_jp_h-s_(0,j)p_h||_2^2)^(1/2)
 <=eta^(-1/2) delta_w.                                 (MD13)
```

The total high range projection is proper because
`m tau(p_h)<=m tau(p)<=1-gamma`. Apply the Stiefel estimate, using `(MD12)`,
with output radius `epsilon_0/3`. It fills the high polar tuple by `S_j(y)`
inside that radius, provided

```text
delta_w <=sqrt(eta) rho_St(epsilon_0/3)
          =epsilon_0^3/276480.                         (MD14)
```

Let `f(y)=1-sum_j S_j(y)S_j(y)^*`. The projection bundle `f(y)C^n` over the
disk is trivial. On the boundary, the low polar tuple `(s_jp_l)` is a
continuous section of the bundle of `m` orthogonal copies of `p_l` inside
`f(y)`. Continuity causes no uniform problem: in one fixed matrix algebra
`a` has a strictly positive least eigenvalue on its support.

After trivializing `f`, the fixed fibre of this low-frame bundle is the
complex Stiefel manifold with total source dimension `m rank(p_l)` and
target dimension `n-m rank(p_h)`. Its complement dimension is
`n-m rank(p)>=1`; hence it is simply connected. The boundary low tuple
therefore extends over the disk, say to `T_j(y)`, while remaining orthogonal
to all high ranges.

Set

```text
W_j(y)=S_j(y)a^(1/2)p_h+T_j(y)a^(1/2)p_l.              (MD15)
```

This is an exact filling in `F_(n,m)(a)`. The high contribution is within
`epsilon_0/3` of the base tuple. Regardless of the low extension,

```text
sum_j||(T_j-s_(0,j))a^(1/2)p_l||_2^2
 <=4m tau(ap_l)
 <=4eta m tau(p_l)
 <=4eta.                                               (MD16)
```

Thus the low contribution is at most `2sqrt(eta)=epsilon_0/6`. Equations
`(MD13)--(MD16)` keep the whole filling inside the `epsilon`-ball and prove
the claimed cubic modulus.

## 5. Why the proof stops at diffuse factors

The finite-dimensional proof uses operator-norm continuity after fixing
`n` to obtain `(MD5)--(MD8)`. For a merely `2`-norm-continuous loop in a
`II_1` factor, refining parameter arcs does not give operator-norm control:
small high-spectrum projections may move through mutually orthogonal
directions. A diffuse extension would follow from a continuous
constant-trace projection loop `e_z` satisfying

```text
tau(e_z)=O(delta^2/kappa^2),
||(v(z)-q)(q-e_z)||<=kappa,
```

but this spectral-capture selection is not proved here. Pointwise
Chebyshev estimates do not supply its continuity.
