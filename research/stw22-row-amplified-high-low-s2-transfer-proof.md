---
rg: 2
id: stw22-row-amplified-high-low-s2-transfer-proof
kind: route
title: Encode all weighted copies in one matrix row and fill the low spectrum relatively
target: stw22-diffuse-weighted-copy-uniform-s2-fillings
requires:
  - stw22-diffuse-stiefel-uniform-two-sphere-fillings
  - stw22-diffuse-relative-low-spectrum-three-ball-extension
  - stw22-all-finite-factor-weighted-copy-uniform-loop-fillings
artifacts:
  - research/artifacts/stw22-dim3-diffuse-bundle-breakthrough-2026-08-30.md
---

All tuple metrics below are Hilbert-sum `2`-metrics.

## 1. The rectangular row is an exact isometry

Put `M=M_m(N)`, give it the normalized trace
`tau_m=Tr_m tensor tau/m`, and set `e=e_11 tensor 1`. For a tuple `v`
write

```text
R(v)=sum_(j=1)^m e_1j tensor v_j in eM.                (W2-3)
```

Orthogonality of the range supports in (W2-1) implies `v_i^*v_j=0`
for `i!=j`, and hence

```text
R(v)^*R(v)=diag(a,...,a).                              (W2-4)
```

If `p` is a projection and `P=diag(p,...,p)`, then

```text
tau_m(P)=tau(p),              tau_m(e)=1/m.            (W2-5)
```

Under (W2-2), a reference frame `t in eMP` with `t^*t=P` exists. Put
`q_0=tt^*<=e`. The map `S |-> S t^*` is an isometry from

```text
{S in eM:S^*S=P}
```

onto `St_(eMe)(q_0)` when the corner `eMe` has its normalized trace.
Indeed

```text
||S-T||_(2,eMe)^2
 =m||S-T||_(2,M)^2
 =sum_j ||S_j-T_j||_(2,N)^2.                          (W2-6)
```

Thus the universal Stiefel two-sphere theorem applies to an `m`-frame
with no hidden `m`-dependent metric loss. Since `N` is II1, both `M` and
`eMe` are separable-predual II1 factors.

## 2. Fill the high row

Fix `epsilon>0`, put `epsilon_0=min(epsilon,1)` and

```text
eta=(epsilon_0/12)^2,
p_h=1_[eta,1](a),       p_l=1_(0,eta)(a),
a_h=ap_h,               b=ap_l.                       (W2-7)
```

For a boundary tuple `v(z)`, its high polar row is

```text
H(z)=R(v(z)a_h^(-1/2)p_h),       H(z)^*H(z)=P_h,       (W2-8)
```

where `P_h=diag(p_h,...,p_h)`. Functional calculus on the fixed
high band gives

```text
d_2(H(z),H(z_0))<=eta^(-1/2)d_2(v(z),v(z_0)).          (W2-9)
```

Let `rho_St,2` be the universal modulus in
`stw22-diffuse-stiefel-uniform-two-sphere-fillings` and take

```text
rho_W,2(epsilon)
 =sqrt(eta) rho_St,2(epsilon_0/3)/2.                  (W2-10)
```

Use the fixed reference frame `t` from Step 1: send the boundary row to
`H(z)t^*` in `eMe`, fill there, and convert the filling back by
`Y |-> Yt`. Thus (W2-6)--(W2-10) fill the high row by

```text
H:B^3->eM,       H^*H=P_h,                            (W2-11)
```

with its weighted high part within `epsilon_0/3` of the base weighted
high part. If `p_h=0`, take `H=0`.

## 3. Fill every low copy at once

On the boundary let

```text
X(z)=R(v(z)p_l),        B=diag(b,...,b).               (W2-12)
```

Then `X^*X=B` and, for `f= e-HH^*`, one has `fX=X`. Moreover

```text
tau_m(P_h)+tau_m(supp(B))
 =tau(p_h)+tau(p_l)=tau(supp(a))<1/m=tau_m(e).         (W2-13)
```

Apply `stw22-diffuse-relative-low-spectrum-three-ball-extension` inside
the single diffuse factor `M`. It gives an exact relative extension
`X:B^3->eM` satisfying (W2-12) and `fX=X`. This is not a componentwise
selection: the one matrix equation `X^*X=B` retains all cross-relations.
Writing `X=sum e_1j tensor X_j`, it says

```text
X_i^*X_j=delta_ij b,
HH^*X=0.                                               (W2-14)
```

The low theorem and (W2-5) give, relative to the base low row `X_0`,

```text
d_2((X_j(y))_j,(X_0,j)_j)
 =sqrt(m)||X(y)-X_0||_(2,M)
 <=2sqrt(m tau(b))
 <=2sqrt(eta m tau(p_l))<2sqrt(eta)=epsilon_0/6.       (W2-15)
```

Now write `H=sum e_1j tensor H_j` and define

```text
V_j(y)=H_j(y)a_h^(1/2)+X_j(y).                         (W2-16)
```

Equations (W2-11), (W2-14), and orthogonality of `p_h,p_l` show exactly
that `(V_j(y))` lies in `F_(N,m)(a)` and has the prescribed boundary.
The high and low estimates total less than `epsilon`, proving the local
modulus.

For an arbitrary weighted two-sphere, use global two-connectivity of the
high Stiefel space in Step 2 and then repeat Step 3 and the reconstruction (W2-16). This proves
global two-connectivity. Combining the new degree-two modulus with the
existing universal degree-zero and degree-one weighted-copy moduli gives
equi-`LC^2` in Michael's sense.

The strict inequality in (W2-13) is the only complement hypothesis. This
lifting proof is diffuse-only: matrix stabilizers obstruct this particular
unitary-lift route. No matrix-factor assertion is made.