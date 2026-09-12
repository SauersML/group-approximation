---
rg: 2
id: moving-basin-blowup-needs-displacement-charge
kind: claim
title: A moving-basin tangent blow-up needs a new displacement-rank charge
distinct_from:
  bs14-thresholded-newton-needs-coordinate-basin: that says the tangent inverse starts only inside an operator-norm coordinate tube; this proves the proposed spectral-truncation bridge into that tube is circular and gives a fixed-degree scalar countermodel.
  fixed-core-passive-fiber-has-positive-basin: that gives a positive radius at every coordinate; this identifies exactly why those radii may collapse despite a uniform tangent gap at all exact zeros.
  sublinear-bs-block-surgery-is-invisible-to-relative-liftability: that proves the active block cut preserves the ultraproduct lifting class; this quantifies why truncating the remaining displacement requires positive-density rather than sublinear padding.
---

**ESTABLISHED FIREWALL.**  Let `X_n` be passive reflections over exact cores
`beta_n`, let `Z_(beta_n)` be the corresponding exact endpoint fibers, and
suppose

```text
dist_2(X_n,Z_(beta_n))>=eta>0.                          (MBB1)
```

For any choice `Y_n in Z_(beta_n)`, put `D_n=X_n-Y_n`.  Given
`0<tau<eta`, let

```text
Q_n=1_((tau,infinity))(|D_n|),          q_n=rank(Q_n). (MBB2)
```

Since `||D_n||<=2`,

```text
eta^2<=||D_n||_2^2
       <=tau^2+4 q_n/d_n,
q_n/d_n >=(eta^2-tau^2)/4.                            (MBB3)
```

Thus the operator-large part of the displacement from **every** exact
endpoint has positive density.  It cannot be discarded or padded by the
`o(d_n)` active budget.  The operator-small remainder has normalized HS
norm at most `tau`, so it cannot carry the fixed distance in `(MBB1)` and
cannot by itself yield a nonzero normalized tangent countervector.

Consequently the proposed contradiction has a missing implication.  The
active residual threshold controls the ranks of spectral projections of
the cubic residuals.  It gives no control on `q_n` in `(MBB2)`, which is a
spectral projection of displacement from an unknown exact endpoint.  To
turn `(MBB3)` into energy-charged padding one would need a new estimate of
the form

```text
inf_(Y in Z_beta) rank 1_((tau,infinity))(|X-Y|)/d
       <=C_tau L_beta(X),                               (MBB4)
```

or a comparable nonlinear error bound.  But `(MBB4)` already implies the
uniform moving-core endpoint basin: if `L_beta(X)->0`, remove the charged
high part and apply the uniform tangent theorem to the operator-small
remainder.  Hence using `(MBB4)` to prove relative liftability would be
circular unless it is established by genuinely new arithmetic input.

Uniform tangent gaps and uniformly bounded word-map derivatives do not
imply `(MBB4)`.  On `[0,1]`, consider the fixed-degree family

```text
f_e(t)=t((t-1)^2+e),                 e>0.              (MBB5)
```

Its exact zero set is `{0}`, `f_e'(0)=1+e>=1`, and all derivatives through
degree three are uniformly bounded.  Nevertheless

```text
f_e(1)=e->0,                  dist(1,{0})=1.            (MBB6)
```

Amplifying `t=1` as a scalar matrix makes the far displacement occupy full
normalized rank, exactly as `(MBB3)` predicts.  The limit has acquired a
new zero at `1`, but no coordinate zero approaches it.  This is the scalar
normal form of an exact ultraproduct homomorphism without coordinate lifts.

Therefore the fixed-core basin, regular-character split, sublinear active
cut, and uniform tangent gap do not by themselves prove adaptive moving-core
relative liftability.  The exact missing theorem is a global arithmetic
displacement charge such as `(MBB4)`, or directly the relative coordinate
lift it would imply.

DERIVATION
moving-basin-truncation-firewall-proof
