---
rg: 2
id: hyperlinear-elementwise-visibility-proof
kind: route
title: Geometric phase average and tensor assembly
target: hyperlinear-elementwise-visibility
requires: []
artifacts:
  - GroupApproximation/Sofic/Hyperlinear.lean
  - GroupApproximation/Sofic/NormTraceGap.lean
---

## Direct proof

Throughout, `tr_d` is the normalized trace, `||.||_(2,norm)` the normalized
Hilbert--Schmidt norm, and all maps are unitary-valued.  Two facts are used
repeatedly: `||uxv||_(2,norm)=||x||_(2,norm)` for unitary `u,v`, and
`||x tensor y||_(2,norm)=||x||_(2,norm)||y||_(2,norm)`, so that
`||x tensor 1||_(2,norm)=||x||_(2,norm)`.

### Necessity

Let `G` be hyperlinear and `g != 1`.  Given `F` and `delta`, apply
`HyperlinearModel` to `F'=F union {1,g}` with accuracy
`epsilon=min(delta^2,1/16)`; since that structure measures the *squared*
Hilbert--Schmidt defect, the defect in `||.||_(2,norm)` is at most
`sqrt(epsilon)<=delta`.  Then `hsDistSq(map g,map 1)>=2-epsilon` and
`||map 1-1||_(2,norm)^2<=epsilon` from the multiplicativity defect at
`(1,1)`, whence

```text
2-2 Re tr(map g)=||map g-1||_(2,norm)^2 >= 2-4 sqrt(epsilon),
```

so `Re tr(map g)<=2 sqrt(epsilon)<=1/2` once `epsilon<=1/16`.  Thus every
`g != 1` is tracially visible with `c_g=1/2`.

### Sufficiency, step 1: killing the phase

Let `g != 1` be tracially visible with constant `c=c_g`, let `F` be finite
and `eta>0`.  Put

```text
F'=F union F^(-1) union F^(-1)F union {1},
```

and let `phi:G->U(d)` be a model with defect `delta` on `F'` and
`Re tr_d(phi(g))<=1-c`.  Write `zeta=tr_d(phi(g))`, so `|zeta|<=1` and

```text
|1-zeta| >= 1-Re zeta >= c.                                   (V1)
```

Fix `m>=1` and define, on `C^(m d^m)`,

```text
Phi = directSum_(j=1)^m (phi^(tensor j) tensor 1_(d^(m-j))).   (V2)
```

All `m` blocks have the same dimension `d^m`, so the normalized trace of
`Phi` is the *unweighted* average of the block traces, and
`tr(phi^(tensor j))=zeta^j` gives the geometric sum

```text
|tr(Phi(g))| = |zeta| |1-zeta^m| / (m |1-zeta|) <= 2/(m c).    (V3)
```

For the defect, telescoping in a tensor power of unitaries,

```text
x^(tensor j) y^(tensor j)-w^(tensor j)
 = sum_(i<j) w^(tensor i) tensor (xy-w) tensor (xy)^(tensor (j-1-i)),
```

and each summand has normalized Hilbert--Schmidt norm `||xy-w||_(2,norm)`,
so each block of `(V2)` has defect at most `m delta` on `F'`; a direct sum
of equal-size blocks has normalized Hilbert--Schmidt norm the root mean
square of the block norms, hence

```text
||Phi(a)Phi(b)-Phi(ab)||_(2,norm) <= m delta   (a,b in F').    (V4)
```

Choosing `m=ceil(4/(c eta))` and then `delta=eta/m` gives a model `Phi_g`
with defect `<=eta` on `F'` and `|tr(Phi_g(g))|<=eta/2`.  Note `m` depends
only on `c_g` and `eta`, which is why `c_g` must not depend on `(F,delta)`.

### Sufficiency, step 2: assembling a finite set

Let `D={a^(-1)b : a != b in F}`, a finite subset of `G\{1}`.  For each
`g in D` take `Phi_g` from step 1 with accuracy `eta` on `F'`, and set

```text
Psi = tensor_(g in D) Phi_g.                                    (V5)
```

Traces multiply, so `|tr(Psi(h))| <= |tr(Phi_h(h))| <= eta/2` for every
`h in D` --- the tensor product, unlike a direct sum, never lets a summand
with trace near `1` dilute the visibility of another element.  Defects add:
by the same telescoping as in `(V4)`,
`||Psi(a)Psi(b)-Psi(ab)||_(2,norm) <= |D| eta` on `F'`.

### Sufficiency, step 3: separation in the repository convention

From the defect at `(1,1)` and unitarity, `||Psi(1)-1||_(2,norm)<=|D|eta`.
For `a != b` in `F`, `a^(-1)b in D` and, using the defect on `F'` twice,

```text
||Psi(a)^* Psi(b)-Psi(a^(-1)b)||_(2,norm) <= 3|D| eta,
```

so

```text
hsDistSq(Psi(a),Psi(b)) = 2-2 Re tr(Psi(a)^* Psi(b))
                        >= 2-2(eta/2)-6|D| eta.
```

Given `epsilon>0`, choose `eta=epsilon/(8|D|+8)`: then `Psi` is a
`HyperlinearModel` for `F` of accuracy `epsilon`, both for multiplicativity
and for the `2-epsilon` separation.  Since `F` and `epsilon` were arbitrary,
`G` is hyperlinear.  End proof.

## Remark

Step 1 is where the naive tensor-power boost fails: `tr(phi(g))` may be a
phase, and `zeta^m` can return to `1`.  That failure is formalized as
`NormTraceGap.phase_deviation_no_amplification`; the invariant tensor powers
do drive is `1-||normTrace u||`
(`NormTraceGap.norm_normTrace_tensorPow_le`), which is why the geometric
average over `zeta,...,zeta^m` --- not the single power `zeta^m` --- is the
right device.  Averaging `zeta,...,zeta^m` with
equal weights is what converts *any* trace deficit into a near-zero trace,
at the price of multiplying the defect by `m`.  In the normalized
Hilbert--Schmidt world that price is harmless because `delta` is free; in
the operator norm it is not, which is exactly the gap recorded in
`mf-implies-hyperlinear`.
