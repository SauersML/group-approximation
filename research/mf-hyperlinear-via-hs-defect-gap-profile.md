---
rg: 2
id: mf-hyperlinear-via-hs-defect-gap-profile
kind: route
title: Phase-cancel the intrinsic HS profile and tensor it to visibility
target: mf-implies-hyperlinear
requires:
  - hyperlinear-elementwise-visibility
  - mf-hs-defect-gap-profile
artifacts:
  - research/artifacts/weak-mf-hs-profile-audit-2026-08-30.md
---

## Why sufficient

Fix `g != 1` in the countable weak-MF group `G`, and take `phi_n`, `eta_n`
and `kappa_n` from `mf-hs-defect-gap-profile`.  Define a unitary table on
dimension `4d_n` by

```text
theta_n(x) = phi_n(x) directSum conjugate(phi_n(x))
             directSum 1_(d_n) directSum 1_(d_n).             (H1)
```

For a tested product `(a,b)`, write

```text
D_n(a,b) = phi_n(ab)^* phi_n(a) phi_n(b),
delta_n(a,b) = ||D_n(a,b)-1||_(2,norm).
```

The relative error unitary for `(H1)` has real normalized trace

```text
r_n(a,b) = (1+Re tr_(d_n)(D_n(a,b)))/2
           = 1-delta_n(a,b)^2/4,                              (H2)
```

which belongs to `[0,1]`.  Likewise

```text
tr_(4d_n)(theta_n(g))
 = (1+Re tr_(d_n)(phi_n(g)))/2
 = 1-kappa_n/2 in [0,1].                                      (H3)
```

Because `eta_n^2/kappa_n -> 0`, there are integers `L_n>=1` with

```text
L_n eta_n^2 -> 0,              L_n kappa_n -> infinity.       (H4)
```

For example, after discarding finitely many indices, one may take

```text
L_n = floor(1/(eta_n sqrt(kappa_n)))
```

when `eta_n>0`; if `eta_n=0`, take any `L_n` with
`L_n kappa_n -> infinity`.  Define

```text
Psi_n(x) = theta_n(x)^(tensor L_n).                            (H5)
```

For the tested product `(a,b)`, unitary invariance of normalized
Hilbert--Schmidt norm, multiplicativity of normalized trace under tensor
products, `(H2)`, and `1-t^L <= L(1-t)` for `0<=t<=1` give

```text
||Psi_n(a)Psi_n(b)-Psi_n(ab)||_(2,norm)^2
 = 2-2 r_n(a,b)^(L_n)
 <= 2 L_n(1-r_n(a,b))
 = (L_n/2) delta_n(a,b)^2
 <= (L_n/2) eta_n^2 -> 0.                                    (H6)
```

On the marked element, `(H3)` gives

```text
tr(Psi_n(g)) = (1-kappa_n/2)^(L_n)
              <= exp(-L_n kappa_n/2) -> 0.                    (H7)
```

Therefore `g` is tracially visible (indeed with trace tending to zero) in
normalized Hilbert--Schmidt models on exhausting windows.  Repeating the
construction separately for every `g != 1` and applying
`hyperlinear-elementwise-visibility` proves that `G` is hyperlinear.

## Exact gain over the existing rate route

The proof never uses the operator-norm bound `epsilon_n` after it ensures
that the original tables are legitimate weak-MF local models.  Relation
accumulation in `(H6)` is governed by the actual normalized
Hilbert--Schmidt errors `delta_n(a,b)`, not by their possibly very wasteful
upper bound `epsilon_n`.  Consequently this route has the sharp sufficient
input `eta_n^2/kappa_n -> 0`, which is invariant under identity padding.
