---
rg: 2
id: kazhdan-finite-sector-corner-mass-proof
kind: route
title: Project the finite corner in Hilbert-Schmidt space and locate every invariant compact operator
target: kazhdan-unitary-corners-require-finite-dimensional-mass
requires: []
artifacts:
  - research/artifacts/quadratic-curvature-flexible-dilation-2026-09-05.md
---

Put `P=WW^*` and `A_s=W^*Pi(s)W`. Expanding the squared
intertwining error gives

```text
||Pi(s)W-WU_s||_HS^2/d
 =2-2 Re tr_d(U_s^* A_s)
 <=2||U_s-A_s||_(2,d)<=2epsilon.
```

Since P and its unitary conjugate have the same finite rank,

```text
||Pi(s)P Pi(s)^*-P||_HS^2
 =2||(I-P)Pi(s)W||_HS^2<=4epsilon d.
```

The conjugation action on `HS(K)` is genuine. If E is its orthogonal
projection onto invariant vectors, property `(T)` yields

```text
||P-E(P)||_HS^2<=4epsilon d/kappa^2.                     (KFP1)
```

Every invariant Hilbert--Schmidt operator T is supported on `Q_fd K`
on both sides. Indeed, T commutes with Pi, as do its compact positive
operators `T^*T` and `TT^*`. Their nonzero spectral subspaces are
finite-dimensional and Pi-invariant. Their closed spans contain the
initial and final spaces of T. Consequently
`(I-Q_fd)T=T(I-Q_fd)=0`.

Apply this to `E(P)`. Multiplying `(KFP1)` on the left by `I-Q_fd`
and using contraction of the HS norm gives

```text
Tr(W^*(I-Q_fd)W)
 =Tr(P(I-Q_fd))
 =||(I-Q_fd)P||_HS^2
 <=||P-E(P)||_HS^2<=4epsilon d/kappa^2.
```

This proves `(KFM1)`. If `dim(Q_fd K)<=k`, then
`Tr(W^*Q_fd W)=Tr(PQ_fd)<=k`; rearranging `(KFM1)` gives `(KFM2)`.

For an infinite group, a regular multiple has no finite-rank invariant
projection. Translation invariance makes all diagonal blocks of such a
projection identical, while its finite trace is the sum of their
nonnegative traces over infinitely many group elements. Every diagonal
block must vanish, and positivity makes the whole projection zero.
Subrepresentations and direct sums therefore still have no
finite-dimensional subrepresentation. A unitary quotient is equivalent
to the orthogonal complement of its closed invariant kernel, so has
the same property.

For finite `H<=G`, realize `Ind_H^G sigma` as functions with
`f(gh)=sigma(h)^(-1)f(g)`, square-summable over `G/H`. Dividing the
function by `sqrt(|H|)` embeds it isometrically into
`ell^2(G) tensor H_sigma` and intertwines the left action. This proves
the finite-stabilizer assertion.

Finally no finite-dimensional representation sigma of an infinite
Kazhdan group is weakly contained in its regular representation. If it
were, `sigma tensor conjugate(sigma)` would be weakly contained in
`lambda_G tensor conjugate(sigma)`. Finite-dimensional tensoring
preserves weak containment. The unitary

```text
delta_g tensor v |-> delta_g tensor conjugate(sigma)(g^(-1))v
```

identifies the latter with a regular multiple. But
`sigma tensor conjugate(sigma)` contains the identity-operator invariant
vector. The trivial representation would then be weakly contained in
regular multiples, supplying almost invariant vectors there; property
`(T)` would give a nonzero invariant vector, impossible for infinite G.

A representation of `C*_r(G)` is weakly contained in the regular
representation, and so has `Q_fd=0`. The Stinespring representation of
a ucp map on `C*_r(G)` is such a representation. Applying `(KFM1)` to
its isometry gives `1<=4epsilon/kappa^2`, which is `(KFM3)`.
The argument makes no corresponding assertion about representations of
the full group algebra.
