---
rg: 2
id: non-hyperlinear-from-p3-lambda-exact-face-and-weak-ucp
kind: route
title: Weak ucp-stability of the lattice confines the p three HNN microstates to the Lambda-exact face, which the metaplectic flux closes
target: non-hyperlinear-group
requires:
  - kazhdan-subgroup-weak-ucp-exactifies-microstates
  - sl3-z-weakly-ucp-stable
  - lambda-exact-face-closes-at-p-three
---

Take the p = 3 pair

```text
Lambda = SL_3(Z) <= Gamma = SL_3(Z[1/3]),  a_1 = h = diag(3, 1, 1/3),
G_3 = < Gamma, t | [t, Lambda] = 1 >.                              (PU1)
```

`Lambda` has property (T) (higher-rank lattice), so
`kazhdan-subgroup-weak-ucp-exactifies-microstates` applies to the pair
`C = Lambda <= A = Gamma` as soon as `sl3-z-weakly-ucp-stable` holds.

Suppose `G_3` were hyperlinear, with hyperlinear approximation `phi_n`.
The theorem replaces it by `phi'_n : G_3 -> U(d'_n)` that is a genuine
representation on `Lambda` and whose letter `k_n = phi'_n(t)` commutes
exactly with `phi'_n(Lambda)`.  Every genuine finite-dimensional unitary
representation of `SL_3(Z)` factors through a congruence quotient
`SL_3(Z/N)` (Margulis superrigidity gives finite image, the congruence
subgroup property makes every finite quotient congruence), so
`phi'_n|_Lambda` is a congruence representation at some level `N_n`:
the restriction `pi = [phi'_n|_Gamma]` to the matrix ultraproduct is a
regular-trace representation of `Gamma` whose `Lambda`-restriction is
`Lambda`-exact at levels `(N_n)`, and `k = [k_n] in pi(Lambda)' cap M`
with `tau(k pi(h) k^* pi(h)^*) = lim tr phi'_n([t, h]) = 0` because
`[t, h] != e` in `G_3` by Britton's lemma.  This is precisely an enemy of
the collapse `(RC3-p3)` with `Lambda`-exact microstates, which
`lambda-exact-face-closes-at-p-three` forbids at every level.
Contradiction; `G_3` is not hyperlinear.

The same three inputs make the coset Bernoulli wreath
`W_3 = C_2 wr_(Gamma/Lambda) Gamma` non-hyperlinear (wreath variant of
the exactification theorem, base lamp in place of `t`), the endpoint of
`nonhyperlinear-coset-wreath-from-p3-collapse` without its full-collapse
input.

**Position relative to the existing routes.**
`non-hyperlinear-from-p3-relative-commutant-collapse` needs the FULL
collapse `sl3-p3-pair-relative-commutant-collapse` (all microstates,
including the everywhere-inexact outliers of
`subgroup-exact-outliers-do-not-exist`'s complement) and no stability
hypothesis.  `non-hyperlinear-from-hnn-over-sln-z` needs flexible
HS-stability of the HOST lattice and a thin co-dense subgroup, and no
collapse.  This route sits between them: a stability hypothesis on the
SUBGROUP lattice in its weakest published form (weak ucp-stability,
strictly weaker than flexible HS-stability, Dogon arXiv:2211.10492), plus
only the `Lambda`-exact face of the collapse, which is the face the
arithmetic lane has already reduced to the metaplectic flux seams.  It is
NOT a shortcut around the face: the exactification theorem leaves the
`l^2(Gamma/Lambda)` leak intact inside the face, as
`no-published-unconditional-codense-stable-host` predicts for any ucp
mechanism.
