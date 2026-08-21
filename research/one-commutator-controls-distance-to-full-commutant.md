---
rg: 2
id: one-commutator-controls-distance-to-full-commutant
kind: claim
title: For subgroup-central vectors the single expanding commutator controls the distance to the full commutant
distinct_from:
  hecke-averaging-realizes-commutant-expectation: that iterates the lazy average to realize the expectation in the limit; this is its Poincare form at ONE application, sharpened by the observation that all coset words share the same h-displacement, so a single commutator appears on the right.
  projective-commutant-transfer-for-arithmetic-pair: that conjectures a transfer inequality for approximate representations with a dimension-free modulus; this proves the exactly-central, exact-representation-free case in every finite tracial algebra, with the explicit constant 1/(4 delta_0) — the tracial-limit shadow of the measured PRT1 modulus.
---

Let `n >= 3`, `Gamma = SL_n(Z[1/p])`, `Lambda = SL_n(Z)`,
`h = gamma_0 = diag(p, 1, ..., 1, p^(-1))`, `(M, tau)` any von
Neumann algebra with faithful normal trace, `pi : Gamma -> U(M)` any
unitary representation.  Let `xi in L^2(M)` be ANY exactly
`Lambda`-central vector (`Ad pi(lambda) xi = xi` for all `lambda`),
and let `E` be the orthogonal projection onto
`L^2(pi(Gamma)' cap M)`.  Then

```text
|| Ad pi(h) xi - xi ||_2^2  >=  4 delta_0 || xi - E(xi) ||_2^2,  (OC1)
```

with the same constant `delta_0 = delta_0(n, p) = epsilon_0^2 / (4L)`
as in `hecke-averaging-realizes-commutant-expectation`.  For a
unitary `k in pi(Lambda)' cap M` this reads

```text
|| [k, pi(h)] ||_2^2  >=  4 delta_0 . dist_2( k, pi(Gamma)' cap M )^2.
```

Consequences.

- **The single-commutation form of the collapse acquires a modulus.**
  `sl3-pair-relative-commutant-route` reduced `(RC3)` to `[k, pi(h)]
  = 0` for `Lambda`-central `k`; `(OC1)` shows this reduction is
  Lipschitz-stable on the exactly-central variety: there is NO regime
  of `Lambda`-central witnesses with tiny-but-nonzero `h`-commutator
  sitting far from the full commutant.  Any enemy must pay the
  `h`-commutator at full scale (`>= 4 delta_0` for the exact
  quasi-regular profile, where `E(k) = 0`), i.e. the leak is visible
  at the FIRST Hecke shell with a proven constant.
- **Tracial shadow of the measured PRT1 modulus.**  The probe of
  `projective-commutant-transfer-for-arithmetic-pair` measures a
  linear transfer modulus of the order of the Hecke shell size on
  exact quotients; `(OC1)` is the statement that in the tracial limit
  the exactly-central case of such a transfer HOLDS with constant
  `1/(4 delta_0)`, `delta_0 = epsilon_0^2/(4L)` — connecting the
  measured constant to the Kazhdan constant of the completion and the
  shell size `L = p(p+1)(p^2+p+1)`.
- **What it does not do.**  `(OC1)` compares an exactly
  `Lambda`-central vector to the full commutant; it does not correct
  approximately central vectors (that quantifier gap is the open
  transfer claim), and it does not force `[k, pi(h)] = 0` — that
  remains exactly the collapse.  The audit's residue is unchanged but
  is now pinched between `(OC1)` (exact side) and the measured
  finite-level modulus (approximate side): the enemy lives only in
  the wedge where exact centrality degrades to approximate centrality
  faster than the transfer constant degrades.
