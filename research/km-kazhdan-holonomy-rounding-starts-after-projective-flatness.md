---
rg: 2
id: km-kazhdan-holonomy-rounding-starts-after-projective-flatness
kind: claim
title: Kac-Moody Kazhdan holonomy rounding starts only after projective flatness has killed the regular core
distinct_from:
  kazhdan-projection-rounding: that rounds a projection for an already exact group representation; this treats a unitary holonomy coming from the Curtis-Tits free presentation and identifies exactly when the required adjoint representation descends to the Kac-Moody quotient.
  fixed-finite-label-km-holonomy-is-scalar-or-gapped: that treats a fixed Schur label factor tensored with arbitrary multiplicity; this applies to the full growing microstate matrices and shows why property T cannot be invoked before projective relator exactification.
  relative-three-chart-correction-is-km-regular-stability: that identifies exact simultaneous chart correction with terminal regular stability; this isolates the strongest dimension-free commutant rounding available from property T and proves that its exact-action hypothesis is already terminal on the regular branch.
---

Let `Gamma=<S|R>` be a property-`(T)` group with Kazhdan constant `kappa>0`
for `S`, let `F=F(S)`, and let `rho:F->U(D)` be any exact free-group
representation. The adjoint maps

```text
Ad rho(s):L^2(M_D)->L^2(M_D)                           (KKH1)
```

factor through an exact unitary representation of `Gamma` if and only if

```text
rho(r) in T I_D                    for every r in R.   (KKH2)
```

Under `(KKH2)`, every unitary `W in U(D)` has a unitary

```text
V in rho(F)' cap M_D
```

such that

```text
||W-V||_2
 <=sqrt(2) kappa^(-1) max_(s in S)||[W,rho(s)]||_2.   (KKH3)
```

Thus `(KKH3)` is a qualitative, dimension-free global holonomy lemma: an
almost-central multiplicity cycle is gauge-equivalent to a global commutant
unitary once the Curtis--Tits connection is exactly projectively flat.

For the infinite finitely generated simple Kac--Moody lattice in
`compact-hyperbolic-km-regular-microstates-synchronize`, however, `(KKH2)`
forces the projective representation `s |-> [rho(s)] in PU(D)` to be
trivial. Hence every `rho(s)` is scalar. Its restriction to every nontrivial
finite rank-one or rank-two parahoric has no regular summand. Consequently
the exact hypothesis under which property `(T)` synchronizes the holonomy
has already annihilated the positive regular core that the argument is meant
to preserve.

In the actual microstate sequence one has only `rho(r)=I+o_2(1)`. Then
`Ad rho` is merely an approximate representation of `Gamma`, and the
Kazhdan inequality cannot be applied to it. Upgrading these near-scalar
Curtis--Tits relators to `(KKH2)` while preserving regular mass is precisely
projective normalized-HS stability of this presentation, not a consequence
of property `(T)` or of the local finite-subgroup spectral gaps.

This gives the sharp scope of every property-`(T)`/relative-commutant attack:
it may finish synchronization after projective flatness, but it cannot
manufacture projective flatness from the native approximate face relations.
Any smaller positive lemma must use additional finite-matrix structure that
controls the relator scalarization itself.
---
