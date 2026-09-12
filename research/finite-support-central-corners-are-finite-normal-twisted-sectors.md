---
rg: 2
id: finite-support-central-corners-are-finite-normal-twisted-sectors
kind: claim
title: Every finite-support central group-algebra corner is a finite sum of finite-normal twisted sectors
distinct_from:
  finite-normalizer-star-no-go: that computes a Plancherel countermodel for one finite packet and its normalizers; this is an intrinsic classification of all finite-support central selectors, independent of a proposed swap chart.
  twisted-factor-existence-is-equivalent-to-nonhyperlinearity: that is the goal-equivalent existence gate for one non-CE twisted factor; this proves that algebraic central-corner promotion cannot evade that gate by using an apparently infinite selector.
artifacts:
  - research/artifacts/finite-support-central-corner-collapse-2026-08-21.md
---

Let `Gamma` be a countable group and let

```text
q=q^*=q^2 in Z(C[Gamma]).                              (FSC1)
```

There is a finite normal subgroup `K normal Gamma` such that

```text
q in C[K].                                             (FSC2)
```

Consequently `q` is a sum of `Gamma`-orbit idempotents in `Irr(K)`.  If
`O` is one selected orbit, `rho in O`, `Gamma_rho` is its inertia subgroup,
and `d=dim(rho)`, then for a finite-valued scalar cocycle `omega_rho`,

```text
q_O C*(Gamma) q_O
 ~= M_(|O| d)(C) tensor C*_(omega_rho)(Gamma_rho/K).   (FSC3)
```

The normalized canonical trace on the summand is the matrix trace tensor
the twisted regular trace.  Therefore

```text
q C*(Gamma) q
 ~= direct_sum_(selected O)
       M_(|O| d_rho)(C) tensor
       C*_(omega_rho)(Gamma_rho/K).                    (FSC4)
```

In particular, a central group-algebra projection cannot be an
infinite-character or diffuse common-corner selector.  Any non-CE trace
promotion through such a corner has already produced a non-CE finite-phase
twisted group factor on one summand, the existing goal-equivalent gate.

The proof is in
`research/artifacts/finite-support-central-corner-collapse-2026-08-21.md`.
