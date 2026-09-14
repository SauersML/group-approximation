---
rg: 2
id: finite-left-inverse-identity-does-not-force-balance-proof
kind: route
title: Amplify the tree's strict automaton to an injective non-balanced automaton with a finite decoder
target: finite-left-inverse-identity-does-not-force-balance
requires:
  - end-fixing-tree-symmetries-carry-strict-automata
  - strict-automata-give-injective-ca-with-skewed-site-marginals
artifacts:
  - research/artifacts/injective-balance-needs-inf-and-nonlocal-2026-09-12.md
---

Let `Gamma` be the end-fixing tree automorphism group. By
`end-fixing-tree-symmetries-carry-strict-automata` there is a strict automaton `tau_0` over `Gamma`:
injective and not surjective.

By `strict-automata-give-injective-ca-with-skewed-site-marginals`, from `tau_0` one builds, for large
`k`, an injective automaton `kappa` on `(A^{k+1})^Gamma` whose single-site output law under the uniform
product measure has entropy strictly below `(k+1) log|A|`. A law of entropy below the maximum on the
alphabet `B = A^{k+1}` is non-uniform, so `mu_kappa` is not balanced. This is the second bullet.

For the first bullet: `kappa` is an injective continuous `Gamma`-equivariant self-map of the full shift
`B^Gamma`. Its image `Y = kappa(B^Gamma)` is compact and `Gamma`-invariant, and
`kappa^{-1} : Y -> B^Gamma` is continuous and `Gamma`-equivariant. By the Curtis-Hedlund-Lyndon
theorem for the inverse, valid over every group, `kappa^{-1}` has a finite memory `E ni e` and local
rule `rho`, so `rho` reads `kappa(x)` on `gE` and returns `x(g)`. Writing `kappa(x)(eta) = mu_kappa(x|_{eta M})`
and evaluating at `g = e`, we get `rho( ( mu_kappa(w|_{eta M}) )_{eta in E} ) = w(e)` for `w = x|_{EM}`.
As `x` ranges over the full shift, `x|_{EM}` ranges over all of `B^{EM}` (the full shift constrains no
finite window), so the identity holds for every `w in B^{EM}`. This is the first bullet.

Both bullets hold for the single automaton `kappa`, so the finite left-inverse identity is satisfied by a
non-balanced injective automaton. This proves the target.
