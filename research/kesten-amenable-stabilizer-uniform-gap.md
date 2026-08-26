---
rg: 2
id: kesten-amenable-stabilizer-uniform-gap
kind: claim
title: One Kesten constant is a spectral gap on every coset space of an amenable subgroup
artifacts:
  - research/artifacts/atomic-schreier-lamp-collapse-audit-2026-08-26.md
distinct_from:
  stabilizer-orbit-commutators-have-a-kesten-chart-carrier: that needs the Kesten spectral measure of a free carrier to be atomless so a quantile exists; this needs only the numerical spectral radius of the ambient walk and says nothing about spectral measures.
  no-exact-quasi-regular-leak: that forbids one exact quasi-regular coefficient profile inside a matrix ultraproduct over an arithmetic pair; this is a classical Dirichlet-form gap for genuine quasi-regular representations and involves no ultraproduct.
  no-spherical-leak-in-matrix-ultraproducts: that excludes leaks of every commutant mass in an ultraproduct; this is a positive statement about Schreier graphs of a nonamenable group.
---

Let `A` be a countable group with a finite symmetric generating set `S`, let

```text
rho = rho(A,S) = || (1/|S|) sum over s in S of lambda_A(s) ||  < 1
```

be its Kesten spectral radius, which is `< 1` exactly when `A` is nonamenable.
Put

```text
kappa = kappa(A,S) = 2 |S| (1 - rho) > 0.                          (KAG1)
```

Then for **every** amenable subgroup `H <= A` and every real `f in l^2(A/H)`,

```text
sum over s in S of || f - s f ||_2^2 >= kappa || f ||_2^2.         (KAG2)
```

The constant depends only on `(A,S)`, not on `H`.  Consequently a group all of
whose proper subgroups are amenable -- a Tarski monster is the model example --
supplies **one** gap constant valid simultaneously on every orbit of every
action with proper point stabilizers.

**What this discharges.**  `infinite-schreier-pvm-transport-kills-finite-mark`
assumes a positive bottom gap `(ISP1)` for the normalized adjacency operator of
the orbit graph and derives the mass collapse from it.  `(KAG2)` supplies that
hypothesis, with `gamma = 1 - rho(A,S)` and no case analysis, for every orbit
whose point stabilizer is amenable -- so an actor with all proper subgroups
amenable needs no per-orbit expansion argument at all.

This is the ingredient that plays the role property (T) plays elsewhere in the
program, and it is strictly weaker: it constrains only quasi-regular
representations, not all unitary representations, so it can amplify but it
cannot round.
