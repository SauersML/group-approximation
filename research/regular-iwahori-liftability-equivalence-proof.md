---
rg: 2
id: regular-iwahori-liftability-equivalence-proof
kind: route
title: Exactify the modular vertices and compare with exact global lifts
target: regular-iwahori-exactification-is-regular-branch-liftability
requires:
  - sl2-z-same-dimension-hs-stable
  - odd-congruence-iwahori-pairs-have-uniform-linear-repair
  - finite-dimensional-dual-of-sl2-z-inverse-two-is-odd-congruence
---

Assume regular relative congruence exactification, and let `phi_n` be a
regular microstate sequence of `Gamma`.  Restrict `phi_n` to the two modular
vertices.  By `sl2-z-same-dimension-hs-stable`, perturb each restriction in
the same dimension to exact representations

```text
pi_(n,+),pi_(n,-):SL_2(Z)->U(d_n).
```

The perturbation is `o(1)` on generators, so the Iwahori edge defect is still
`o(1)`.  It also does not change the induced ultraproduct representation;
in particular its character remains `delta_e`.  Relative congruence
exactification now gives odd-congruence vertex representations
`eta_(n,+),eta_(n,-)` at `o(1)` distance with edge defect `o(1)`.

Apply `odd-congruence-iwahori-pairs-have-uniform-linear-repair`.  Its level-
and dimension-independent constant perturbs the `eta` pair by `o(1)` to an
exactly compatible pair.  The latter is a genuine representation

```text
rho_n:Gamma->U(d_n)
```

at `o(1)` distance from `phi_n`.  This proves same-dimensional regular-
branch liftability.

Conversely, assume same-dimensional regular-branch liftability and start
with an exact vertex pair in property 1.  Since the only nonzero defining
defects are the finitely many edge-identification defects, the pair itself
is a regular microstate sequence of `Gamma`.  Liftability gives genuine
representations `rho_n:Gamma->U(d_n)` at `o(1)` distance.  By
`finite-dimensional-dual-of-sl2-z-inverse-two-is-odd-congruence`, every
`rho_n` factors through an odd congruence quotient.  Its two vertex
restrictions are therefore the required congruence pair; their edge defect
is zero.  This proves relative congruence exactification.

