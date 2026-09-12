---
rg: 2
id: finite-left-inverse-identity-does-not-force-balance
kind: claim
title: The finite left-inverse identity of an injective automaton does not imply its local rule is balanced
distinct_from:
  every-injective-ca-has-uniform-single-site-output-law: that is the open goal-equivalent statement that injective automata over a fixed group are balanced; this is a negative structural fact, that the finite decoder identity alone is insufficient, witnessed over a nonunimodular group.
  strict-automata-give-injective-ca-with-skewed-site-marginals: that constructs a non-balanced injective automaton from a strict one; this uses that construction over the tree group to refute the finite-identity route to balance.
artifacts:
  - research/artifacts/injective-balance-needs-inf-and-nonlocal-2026-09-12.md
---

**ESTABLISHED.** There are a group `Gamma`, a finite alphabet `B`, and an injective cellular automaton
`kappa : B^Gamma -> B^Gamma` such that

- `kappa` admits a finite-memory left inverse: there are a finite `E subset Gamma` with `e in E` and a
  rule `rho` with `rho( ( mu_kappa(w|_{eta M}) )_{eta in E} ) = w(e)` for **every** pattern
  `w in B^{EM}` (`M` the memory of `kappa`); and
- the local rule `mu_kappa` is **not balanced**: the law of `kappa(x)(e)` under the uniform product
  measure is non-uniform on `B`.

So the finite left-inverse identity does not imply balance. Any proof of
`every-injective-ca-has-uniform-single-site-output-law` (equivalently, that an injective automaton is
balanced) must use a nonlocal, group-level hypothesis; a finite counting argument from the decoder
identity alone cannot succeed.

Witness: `Gamma` is the end-fixing tree automorphism group, which carries a strict automaton
(`end-fixing-tree-symmetries-carry-strict-automata`); the amplification of that strict automaton
(`strict-automata-give-injective-ca-with-skewed-site-marginals`) is an injective `kappa` with
non-uniform one-site law, and injectivity gives the finite decoder identity by Curtis-Hedlund-Lyndon
for the inverse. Full argument: `finite-left-inverse-identity-does-not-force-balance-proof`.

This complements the entropy analysis in the artifact: the conjugacy-entropy proof of
`injective => balanced` factors exactly through maximal Bernoulli Rokhlin entropy
(`bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups`), so neither the finite nor the entropy route
avoids a nonlocal input.
