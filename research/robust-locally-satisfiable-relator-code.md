---
rg: 2
id: robust-locally-satisfiable-relator-code
kind: claim
title: A finite noncommutative relator code has constant tracial soundness and sparse local satisfiability
artifacts:
  - research/artifacts/nonhyperlinear-finite-moment-sparsification-2026-08-18.md
---

There exist free generators, a finite relator menu `S`, a finite short-word
test set `B`, constants

```text
delta > 0,
0 < eps < eps_plus,
alpha > 0,
```

a full-support probability distribution `mu` on `S`, an integer `m`, and a
presentation-preservation event `SC` for `m` independent samples from `mu`,
with the following properties.

1. **Robust finite-dimensional soundness.**  For every matrix size and every
   unitary generator tuple whose words in `B` are pairwise `delta`-separated,
   at least `alpha` of the `mu`-mass of relators has normalized-HS defect
   greater than `eps_plus`.  Equivalently, on the compact profile space of
   `finite-trace-profile-net-is-dimension-free`, `q <= 1-alpha`.
2. **Sparse local satisfiability.**  On `SC`, the sampled presentation keeps
   all distinct words in `B` distinct in the quotient.
3. **Entropy margin.**  For some profile-net radius satisfying
   `2 eta < eps_plus^2-eps^2`, if `N` is the corresponding finite profile-net
   size, then

   ```text
   N (1-alpha)^m < Pr(SC).
   ```

This is the construction theorem which, via
`finite-moment-random-relator-sparsification`, makes the all-matrix-size part
of the random-relator route finite.  It is deliberately phrased as a robust
**code** condition: many redundant local checks must certify global failure of
a separated unitary model, yet a random sparse set of checks must often leave a
specified group ball intact.

## Attempts

- **Thin derivation / coupon collector — insufficient.**  If `M` checks form a
  chain where only the complete chain forces collapse, an adversarial profile
  can satisfy `M-1` checks, so `alpha` is only `1/M`; the probability that a
  random sparse sample preserves the forbidden consequence then loses on the
  same coupon-collector scale.  The finite net factor cannot be beaten.  The
  soundness must be redundant, PCP-style.
- **Classical parity/LTC code — wrong endpoint.**  Classical locally testable
  linear constraints can have excellent soundness, but commuting/parity group
  presentations left after sparsification remain in an amenable/residually
  finite regime.  Code soundness alone is not nonhyperlinearity; the checks
  must be noncommutative in the unitary/tracial assignment class.
- **BCS algebra route.**  Paddock--Slofstra (arXiv:2310.07901) identify BCS
  algebras with synchronous game algebras and show algebra-preserving
  reductions; they explicitly connect `R^U`-satisfiability dichotomies to the
  existence of a nonhyperlinear group.  Search for a robust-sound BCS whose
  constraint hypergraph has enough local redundancy and whose random sparse
  subinstances retain a short nontrivial solution-group ball.
- **LCS/solution-group compiler.**  Goldberg (arXiv:2007.02782) realizes the
  synchronous LCS game algebra as a quotient of the solution-group algebra.
  Thus a constant-gap commuting-operator verifier compiled to LCS syntax would
  nearly produce the required relator code.  The missing theorem is a robust
  compiler preserving both finite-dimensional/tracial soundness and the sparse
  local group witness.
- **MIP^co compression as soundness source.**  Lin (arXiv:2510.07162) proves
  `MIP^co = coRE` via gapped commuting-operator compression.  Rather than use
  the game as a final object, use its redundant checks as a master PCP and
  groupify them through BCS/LCS reductions.  The key audit question is whether
  the reduction preserves a constant finite-dimensional unitary loss, not
  merely perfect-strategy satisfiability.
- **qLTC analogy, not an import.**  Constant-soundness qLTC constructions show
  that local quantum checks can robustly certify global failure.  Translating
  Hamiltonian/code distance into normalized-HS group-word syndrome is exactly
  the missing work, paralleling the warning already recorded at
  `extensive-cosystolic-index-defect`.
