---
rg: 2
id: level15-lattice-has-invariant-parity-character-detecting-h2
kind: claim
title: The index-2 subgroup N of the level-15 torsion-free lattice has an h-invariant Z/2 character that is nontrivial on h^2
distinct_from:
  index-two-strong-atiyah-is-a-twisted-norm-equation: that is the general criterion that Strong Atiyah passes to G exactly when sigma(a) a = h^2 has no solution in D(N); this computes the group-level parity invariant of h^2 for one lattice.
  sl3z-level-15-torsion-free-subgroup-outside-p-adic-hosts: that constructs H and N and shows H embeds in no torsion-free profinite group; this is a character of N detecting h^2, the input of a parity obstruction to the norm equation.
artifacts:
  - experiments/strong-atiyah-sl3z/level15_parity_character.py
  - experiments/strong-atiyah-sl3z/level15_parity_character.out
  - research/artifacts/hl-atiyah-level15-parity-2026-09-13.md
---

**ESTABLISHED** by [[level15-invariant-parity-character-proof]]. Not
independently reviewed. No novelty is claimed.

Let `H`, `N = H cap Gamma(3)`, `t`, `P_5`, `chi` and `S` be as in
`sl3z-level-15-torsion-free-subgroup-outside-p-adic-hosts`. Put
`K = ker(chi) <= P_5`, of order 16. Fix `h` in `H` minus `N`, let
`sigma(x) = h x h^-1`, and let `M = h mod 5`, so `chi(M) = 1`.

1. `N / Gamma(15)` is `{(1, k) : k in K}`, and every homomorphism `N -> Z/2`
   factors through `N -> K`, reduction mod 5.
2. Let `V = K / K^2 [K, K]`. Then `V = F_2^3`, conjugation by `M` induces a linear
   map `sigmabar` on `V`, and the image of `1 + sigmabar` has order 2.
3. For every `M` in `P_5` with `chi(M) = 1`, the class of `M^2` is not in
   `(1 + sigmabar) V`.
4. Hence some homomorphism `theta_N : N -> Z/2` has `theta_N o sigma = theta_N` and
   `theta_N(h^2) = 1`. The class of `h^2` modulo `(1 + sigmabar) V` does not depend
   on the choice of `h`.

By `twisted-norm-equation-dies-under-invariant-parity-character`, `H` satisfies
Strong Atiyah as soon as `theta_N`, or any invariant character nontrivial on
`h^2`, extends to the units of the Linnell division ring `D_C(N)`. That extension
is the open claim `level15-parity-character-extends-to-linnell-division-ring`.
