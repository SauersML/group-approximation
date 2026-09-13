---
rg: 2
id: infinite-support-coordinate-permutations-are-nowhere-v-germs
kind: claim
title: A coordinate permutation of Cantor space with infinite support agrees with no element of V near any point
distinct_from:
  shell-cantor-embeddings-are-finite-germ-extensions: that realizes an arbitrary countable group by homeomorphisms singular only on the countable orbit V*p, giving a finite germ extension of V; this shows that Bernoulli coordinate actions are singular at every point, so they never give a finite germ extension of V.
  fp-full-binary-cantor-groups-have-type-a-actions: that turns a finitely presented full Cantor group containing V into a type (A) actor; this rules out Bernoulli coordinate actions as a supply of germs for such a group through the finite germ extension criterion.
artifacts:
  - research/artifacts/shell-envelope-local-tests-2026-09-13.md
---

**ESTABLISHED.** Let `C = {0,1}^N` with `N = {0,1,2,...}`, and let `V` be the
standard binary Thompson group acting on `C` by prefix replacements. For a
bijection `pi : N -> N` let `f_pi` be the homeomorphism
`f_pi(x)_j = x_(pi^(-1)(j))`.

**Theorem.** If `pi` moves infinitely many points, then for every `x` in `C`
no element of `V` agrees with `f_pi` on any neighbourhood of `x`. So `f_pi` is
singular relative to `V` at every point: `sing(f_pi) = C`.

**Consequence (Bernoulli hosts).** Let `Gamma` be an infinite countable group,
`nu : Gamma -> N` a bijection, and `beta_g = f_(pi_g)` with
`pi_g = nu o lambda_g o nu^(-1)`, where `lambda_g` is left translation. This is
the Bernoulli action `(g.x)(h) = x(g^(-1) h)` on `{0,1}^Gamma`, transported to
`C`. For `g != 1`, `lambda_g` has no fixed point, so `pi_g` has infinite support
and `sing(beta_g) = C`. Hence `<V, beta(Gamma)>` is not a finite germ extension
of `V` in the sense of Belk–Hyde–Matucci (arXiv:2407.03149; the definition
requires finitely many singular points for every element, quoted in the
artifact), and their Theorem 2.1 gives no finiteness information about it.

**Scope.** Nothing is asserted about finite presentation of `<V, beta(Gamma)>`.
The result is elementary and no novelty is claimed.
