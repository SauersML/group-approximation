---
rg: 2
id: prime-field-left-inverse-pairs-are-stably-formalizable
kind: claim
title: Every left-inverse automaton pair over an F_p^n alphabet becomes formalizable after adding identity tracks
distinct_from:
  binary-left-inverse-pairs-are-formalizable: that is the characteristic-two statement without stabilization, which implies the p = 2 case here with no extra tracks; this is every prime, and stabilization is necessary for p >= 5 because some one-track sitewise pairs are not formalizable.
  sitewise-pairs-over-prime-fields-are-stably-formalizable: that settles the sitewise case; this asks for arbitrary memories.
artifacts:
  - research/artifacts/formalizability-prime-fields-and-alphabet-bridge-2026-09-12.md
---

**OPEN.** For every prime `p`, every group `G`, every `n >= 1`, and all automata `tau`, `sigma` on
`(F_p^n)^G` with `sigma o tau = id`, there is `k >= 0` such that `(tau (+) id_k, sigma (+) id_k)` on
`(F_p^(n+k))^G` has equivariant polynomial representatives, on possibly larger memories, in which
`sigma o tau = id` holds formally.

**Why it matters.**
- With `formal-polynomial-strict-pairs-need-unstable-linearization`, it gives
  `stable-finiteness-forces-prime-power-surjunctivity`: Kaplansky stable finiteness over `F_p` implies
  Gottschalk over every alphabet of size `p^n`.
- Through `formalizable-strict-pairs-certify-non-linear-soficity`, every counterexample over a `p`-power
  alphabet would then be a non-linear-sofic group in characteristic `p`.

## Attempts

- **Stabilization is necessary for `p >= 5`.** Over one track, a formalizable pair acts affinely on
  constant configurations (`formalizable-pairs-induce-polynomial-automorphisms-on-constants`). So a
  sitewise non-affine permutation of `F_p` has no formalizing representatives.
- **Sitewise pairs.** Formalizable after one identity track, for every prime
  (`sitewise-pairs-over-prime-fields-are-stably-formalizable`), since formally invertible maps induce every
  permutation of `F_p^n`, `n >= 2` (`tame-maps-induce-every-permutation-of-prime-field-cubes`).
- **Bennett form, every characteristic.** `V = P o S o T`, with `T(x,y) = (x, y + tau(x))` and
  `S(x,y) = (x - sigma(y), y)`, is formally invertible, and `V(x,0) = (tau(x), x - sigma(tau(x)))`. The
  task is to make the second coordinate vanish formally after adding tracks. Artifact, Section 5.
- **Where it stops.** It is the same equivariant finite-memory solvability problem inside the ideal
  `(X_h^p - X_h)` as in characteristic two. No argument is known on any group with nontrivial memory, and
  no pair that fails to be stably formalizable is known.
- **What the constant obstruction does not reach.** It only sees the diagonal specialization, and after
  one extra track every permutation of the constants is realizable. So it cannot refute this claim.
