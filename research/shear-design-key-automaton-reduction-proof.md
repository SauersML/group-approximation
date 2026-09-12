---
rg: 2
id: shear-design-key-automaton-reduction-proof
kind: route
title: Undo the key-controlled permutations coordinatewise and split two-address key automata over cyclic cosets
target: shear-designs-are-strict-iff-their-key-automaton-is
requires:
  - sofic-groups-are-surjunctive
artifacts:
  - research/artifacts/vh-lattice-table-hosts-2026-09-12.md
---

Section 6 of the artifact, Theorem E and Corollary 6.1. Write `pi_x(g)` for the
permutation used at `g`. It depends only on `x_K`.

1. **Surjectivity.** Given `y`, choose `x_K` with `kappa(x_K) = y_K` and put
   `x_D(g) = pi_x(g)^(-1)(y_D(g))`. Conversely the first coordinate of `tau` is `kappa`.
2. **Injectivity.** If `kappa` is injective, equal images give equal keys, hence equal
   permutations and equal data. If `tau` is injective and `kappa(x_K) = kappa(x'_K)`, take
   any `x_D` and put `x'_D(g) = pi_(x')(g)^(-1)(pi_x(g)(x_D(g)))`. Then `tau(x) = tau(x')`,
   so `x_K = x'_K`.
3. **Two-address track automata.** `k -> phi(k(. v), k(. h))` is the bijective translation by
   `v` followed by an automaton with memory `{1, c}`, `c = v^(-1) h`. That automaton acts on
   every left coset of `<c>` as one automaton on `A^(<c>)`, so it is injective, respectively
   surjective, iff that one is. A cyclic group is residually finite, hence sofic and
   surjunctive.
4. A product of track automata is injective, respectively surjective, iff every factor is.
