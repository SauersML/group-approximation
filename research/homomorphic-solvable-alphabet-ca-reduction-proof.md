---
rg: 2
id: homomorphic-solvable-alphabet-ca-reduction-proof
kind: route
title: Filter by the derived series and apply the snake argument layer by layer
target: homomorphic-solvable-alphabet-ca-reduce-to-stable-finiteness
requires: [stable-finiteness-failure-refutes-surjunctivity]
artifacts:
  - research/artifacts/strategist-neg-counterexample-plans-2026-09-12.md
---

Section 1.3 of the artifact.
- The local rule `mu : K^S -> K` is a homomorphism. It maps `(K^(i))^S` into `K^(i)` for every term of
  the derived series, and it preserves the p-primary components and the subgroups `p^j L` of each
  abelian layer. So the automaton preserves a characteristic filtration whose layers are `F_p`-vector
  spaces.
- **Induction on the filtration.** Take a characteristic `N` with quotient `Q`.
  - `tau` injective gives `tau_N` injective, hence surjective by induction.
  - Then `tau_Q` is injective: `tau(x) = tau(n)` forces `x = n`. So it is surjective by induction.
  - Then `tau` is surjective: `y = tau(x) tau(n) = tau(xn)`.
- **Base case.** An injective `F_p`-linear automaton on `(F_p^n)^G` is surjective when `M_n(F_p[G])` is
  directly finite (the linear surjunctivity–stable finiteness equivalence).
- **Converse.** That is the required node.
