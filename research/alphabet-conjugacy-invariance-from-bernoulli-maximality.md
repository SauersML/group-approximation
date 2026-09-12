---
rg: 2
id: alphabet-conjugacy-invariance-from-bernoulli-maximality
kind: route
title: Push uniform Bernoulli measure through the conjugacy and bound Rokhlin entropy by the smaller alphabet
target: full-shifts-with-different-alphabets-are-not-conjugate
requires:
  - bernoulli-rokhlin-entropy-maximal-for-every-group
artifacts:
  - research/artifacts/gk-p-inf-wild-borel-and-topological-2026-09-12.md
---

Proposition 3.2 of the artifact.

1. Let `phi: A^G -> B^G` be a conjugacy with `|A| > |B|`, `mu` the uniform product measure and
   `nu = phi_* mu`. Then `phi` is an isomorphism of `(A^G, mu)` with `(B^G, nu)`.
2. Rokhlin entropy is an isomorphism invariant. The time-zero coordinate partition of `B^G`
   generates under the shift and has Shannon entropy at most `log |B|`.
3. So `h^Rok(A^G, mu) <= log |B| < log |A|`, which contradicts maximality.

The same argument works group by group: `h^Rok_G(A^G) = log |A|` for `G` alone suffices, which is
RBS(G) in `seward-per-group-rokhlin-entropy-of-bernoulli-shifts`.
