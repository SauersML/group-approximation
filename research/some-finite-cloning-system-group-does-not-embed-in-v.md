---
rg: 2
id: some-finite-cloning-system-group-does-not-embed-in-v
kind: claim
title: "Some cloning system on finite groups has a Thompson-like group that does not embed in V"
artifacts:
  - research/artifacts/zp-lehnert-2-16-2026-09-13.md
---

There is a cloning system on finite groups whose Thompson-like group `T(G_*)`
does not embed in Thompson's group `V`. This is the negative answer to the
embedding sub-question of Zaremsky Problem 2.16.

## Attempts

- If the witness `T(G_*)` is also coCF, it refutes Lehnert's conjecture
  (`lehnert-conjecture-every-cocf-group-embeds-in-v`); the standing candidates
  are `V_(G,θ)`, `θ ≠ id` (`twisted-direct-power-cloning-finite-groups-are-cocf`),
  which are coCF and have no obvious faithful Cantor action (Berns-Zieve et al.).
  Proving non-embedding needs an invariant `V` has that `V_(G,θ)` lacks;
  Burillo–Cleary–Röver obstructions (arXiv:1402.3860) and the CF-TR /
  context-free-action characterisation (arXiv:2608.02111) are the tools.
- If the witness is not coCF (see
  `some-finite-cloning-system-group-is-not-locally-cocf`), non-embedding is
  automatic, since every f.g. subgroup of `V` is coCF. That route does not touch
  Lehnert's conjecture.
- Bodart–D'Angeli–Perego–Rodaro (arXiv:2608.02111) report all currently known
  coCF groups embed in `V`, so no witness is known to this lane.
- Status update (2026-09-16): the standing candidates `V_(G,θ)`, `θ ≠ id`, in
  the first bullet are eliminated. They embed in `V` by BDPR (arXiv:2608.02111v1,
  Theorem B / Theorem 3.2, PDF read 2026-09-16) and independently by
  `twisted-power-cloning-groups-embed-in-v`, which also covers two-endomorphism
  direct-power cloning systems. Any witness must come from a cloning system
  outside that family, for example the non-local upper-triangular systems
  `B_n(F_q)`.
