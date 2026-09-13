---
rg: 2
id: km-246-stability-dictionary-via-character-rigidity
kind: route
title: Apply the character-rigid stability dictionary to the (2,4,6) Kac-Moody lattice
target: km-246-lattice-stability-dictionary
requires:
  - km-246-lattice-is-character-rigid
  - km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4
  - character-rigid-fp-simple-groups-stability-dictionary
---

Let `q >= 4`.
- By `km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4`, `S_q` is finitely presented,
  infinite and simple.
- By `km-246-lattice-is-character-rigid` (CR2), its only extreme normalized characters are
  `τ_reg = δ_e` and `τ_triv = 1`, and every normalized character is
  `t τ_reg + (1-t) τ_triv`.

These are exactly the hypotheses of `character-rigid-fp-simple-groups-stability-dictionary`.
Its items (P) and (U), specialized to `Γ = S_q`, are items (P) and (U) of the target.
