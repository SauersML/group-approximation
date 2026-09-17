---
rg: 2
id: cloning-system-groups-on-finite-groups-embed-in-v
kind: claim
title: "Every cloning system on finite groups has a Thompson-like group that embeds in V"
artifacts:
  - research/artifacts/zp-lehnert-2-16-2026-09-13.md
refuted_by:
  - some-finite-cloning-system-group-does-not-embed-in-v
---

For every cloning system on finite groups `G_n`, the Thompson-like group
`T(G_*)` embeds in Thompson's group `V`. This is the affirmative answer to the
embedding sub-question of Zaremsky Problem 2.16. Because `V` is coCF and coCF
passes to finitely generated subgroups, this implies
`finite-cloning-system-groups-are-locally-cocf`.

## Attempts

- Positive test cases: `G_n = S_n` gives `V` itself; `G_n` trivial gives `F ≤ V`;
  `G_n = Z/n` gives `T ≤ V`. For twisted direct powers `V_(G,θ)` with `θ = id`
  the group is the labeled `V` `= G ≀_C V`, which embeds in `V` (Nekrashevych;
  a finite group of leaf-labels is a demonstrative subgroup datum).
- The open case is `θ ≠ id`: Berns-Zieve et al. found no obvious faithful Cantor
  action for `V_(G,θ)`. The CF-TR criterion (Bodart–D'Angeli–Perego–Rodaro,
  arXiv:2608.02111: embeds in `V` iff admits a faithful context-free action)
  and Jaspars' pullback criterion (arXiv:2608.01168) are the tools to decide it;
  the former's abstract states all known coCF groups embed in `V`. Not settled
  by this lane.
- Status update (2026-09-16): the case `θ ≠ id` above is settled. BDPR
  (arXiv:2608.02111v1, Theorem B / Theorem 3.2, PDF read 2026-09-16) prove that
  `V_(H,θ)` embeds in `V` for every finite `H` and every `θ ∈ End(H)`.
  Independently, `twisted-power-cloning-groups-embed-in-v` covers the pure
  direct-power systems with cloning `g ↦ (φ0 g, φ1 g)`,
  `ker φ0 ∩ ker φ1 = 1`, which includes `φ0 = id`. Still open: general non-local
  cloning systems, such as the Witzel–Zaremsky upper-triangular groups
  `B_n(F_q)`, where cloning duplicates a row and a column (see
  `notes/zaremsky-2-16-lehnert-conjecture-swarm-2026-09-16.md` §3, item 4).
- Status update (2026-09-17, swarm-0917-w5-pull-z-1).
  - *Refuted.* This universal claim is REFUTED by the ESTABLISHED
    `some-finite-cloning-system-group-does-not-embed-in-v`. The bit-register system on
    `Sym({0,1}^n)` has doubly exponential period growth; see route
    `finite-cloning-group-not-in-v-by-period-growth`.
  - *Upper-triangular systems.* For `B_n(F_q)` the case is reduced rather than settled.
    - `upper-triangular-cloning-groups-contain-lamp-wreath-z2` (ESTABLISHED, unreviewed) gives
      `(R,+) ≀ Z^2 ≤ T(B_*(R))` for every nonzero ring `R`. The lamps are root-split unipotent
      blocks, and `Z^2` comes from `F_L × F_R`. It is checked by computer over `F_3`.
    - In characteristic 0 this gives `char-zero-upper-triangular-cloning-groups-do-not-embed-in-v`
      via Corwin's theorem. Those groups are infinite, so they are outside this claim.
    - Over `F_q` it reduces the question to the OPEN
      `cyclic-p-wreath-z2-does-not-embed-in-thompson-v`, through route
      `finite-field-upper-triangular-cloning-not-in-v-via-lamplighter`. Period growth fails for
      `B_n(F_q)`, because element orders are linear in `n`.
