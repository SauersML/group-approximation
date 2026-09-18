---
rg: 2
id: ballistic-machine-runs-give-periodic-points-proof
kind: route
title: A ballistic run reads a constant symbol, so its state sequence is eventually periodic, and so is the trail it writes
target: ballistic-machine-runs-give-periodic-points
requires:
  - odometer-factor-witnesses-mix-coordinates
  - renormalizable-thompson-elements-are-odometer-codes
  - brin-thompson-first-return-maps-lie-in-kv
---

**Item 1.** Let `q_0 = q` run ballistically over `a`. The head never turns, so every cell it reads is a fresh
cell of the background: the symbol read is always `a`.
- The next state is `q_{i+1} = g(q_i)` and the written symbol is `b_i = w(q_i)`, where `(q_i, a) → (b_i, q_{i+1})`
  is the table entry. Both depend on `q_i` alone.
- The state set is finite, so there are `i_0` and `p ≥ 1` with `q_{i+p} = q_i` for all `i ≥ i_0`. Then also
  `b_{i+p} = b_i`.
- Let `c` be the configuration at phase 2 in state `q_{i_0}`, with `a^∞` ahead of the head and the trail
  `⋯ b_{i_0+p-1} ⋯ b_{i_0} b_{i_0+p-1} ⋯ b_{i_0}` behind it, repeated with period `p` and read outward from the
  head.
- After `p` read-and-move cycles, i.e. `2p` steps of `F`, the head is again in state `q_{i_0}` at phase 2. The tape
  ahead is still `a^∞`, and the trail behind has gained `p` new symbols `b_{i_0}, …, b_{i_0+p-1}`, which is the same
  periodic pattern.
- Positions are measured from the head, so `F^{2p} c = c`. ∎

**Item 2.** If `π ∘ F = π + 1` in `Z_m`, then `π(c) = π(F^{2p} c) = π(c) + 2p`. So `2p = 0` in `Z_m`, which is false
because `Z_m` is torsion-free.

**Item 3.**
- The orbit of `c` meets `Y`, by bounded return. Pick `y` in it. Its `S`-orbit is contained in the finite
  `F`-orbit of `c`, so `y` is a periodic point of `S`.
- A height-`m` renormalization of `S` gives a factor onto `Z_m` (`renormalizable-thompson-elements-are-odometer-codes`,
  item 2), and a periodic point excludes that, as in item 2 and in `odometer-factor-witnesses-mix-coordinates`.
- The bounded-return hypothesis is the one of `brin-thompson-first-return-maps-lie-in-kv`, which is what puts `S`
  into `kV`. ∎

**The tables.**
- `M_m`, rule `F_j → (0, F, pass)`: in state `F` reading `j`, it writes 0 and continues in `F`. So `F` runs
  ballistically over `j`, with `p = 1`.
- `M_m`, rule `H0 → (2j, H, pass)`: `H` runs ballistically over 0.
- The quadrupling table, rule `F0 > F0` (non-mirror state `F` = shape 0 moving left): same state, same direction.
- SMART (Callard–Salo's table), filled states: on 0 they write 1 and flip, and on nonzero symbols they keep the
  symbol and flip to hollow.
- SMART, hollow states: on 0 or 1 they turn filled, and the filled state then turns on its next read; on 2 they
  flip.
- So SMART has no ballistic state. The same check on `SMART_m`'s table (`odd-smart-machines-have-exact-m-fold-moves`)
  gives the same result: every `b_1`/`d_1` entry flips, and every `p_1`/`q_1` entry either flips or turns filled,
  which then flips.
