---
rg: 2
id: ssa-kunneth-forces-solid-k-theory
kind: claim
title: Strongly self-absorbing algebras satisfying Kunneth have solid K-theory rings
artifacts:
  - research/artifacts/stw99-xv-solid-ring-reduction-2026-08-30.md
  - research/artifacts/ssa-self-kunneth-xiv2-audit-2026-08-31.md
---

Let `D` be a strongly self-absorbing C\*-algebra satisfying the
Künneth short exact sequence for the pair `(D, D)`.  Then:

1. `K_1(D) = 0`. This is a consequence of the self-Kunneth
   hypothesis: the first-factor K-isomorphism forces unit insertion
   into the graded tensor square to be onto, which kills the odd
   group. It is not an unconditional consequence of SSA.
2. The tensor multiplication makes `K_0(D)` a commutative unital ring
   whose multiplication map `K_0(D) ⊗_Z K_0(D) → K_0(D)` is an
   ISOMORPHISM — a *solid ring* in the sense of Bousfield--Kan.
3. `K_0(D)` is TORSION-FREE: the degree-one Künneth sequence has
   vanishing tensor part (`K_1 = 0`), so
   `K_1(D ⊗ D) ≅ Tor(K_0(D), K_0(D))`; the first-factor isomorphism
   identifies this with `K_1(D) = 0`, and `Tor(A, A) = 0` forces `A`
   torsion-free.
4. By the Bousfield--Kan classification, a torsion-free solid ring is
   a localization: `K_0(D) ≅ Z[J^{-1}]` with `[1_D]` the ring unit
   `1`, or `K_0(D) = 0`.

Consequently STW Problem XV holds IN FULL for every `D` satisfying
the Künneth sequence against itself: the `K`-theory is
`(Z[J^{-1}], 0)` — realized by `M_{J^∞}` (`(Z,0)` by `Z`/`O_∞`,
`(Q,0)` by the `Q`-types) — or `(0,0)`, realized by `O_2`; and in the
`K_0 = 0` case `stw99-xvi-holds-for-reference-targets` upgrades the
conclusion to `D ≅ O_2` outright.  The only escape for a
counterexample to XV is FAILURE of the self-Künneth sequence, a
UCT-level event.  (The earlier torsion-free-locus caveat is removed
by clause 3; `stw99-iv-implies-xv-torsion-free` remains as the
route from the torsion-free-coefficient Künneth problem IV.)
