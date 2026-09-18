---
rg: 2
id: rover-nekrashevych-bnsr-invariants-are-full
kind: claim
title: Every BNSR invariant of a Rover--Nekrashevych group is its whole character sphere, the sphere of sum-invariant characters
distinct_from:
  rover-nekrashevych-finite-presentation-criteria: that records finiteness properties, simplicity of the commutator subgroup and the abelianization; this computes the BNSR invariants on the character sphere.
---

**OPEN (candidate answer to Zaremsky Problem 1.14).** Let `G <= Aut(T_d)`, `d >= 2`, be a finitely generated
self-similar group, and put `Γ = V_d(G)`.

1. **Sphere.** Restriction to `G` (acting on one cone) identifies `Hom(Γ,R)` with the characters `χ: G -> R`
   satisfying `χ(g) = Σ_{x in X} χ(g|_x)` for all `g`.
2. **Invariants.** `Σ^m(Γ) = S(Γ)` for every `m >= 1` such that `Γ` has type `F_m`.

Model tests. With `G` trivial, `Γ = V_d` has finite abelianization, so both items are vacuous. For the binary
odometer `a = σ(1, a)` the sphere is `S^0`, and item 2 says both kernels of `Γ -> Z` have type `F_m` whenever `Γ` does.

## Attempts

- **Item 1: ESTABLISHED** as `rover-nekrashevych-characters-are-sum-invariant` (unreviewed).
- **Item 2, `m = 1`: ESTABLISHED** as `rover-nekrashevych-groups-have-full-bns-invariant` (unreviewed). The
  characters are realized on arbitrarily small cones, where they commute with cone-fixing generators of `V_d`.
- **Item 2 for `G` of type `F_m`: OPEN**, isolated as `rover-nekrashevych-higher-sigma-invariants-are-full` and
  reduced by `rover-nekrashevych-higher-sigma-full-via-kernel-brown` to two named inputs:
  - `rover-nekrashevych-stein-farley-complex-properties`;
  - `characters-living-on-m-plus-one-factors-lie-in-sigma-m`.
  - Key step: `χ(Stab σ) = χ(Γ)` for every cell, so the kernel of the full character map acts cocompactly on every
    cocompact subcomplex, with stabilizers that are kernels on products `G^n`.
- **Item 2 for bounded automata `G`, all `m`: ESTABLISHED** as
  `rover-nekrashevych-bounded-automata-sigma-invariants-full` (unreviewed): `Σ^∞(V_{d,r}G) = S`.
  - The complex is the Belk–Hyde–Matucci germ complex of `V_{d,r}G` over `V_{d,r}`, whose cell stabilizers are
    virtually point stabilizers in `V_{d,r}`, not products `G^n`. The engine is
    `germ-extension-base-trivial-characters-lie-in-sigma`: a germ-charge potential gives an equivariant height, and
    ascending links are joins of discrete sets with skeleta of infinite simplices.
  - This covers groups of every finiteness type, including the Basilica group (settling the test below) and the
    odometer.
  - Still open: contracting `G` beyond bounded activity (polynomial activity, where the base carries characters), and
    general self-similar `G`.
- **Item 2 when `G` is not of type `F_m` but `Γ` is: OPEN beyond bounded automata** (see the previous bullet for
  Basilica and all bounded automata groups). Nekrashevych (arXiv:1312.5654, Theorem 5.9)
  gives finite presentation of `V_d(G)` for every contracting `G`, finitely presented or not. The Basilica group has
  the character `χ(a) = χ(b) = 1`, assuming its abelianization `Z^2` (Grigorchuk–Żuk, not re-derived here). So
  `Σ^2(V_2(Basilica))` is the first test where item 2 could fail. The stabilizer route gives nothing there, because
  `Basilica^n` is not finitely presented. A proof would need a different complex, such as the nucleus-based
  presentation of Nekrashevych.
