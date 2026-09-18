---
rg: 2
id: fox-witness-kills-augmentation-torus-degree-proofs
kind: claim
title: Over every group with a nontrivial finitely generated perfect subgroup, some square matrix over the integral group ring has identity augmentation and a nonzero left kernel, so augmentation-only proofs of torus degree regularity die there, torsion-free groups such as Higman's included
distinct_from:
  torus-degree-regular-on-prime-power-residual-support: its sharpness half (b) is the Bezout witness, which needs a finite subgroup of non-prime-power order and lives at d = 1; this is the Fox-Jacobian witness, which needs a finitely generated perfect subgroup, exists over torsion-free groups such as Higman's group, and lives at d = number of generators.
  locally-indicable-groups-are-torus-surjunctive: that is the positive half on locally indicable support; this is the obstruction on the complementary class of groups with perfect finitely generated subgroups.
  higman-group-algebra-not-stably-finite: that concerns stable finiteness of a Higman-group algebra; this is a zero divisor in a matrix ring over the integral group ring of Higman's group with identity augmentation.
artifacts:
  - research/artifacts/torus-degree-locally-indicable-and-fox-witness-2026-09-18.md
  - experiments/torus-fox-witness-2026-09-17/check_fox_witness.py
---

**Setup.** Let `H` be a group containing a nontrivial finitely generated perfect subgroup
`L = <x_1, ..., x_n | r_j>`, with every `x_i != 1`. Let `J` be the Fox Jacobian of the relators
(entries in `Z[L]`), and pick `P in M_{n x k}(Z)` with `P epsilon(J) = I_n`, using finitely many
relators. Put `D = (P J)^*`.

**Claim.**
- `D in M_n(Z[H])` and `epsilon(D) = I_n`.
- `c^* D = 0` for the nonzero row `c^* = (x_1^{-1} - 1, ..., x_n^{-1} - 1)`.
- So `D` passes every test visible to the constants of a torus automaton. That is exactly the
  data `epsilon(D) in GL_d(Z)` from the periodic-point lemma at `N = G`, yet `D` is singular
  over `Q[H]`.
- Any proof of `injective-torus-automata-have-regular-degree` that uses only
  `epsilon(D) in GL_d(Z)` plus ring theory of `Z[H]` fails on `H`.

**Higman's group.** Explicitly, `H = <a, b, c, d | x_{i-1}^{-1} x_i x_{i-1} = x_i^2>` with
indices mod 4. Row `i` of `P J`, reduced in `H`, has `1 + x_i - x_{i-1}^{-1}` in column `i` and
`x_{i-1}^{-1}(1 - x_i)` in column `i-1`, giving a `4 x 4` witness.

**Updated map of augmentation-only reach**, with the support group `<supp D>`:
- It **succeeds** on RPP support (`torus-degree-regular-on-prime-power-residual-support`) and on
  locally indicable support (`locally-indicable-groups-are-torus-surjunctive`).
- It **dies** on a finite subgroup of non-prime-power order (Bezout) and on a nontrivial f.g.
  perfect subgroup (Fox, here).

**Kill-test.** Construct, or rule out, an injective torus automaton on `(T^4)^H` with degree
`D`, for `H` Higman's group. It would refute torus surjunctivity at `H`.

**ESTABLISHED 2026-09-18** by [[fox-witness-kills-augmentation-torus-degree-proofs-proof]].
