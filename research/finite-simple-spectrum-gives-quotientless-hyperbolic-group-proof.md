---
rg: 2
id: finite-simple-spectrum-gives-quotientless-hyperbolic-group-proof
kind: route
title: Avoid a prime: a common quotient with a free product of three cyclic groups of that order has no finite simple image
target: finite-simple-spectrum-gives-quotientless-hyperbolic-group
requires: [olshanskii-g-subgroup-quotient-theorem, torsion-free-hyperbolic-kazhdan-partner-exists]
artifacts:
  - research/artifacts/hyperbolic-finite-simple-spectrum-construction-2026-09-12.md
---

Let `S_1, ..., S_r` be the finite simple quotients of `H`, up to isomorphism. Choose a
prime `ℓ` dividing none of the orders `|S_i|`.

**Inputs.**
- `H_1 = H/E(H)`, where `E(H)` is the maximal finite normal subgroup. It is
  non-elementary hyperbolic with trivial finite radical, and its finite simple quotients
  are among the `S_i`.
- `J = C_ℓ * C_ℓ * C_ℓ`, non-elementary hyperbolic with trivial finite radical.
- `K` from `torsion-free-hyperbolic-kazhdan-partner-exists`: torsion-free,
  non-elementary, hyperbolic, Kazhdan.

**Common quotient.** Put `G = H_1 * J * K`. It is non-elementary hyperbolic, and
`E(G) = 1`.

Take a factor `X`. A nontrivial finite subgroup normalized by `X` fixes a vertex of the
Bass–Serre tree, and since `X` is infinite, that vertex is the unique vertex fixed by
`X`. So the subgroup is a finite normal subgroup of `X`, hence trivial. This gives
`E(X) = 1 = E(G)`, and both index conditions in part 1 of
`olshanskii-g-subgroup-quotient-theorem` read `1 = 1`. So each factor is a G-subgroup.

Part 2 of that theorem gives a non-elementary hyperbolic group `P` and an epimorphism
`φ : G -> P` with `φ(H_1) = φ(J) = φ(K) = P`.
- `P` has property (T), because `K` surjects onto it.
- `P` is infinite, because it is non-elementary.

**No finite quotient.** Suppose `P -> F` is onto a nontrivial finite group. Choose a
maximal proper normal subgroup of `F`, with simple quotient `S`.
- `H -> H_1 -> P -> S` is onto, so `S` is some `S_i`, and `ℓ` does not divide `|S|`.
- `J -> P -> S` is onto and nontrivial. So it is nontrivial on some free factor `C_ℓ`,
  hence injective on it, and `ℓ` divides `|S|`.
This is a contradiction, so `P` has no nontrivial finite quotient.

(Artifact §1 is this argument with the forbidden subgroup `A = C_ℓ`, and §2 item 2 is the
reduction to a prime.)
