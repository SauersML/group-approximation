---
rg: 2
id: leavitt-visible-states-colimit-proof
kind: route
title: Split the cone over the characters, push along the refined idempotents, and pass to the colimit through finitely supported certificates
target: leavitt-visible-states-are-factorwise-and-colimit-stable
requires:
  - leavitt-unit-group-algebras-split-over-scalar-characters
  - twisted-leavitt-corner-fullness-equals-absence-of-k0-states
  - cyclic-twist-makes-leavitt-visible-factor-a-matrix-algebra
artifacts:
  - research/artifacts/ternary-anti-central-invariant-census-2026-09-12.md
---

## Why sufficient

- **Factorwise.**
  - `K_0` of a finite product is the direct sum, with the product cone.
  - A state with weight `t_chi = 0` on a factor vanishes there, because every class of `K_0(A_chi)`
    lies between `-N[eps_chi]` and `N[eps_chi]`.
  - The augmentation `F_q[G] -> F_q` kills every `eps_chi` except the trivial one.
- **Ascent.**
  - `eps_iota(q) eps_iota(q^r) = eps_iota(q^r)`, because each `[lambda]` with `lambda in F_q^x` acts
    as `lambda` on `A_iota(q^r)`.
  - Since `eps_iota(q^r)` is central, multiplication by it is multiplicative and unital.
  - Ring homomorphisms preserve the positive cones and the unit classes.
- **Colimit.**
  - *Finiteness.* `V` and `K_0` commute with directed colimits of unital rings, because idempotent
    matrices, and the matrices realizing isomorphisms, have finitely many entries. So `u <= 0` holds
    in the colimit iff it holds at some stage. The state criterion (Theorem A(b) of the artifact,
    valid for every unital ring) gives the first equivalence.
  - *Corner to nonpositive.* Ascend the corner to a stage with `m | q - 1`. This is possible because
    every `m` prime to `p` divides some `p^(k!) - 1`. Then apply 1 => 4 of the equivalence claim.
  - *Nonpositive to corner.* Choose an admissible `m` prime to `p`: `d` or `2d - 1`, both
    `1 mod (d - 1)`, and `p` cannot divide both. Push `u <= 0` to a stage containing a primitive
    `m`-th root of unity, and apply 4 => 1 there.

Section 8 of the artifact.
