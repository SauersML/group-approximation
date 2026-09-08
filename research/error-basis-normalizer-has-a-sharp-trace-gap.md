---
rg: 2
id: error-basis-normalizer-has-a-sharp-trace-gap
kind: claim
title: Every nonscalar normalizer of a group-labelled unitary error basis is a fixed normalized-HS distance from the identity
distinct_from:
  clifford-direct-sum-dilution-forces-an-exact-good-block: that quantizes the distance from a curvature already in the normal form lambda P_a to the block unit scalars and gets squared distance exactly 2; this bounds every nonscalar element of the full normalizer of an arbitrary group-labelled error basis, a strictly larger class containing the phase gate, whose sharp constant is the smaller 2 - sqrt 2.
  finite-clifford-symplectic-section-obstruction: that is a global group-extension nonsplitting theorem for the Clifford group; this is an elementary trace identity for one normalizer element, with no extension or cohomology.
artifacts:
  - research/artifacts/leavitt-error-basis-normalizer-obstruction-2026-09-08.md
---

**ESTABLISHED.** Let `(W_a)_(a in A)` be a group-labelled unitary error
basis of `M_d(C)`: `A` is a finite group of order `d^2`, `W_e = I`,
`tr_d(W_a^* W_b) = delta_(ab)`, and `W_a W_b` is a unit scalar times
`W_(ab)`. Let

```text
N(W) = { U in U(d) : U W_a U^* in T W_(sigma(a)) for a permutation sigma }.
```

Then `N(W)/T I` is finite, and every nonscalar `U in N(W)` satisfies

```text
|tr_d(U)| <= 1/sqrt 2,      ||U - I||_(2,d)^2 >= 2 - sqrt 2.
```

Both constants are sharp: in `d = 2` with the Pauli basis, the phase gate
`S = diag(1,i)` normalizes it with `SXS^* = Y`, `SYS^* = -X`,
`SZS^* = Z`, and `e^(-i pi/4) S` attains equality in both.

The mechanism is that conjugation by `U` has trace `|Tr(U)|^2` in the
matrix-unit basis and `sum_(sigma(a)=a) xi(a)` in the error basis, where
`U W_a U^* = xi(a) W_(sigma(a))`. The multiplication rule forces `sigma`
to be an automorphism, so its fixed points are a subgroup: proper when
`sigma` is nontrivial, which halves the count, and when `sigma` is
trivial `xi` is a character of `A`, nontrivial for nonscalar `U`, so
the sum vanishes outright.

Write `gamma = sqrt(2 - sqrt 2)` for the resulting gap.

DERIVATION
error-basis-normalizer-trace-gap-proof
