---
rg: 2
id: fanizza-wandering-dirichlet-return-route
kind: route
title: Replace the Fanizza heat-filter tower by one wandering return word
target: non-hyperlinear-group
requires:
  - two-copy-bcs-game-hamiltonian-dominates-fanizza-signal
  - uniform-clock-reflection-block-encodes-game-hamiltonian
  - wandering-mark-cesaro-amplifier
  - fanizza-coherent-verifier-wandering-promotion
  - kleene-completeness-needs-only-a-nontrivial-exact-representation
---

**INVALIDATED BY `uniform-clock-corner-is-not-a-reflection`.** The two-copy
theorem still gives the explicit semantic inequality

```text
D_R <= C_m H_m
```

on every exact representation in the nonmember case.  The uniform clock and
controlled flag package the entire `H_m` into one explicit algebraic
reflection `V_m`, with corner Dirichlet form exactly `H_m`.  Promote this
reflection to one infinite-order group word `w` whose finite-matrix packet
compression satisfies

```text
H_m <= C'(1-Re w)                                     (FWD1)
```

in the weighted sense needed by `wandering-mark-cesaro-amplifier`.  Arrange
by an HNN/free normal form that the translates of the fixed signal mark by
`w^k` are canonically orthogonal. The former route claimed that the Cesaro
amplifier then gives a direct finite-dimensional HS ceiling versus regular
square-root growth. But the native carrier does not reduce `V_m`: its
compressed block is `1-H_m` and its squared complementary leakage is
`H_m(2-H_m)`. Therefore first-step Dirichlet comparison `(FWD1)` does not
control powers of `w`, and the compressed-reflection Cesaro theorem is
unavailable.

Exact HALT completeness may realize the packet return on countably infinite
multiplicity.  The finite-matrix estimate must not become a universal
tracial inequality.

A valid replacement must additionally construct a reducing returned carrier
or prove a weighted-state bound on all required excursions. One ordinary
return word and one first-step Dirichlet comparison are insufficient.
