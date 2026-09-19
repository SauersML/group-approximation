---
rg: 2
id: self-similar-clifford-quantum-expander-tape
kind: claim
title: A finite presentation realizes uniform quantum-expander checks on every Clifford tape prefix
distinct_from:
  explicit-constant-degree-quantum-expanders: that supplies explicit channels in circuit form; this requires one finite group-word syntax compatible with a nested Clifford tower.
  relative-t-heisenberg-adjoint-quantum-expansion: that proves a relative-Kazhdan Jacobi action supplies the uniform analytic gap once the quotient representations exist; this still has to construct their finite self-similar word syntax and controlled rank-gate compatibility.
  uniform-halting-pauli-word-oracle: that exposes all questions of a post-halting Pauli test; this exposes only a constant-degree commutant test at every prefix of one self-similar Clifford tape.
---

Construct a finitely presented self-similar group containing a nested Clifford
tower

```text
E_1 <= E_2 <= ...,
```

with a marked sign transported coherently between levels, together with a
fixed number `D` of word templates
whose level-`n` conjugates act on every `J=-1` spin block of `E_n` as a
`D`-regular quantum expander with one uniform gap `1-lambda>0`.

The defining relations must expose those conjugations with derivation cost
polynomial in `n`, preserve an exact nontrivial marked model in the required
self-referential branch, and be compatible with adjoining the next controlled
Pauli cell. These conditions let
`quantum-expander-rounds-relative-pauli-cell` exactify each new cell with a
constant independent of the existing Clifford rank.

## Attempts

- Ben-Aroya--Schwartz--Ta-Shma give explicit constant-degree quantum expanders
  by tensoring, squaring and quantum zig-zag. Their circuit descriptions are
  not automatically conjugates of finitely many words in one presentation.
- Gross--Eisert's quantum Margulis construction uses affine phase-space maps
  implemented by Clifford/metaplectic unitaries and has the classical
  Margulis spectrum, but the cited construction is for odd phase-space
  dimension and does not directly provide the binary nested tower here.
- **Automatic mother-group test.**
  `automatic-mother-expanders-do-not-normalize-leavitt-prefix-heads` proves
  that the cyclic odometer `P_n` and the Thue--Morse diagonal `D_n` generate
  every binary matrix algebra.  Hence the fixed Kazhdan generators of
  `EL_3(F_2<x,y>)` do give uniform transitive expanders on the separate
  finite natural modules.  The direct self-similar compiler nevertheless
  fails exactly on off-diagonal prefix roots: the odometer's unequal
  sections leave a tail multiplier.  Any inner normalizers compatible with
  all nested full matrix heads factor into one-qubit tensor products and
  cannot be transitive.  The missing operation is therefore a uniform
  state-decoupling relation, not another finite-level expander.
- `relative-t-heisenberg-adjoint-quantum-expansion` removes the need to
  internalize a quantum zig-zag circuit. A fixed relative Kazhdan set in a
  Jacobi-type group is automatically a constant-degree quantum expander in
  every irreducible finite Heisenberg quotient. The remaining construction
  problem is algebraic: find one finitely presented Jacobi/self-similar group
  with a binary nested congruence tower, compatible Schrodinger--Weil
  projective actions, polynomial word-derivation cost, and the same central
  sign used by the controlled Schur rank gate. The sign may be the conjugate
  level family `J_n=t^n J_0 t^(-n)`:
  `conjugate-local-signs-preserve-marked-carrier` proves that this retains the
  marked separation and carrier trace exactly, so global centrality is not
  required.
- **Thompson--Nekrashevych frame.**
  `nekrashevych-clifford-sign-tape` isolates a classical home for internal
  subtree transport and polylogarithmic addressing. Its prior algebraic gate
  is `self-similar-central-sign-cocycle`: the sign cannot satisfy the
  untwisted recursion `J=(J,J)`, by
  `untwisted-sign-replication-flips-minus`. If the cocycle is found, the
  remaining soundness obligation is the fixed sibling covariance certificate
  a still-missing sibling trace-independence certificate.
