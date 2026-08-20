---
rg: 2
id: self-similar-clifford-quantum-expander-tape
kind: claim
title: A finite presentation realizes uniform quantum-expander checks on every Clifford tape prefix
distinct_from:
  explicit-constant-degree-quantum-expanders: that supplies explicit channels in circuit form; this requires one finite group-word syntax compatible with a nested Clifford tower.
  uniform-halting-pauli-word-oracle: that exposes all questions of a post-halting Pauli test; this exposes only a constant-degree commutant test at every prefix of one self-similar Clifford tape.
---

Construct a finitely presented self-similar group containing a nested Clifford
tower

```text
E_1 <= E_2 <= ...,
```

with common marked sign, together with a fixed number `D` of word templates
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
- The likely route is to internalize the quantum zig-zag recursion as a finite
  substitution system, with the tape shift implementing tensor growth and a
  constant seed expander acting on the rotation register. The unresolved
  check is exact compatibility with the common central sign and the controlled
  rank gate.
