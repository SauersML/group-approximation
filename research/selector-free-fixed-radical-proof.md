---
rg: 2
id: selector-free-fixed-radical-proof
kind: route
title: Read every transverse phase in the endpoint's central intersection
target: selector-free-transverse-completion-has-fixed-radical
requires:
  - full-q-masa-forgets-selectors-retains-branches
  - schur-complement-controls-relative-pauli-module
---

The ambient packet is class two, so for `g,h in E` the commutator `[g,h]`
lies in the ambient central subgroup `D` and also lies in `E`.  Assumption
`(SFT1)` therefore forces `[g,h] in <J>`.  Choose exponent vectors for the
noncentral generators of `E`.  Their commutator matrix consequently has
entries only `0` and the fixed marked bit `J`; it contains no coefficient of
any `z_i`.

After fixing `J=-1`, this is the same binary matrix on every selector sector.
Row reduction gives the same rank and the same radical subspace at every
`x`.  If `(SFT2)` gives two distinct radical lines, that fixed radical cannot
equal both.  Conversely, making a commutator matrix whose kernel follows
`v(x)` requires some entry to depend on `x`; in the group presentation that
entry is a nontrivial selector word.  Because it is a commutator of endpoint
elements, the word belongs to `E intersect D`, proving `(SFT3)`.
