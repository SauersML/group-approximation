---
rg: 2
id: cantor-power-function-modules-are-v-acyclic
kind: claim
title: For every j >= 1 the V-module of locally constant integer functions on the j-th power of the Cantor set is V-acyclic
---

Let Thompson's group `V` act diagonally on `C^j`, where `C` is the Cantor set,
and let `C(C^j, Z)` be the locally constant integer-valued functions. The claim
is `H_p(V; C(C^j, Z)) = 0` for all `p ≥ 0` and all `j ≥ 1`.

Rationally this holds: Lemma B3 of
`research/artifacts/zp-braided-v-rational-acyclicity-2026-09-13-part2.md`.
Integrally it would give integral acyclicity of the braided Thompson group
`bV` (route `braided-thompson-group-bv-is-acyclic-from-cantor-modules`), which
answers Zaremsky Problem 2.9 affirmatively.

## Attempts

- Degree 0 holds integrally: the coinvariants vanish by the subdivision identity
  `1_U = 1_{U_0} + 1_{U_1}` and transitivity of `V` on boxes of pairwise disjoint
  cones with nonempty complement (`f = 2f`), plus the covering case handled by
  one subdivision.
- Labelled Thompson route (part 2): `V(Z^j) = C(C, Z^j) ⋊ V` is acyclic
  (Palmer–Wu, Theorem 2.6), and `C(C^j, Z)` is the multilinear summand of row
  `j` of its Lyndon–Hochschild–Serre spectral sequence. Integer scalings only
  bound differentials leaving that summand by the fixed divisor of `x^ν − x^μ`,
  which can be 2. A chain-level formality `Λ^* A ≃ C_*(BA)` natural in
  `V`-equivariant maps would kill all differentials. Totaro-type examples of
  non-degenerating spectral sequences for split extensions by `Z^n` show this
  needs a real argument, not naturality alone.
- Mod-ℓ route: for coefficients `F_ℓ`, integer units mod `ℓ` separate degrees only
  modulo `ℓ − 1`, and not at all for `ℓ = 2`. The case `ℓ = 2` is the crux.
- Groupoid route: `H_*(V; C(C^j, Z))` is the homology of the transformation
  groupoid `C^j ⋊ V`. A version of Xin Li's topological full group theorem with
  such coefficient modules would decide it.
