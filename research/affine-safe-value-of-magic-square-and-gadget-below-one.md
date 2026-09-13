---
rg: 2
id: affine-safe-value-of-magic-square-and-gadget-below-one
kind: claim
title: The affine-safe value of the magic-square AND gadget is bounded below one by an explicit constant
distinct_from:
  matrix-conj-forces-unsafe-support: that shows every perfect trace of the gadget has affine-unsafe support in the AND context; this is the quantitative form, an explicit constant gap on the value of every affine-safe strategy and every canonical-corner pushforward, with no perfect model assumed.
  jnvwy-active-output-has-no-affine-safe-perfect-model: that excludes perfect affine-safe models of the recursive JNVWY output; this is a value gap for one fixed finite gadget and needs no compression machinery.
  near-perfect-bcs-strategy-gives-synchronous-relator-state: that is the general strategy-to-relator-state interface used as an input here; this is the application to the fixed magic-square AND gadget together with the affine-support analysis.
artifacts:
  - research/artifacts/affine-support-value-gap-2026-09-13.md
---

**ESTABLISHED** by `magic-square-and-gadget-affine-value-proof`. Not
independently reviewed. No novelty is claimed: it combines the fixed magic
square AND gadget of `matrix-conj-forces-unsafe-support` with the relator-state
modulus of `near-perfect-bcs-strategy-gives-synchronous-relator-state` and an
elementary count of the affine subsets of the AND graph.

## The gadget

Let `B_MS^AND` be the Boolean constraint system of
`matrix-conj-forces-unsafe-support`: the Mermin--Peres magic square on the
nine involutions `A..I`, with the listed row/column commutations and the row
and column parity products, together with one adjoined involution `Y` and one
context `c_AND=(A,B,Y)` whose allowed set is the graph of Boolean AND,

```text
Allowed_(c_AND) = {000,010,100,111}.                               (V0)
```

Its maximum context size is `M=3` and it has a fixed finite constraint count
`k`, so the modulus of `near-perfect-bcs-strategy-gives-synchronous-relator-state`
is the fixed number

```text
T = 4^(M+2) k M^3 = 4^5 * 27 * k.                                  (V1)
```

There is a further fixed constant `C0 >= 1`, the number of listed relations
combined in the derivation `(UTC4)` of the anticommutations `AE=-EA`,
`BD=-DB` and the conjugation `G(AB)G^{-1}=-AB` with `G=AD`. Put

```text
c* = 1 / (9 C0 T).                                                 (V2)
```

## Statement

Let `S` be any synchronous (tracial commuting-operator) strategy for
`B_MS^AND` with game value `1-eps`, and let `tau` be its synchronous state.

**(VA) Affine-safe strategies.** If `S` is affine-safe, meaning
`affineHull(supp(tau_c)) subseteq Allowed_c` in every context `c`, then

```text
eps >= 4 / (9 C0 T).                                               (VA)
```

**(VB) Canonical-corner pushforwards.** Let `D` be any affine decoder from
`B_MS^AND` into a central-character group corner `p_omega C*(Gamma) p_omega`
in the sense of `group-corner-exact-compilers-force-source-affine-safety`
(GC5), and let `S` be the decoded strategy obtained from the **canonical
corner trace** `tau_omega` of (GC3), whose context answers are uniform on the
coset `X_A(omega)` by (CS1). Then the decoded value satisfies

```text
eps >= c* = 1 / (9 C0 T).                                          (VB)
```

Both `4/(9 C0 T)` and `c*` are fixed positive constants of the single finite
gadget, independent of any source it is adjoined to and of any compiler
family. So for `B_tilde = B_0 disjoint-union B_MS^AND` of
`matrix-conj-forces-unsafe-support`, the affine-safe value and the
canonical-corner-pushforward value of `B_tilde` are both at most `1-c*`, since
a disjoint-union value is at most the value of each component and affine
safety restricts to the component.

## Why

The magic-square subgame forces the `(A,B)` marginal of `tau` to be within
`(3/8)C0 sqrt(2 T eps)` of uniform on its four joint atoms. Affine safety puts
at most two of those four atoms in the support (the AND graph `(V0)` has no
affine subset of size greater than two), so at least two atoms of mass close
to `1/4` are missing, giving `(VA)`. A canonical-corner pushforward is uniform
on a flat, which either misses an allowed atom (again `(VA)`) or is the whole
cube with every atom of mass `1/8 != 1/4`, giving `(VB)`. The proof route
carries out the estimates.

## Consequence

This is the quantitative upgrade requested at gap (iii-c) of
`research/artifacts/ce-only-decoder-floor-map-2026-09-13.md`: an explicit
constant `s < 1` below the value of affine strategies for an affine-unsafe
source. It feeds `constant-gap-affine-corner-compiler-forces-nonhyperlinear`.
