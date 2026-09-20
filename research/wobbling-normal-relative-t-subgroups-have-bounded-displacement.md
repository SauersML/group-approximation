---
rg: 2
id: wobbling-normal-relative-t-subgroups-have-bounded-displacement
kind: claim
title: "A normal subgroup with relative property (T) in a subgroup of the wobbling group of Z has uniformly bounded displacement, so all its orbits have boundedly many points"
distinct_from:
  wobbling-normal-relative-t-subgroups-are-locally-finite: that bounds the orbits of each finitely generated subgroup of H by a constant depending on its generators, and bounds bad points only in density; this bounds the displacement of every element of H by one constant, with no finite generation of H or of Gamma
  heisenberg-not-in-wobbling-groups-of-quadratic-growth-graphs: that is a growth obstruction for one nilpotent group on other graphs; this is a Kazhdan-projection bound on Z for normal relative-(T) subgroups
---

Let `W(Z)` be the group of bijections `g` of `Z` with finite displacement
`d(g) = sup_n |g(n) − n|`. Let `Γ ≤ W(Z)` be any subgroup (not necessarily finitely generated),
and let `H ⊴ Γ` be normal with `(Γ, H)` having relative property (T).

**Statement.** Let `(Q, ε)` be a relative Kazhdan pair for `(Γ, H)`: `Q ⊂ Γ` is finite, `ε > 0`,
and every unitary representation of `Γ` with a unit vector `ξ` satisfying
`max_{q∈Q} ‖qξ − ξ‖ < ε` has a nonzero `H`-invariant vector. Put `D = max(1, max_{q∈Q} d(q))` and

`B = ⌊24 D² / ε²⌋ + 1`.

Then:

1. every `h ∈ H` has `d(h) < B`;
2. every `H`-orbit in `Z` has at most `2B − 1` points, and lies in an interval of length `< 2B`;
3. `H` embeds in the product `∏_O Sym(O)` over its orbits, each factor of order at most `(2B−1)!`.
   In particular `H` has finite exponent dividing `lcm(1, …, 2B−1)`, and it is locally finite.

A relative Kazhdan pair exists for every relative-(T) pair of a countable group. This is the
standard direct-sum argument, and Step 1 of `wobbling-normal-relative-t-locally-finite-proof`
is a version of it.

The same holds for `Γ ≤ [[X]]`, with `X` the full shift. Use the embedding `[[X]] → W(Z)` along a
dense orbit from Step 6 of `wobbling-normal-relative-t-locally-finite-proof`.

Proof in `wobbling-normal-relative-t-bounded-displacement-proof`.
