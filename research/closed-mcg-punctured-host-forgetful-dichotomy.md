---
rg: 2
id: closed-mcg-punctured-host-forgetful-dichotomy
kind: claim
title: A copy of a finite-index subgroup of a closed-surface mapping class group in a punctured or bordered mapping class group either splits a Birman sequence of genus at least g or has a nontrivial free or surface-group forgetful kernel
distinct_from:
  closed-mcgs-virtually-embed-in-punctured-mcgs: that asks whether such a copy exists; this sorts every copy, if one exists, into two shapes by forgetting punctures one at a time.
  closed-mcg-in-asymptotic-mcg-is-bordered-or-infinite-in-v: that sorts copies inside Aramayona--Funar asymptotic mapping class groups by their image in V; this sorts copies inside finite-type punctured or bordered mapping class groups by forgetful kernels.
---

**ESTABLISHED.** Let `g ≥ 3` and let `L ≤ Mod(S_g)` have finite index. Let `Σ′`
be an orientable finite-type surface of genus `h` with `n` punctures and `b`
boundary components, where `m := n + b ≥ 1`. Let `ι: L → Mod^±(Σ′)` be injective.
Write `S_(h,j)` for the closed genus-`h` surface minus `j` points, and
`PMod(S_(h,j))` for its orientation-preserving mapping classes fixing each
puncture.

**0. Normal form.** There are a finite-index subgroup `L′ ≤ L` and an injective
homomorphism `ρ′: L′ → PMod(S_(h,m))`. For `0 ≤ j ≤ m`, write `ρ′_j` for `ρ′`
followed by forgetting all punctures but the first `j`. So `ρ′_m = ρ′`,
`ρ′_0` lands in `Mod(S_h)`, and `ρ′_1` lands in `Mod(S_h, ∗) = PMod(S_(h,1))`.

Exactly one of the following holds.

**A. Closed shape: `ρ′_0` is injective.** Then:
- `h ≥ g`;
- `ρ′_1` lifts `ρ′_0` through the forgetful map `Mod(S_h, ∗) → Mod(S_h)`;
- so the Birman exact sequence `1 → π_1(S_h) → Mod(S_h, ∗) → Mod(S_h) → 1`
  splits over the subgroup `ρ′_0(L′) ≅ L′`.

**B. Forgetful-kernel shape: `ρ′_0` is not injective.** Let `j` be the largest
index with `ρ′_j` not injective. Then:
- `0 ≤ j < m` and `χ(S_(h,j)) < 0`; so `j ≥ 3` if `h = 0`, and `j ≥ 1` if
  `h = 1`;
- `K := ker ρ′_j` is a nontrivial normal subgroup of `L′`;
- `ρ′_(j+1)` maps `K` isomorphically onto `ρ′_(j+1)(L′) ∩ Push(π_1(S_(h,j)))`,
  where `Push(π_1(S_(h,j)))` is the kernel of forgetting the last puncture;
- `K` is free if `j ≥ 1`, and isomorphic to a subgroup of `π_1(S_h)` if
  `j = 0`; in either case `K` has no subgroup `Z^2`;
- `K` is infinite and not cyclic;
- `L′/K ≅ ρ′_j(L′) ≤ PMod(S_(h,j))`.

**Converse for A.** Take `h ≥ 2`, an injective `ρ_0: L′ → Mod(S_h)` for some
finite-index `L′ ≤ Mod(S_g)`, and a lift `ρ_1: L′ → Mod(S_h, ∗)`. Then `ρ_1` is
injective and lands in `PMod(S_(h,1))`. So shape A alone would prove
`closed-mcgs-virtually-embed-in-punctured-mcgs`.

**Consequences.**
- Hosts of genus `h ≤ 1` always have shape B, because A needs `h ≥ g ≥ 3`.
- Shape A is impossible when `h = g`, and whenever `ρ′_0` is a covering lift
  up to conjugation: `covering-lift-copies-of-closed-mcgs-have-no-marked-lift`.
- Hosts of genus `h ≤ 1` force virtual surjections onto `Z`:
  `closed-mcg-low-genus-host-gives-infinite-abelianization`.

**Scope.**
- `ι` is only assumed injective. No geometric hypothesis is made about it.
- Shape B is not excluded in any genus. Shape A is excluded only in the cases
  listed above.

The derivation is `closed-mcg-punctured-host-forgetful-dichotomy-proof`.
