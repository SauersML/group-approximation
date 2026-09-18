---
rg: 2
id: deterministic-extensions-of-rigid-sfts-are-rigid
kind: claim
title: A finite-fibre extension of a quantum rigid SFT whose fibre letter is transported deterministically along a monoid-generating set of directions is quantum rigid, and free when the base is free
distinct_from:
  quantum-rigidity-is-product-stable: that proves rigidity of products X × Y from rigidity of both factors; this proves rigidity of extensions whose extra layer has no freedom beyond one fibre value, including cocycle, copy and constancy layers.
  permutive-triangle-sfts-are-quantum-rigid: that propagates determinism inside one layer of a Z^2-SFT to get rigidity outright; this transports a fibre layer over an arbitrary rigid base, over any finitely generated group.
---

**ESTABLISHED** through `deterministic-extension-rigidity-proof` (lane proof, elementary; not
independently reviewed; no priority claimed).

## Setting

Quantum rigidity is as in `fp-v-times-subshift-full-groups-force-quantum-rigidity`. Let
`Λ = ⟨S⟩` be finitely generated, `Y ⊆ B^Λ` an SFT, `F` a finite set, and `X ⊆ (B × F)^Λ` an
SFT whose `B`-projection lies in `Y`. Write points of `X` as `(y, f)`.

**Deterministic transport.** Let `S' ⊆ S ∪ S^-1` generate `Λ` as a monoid. For each `s ∈ S'` fix
a finite window `W_s ⊆ Λ` and a map `θ_s : B^(W_s) × F → F`. The transport rule is

```text
f(zs) = θ_s( (w ↦ y(zw))_(w ∈ W_s), f(z) )   for all (y, f) ∈ X, z ∈ Λ, s ∈ S'.
```

Let `R` bound the lengths of `s ∈ S'` and of the elements of all `W_s`.

## Statement

1. **Rigidity.** If `Y` is `D_0`-quantum rigid over `k`, then `X` is `D`-quantum rigid over `k`
   for every `D ≥ max(D_0, R)`.
2. **Freeness.** If `Λ` acts freely on `Y`, it acts freely on `X`.
3. **Fibres.** A point of `X` is determined by its `B`-projection and its fibre letter at one
   site, so `X → Y` is at most `|F|`-to-one.

Minimality of `X` is not automatic. For finite-group cocycle extensions it is the usual
ergodicity condition on the cocycle, not examined here.

## Instances

- **Constancy layers** (`θ_s(p, f) = f`). These are the inflation layers of
  `quantum-rigidity-is-product-stable`, and the "copy" layers of simulation constructions,
  which carry a value unchanged along a set of directions.
- **Finite-group cocycle extensions** (`F = K` a finite group, `θ_s(p, f) = f · c_s(p)`). This
  is how torsion or flux decorations are added to a base shift.
- **Reversible dynamics along a spanning set of directions.** A layer that evolves bijectively
  and locally along every direction in `S'` is covered.
  - A reversible cellular-automaton time direction alone is not covered unless `S'` still
    generates `Λ` as a monoid.

## Lesson for general BH

In a coded SFT, non-rigidity can only come from **genuine freedom**: a layer that is not
transported deterministically from a rigid base. Deterministic layers (constancy, copying,
finite-group flux, bijective local transport) inherit rigidity, over any group. For the master
route's G2 this localizes the whole crux in the non-deterministic layers of a construction.
- In a simulation over `Λ_0 × H`, those are the hierarchical skeleton over `H`, and the input
  layer carrying the simulated `Λ_0`-subshift.
- Computation layers are covered when they are driven by reversible, deterministic transport
  along a monoid-generating set of directions.
