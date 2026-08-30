---
rg: 2
id: ssa-solid-k-theory-proof
kind: route
title: The first-factor isomorphism inverts the Kunneth multiplication
target: ssa-kunneth-forces-solid-k-theory
requires: []
artifacts:
  - research/artifacts/stw99-xv-solid-ring-reduction-2026-08-30.md
---

**`K_1 = 0`** (unconditional; cited chain).  Toms--Winter's analysis
of strongly self-absorbing algebras shows a `K_1`-injective SSA
algebra has trivial `K_1` (the approximately inner flip makes `u ⊗ 1`
and `1 ⊗ u` homotopic, and self-absorption turns this into
`u ∼_h 1`); `K_1`-injectivity is automatic by Winter
(SSA ⟹ `Z`-stable) plus Jiang (`Z`-stable ⟹ `K_1`-bijective).

**Solidity.**  By strong self-absorption there is an isomorphism
`φ : D → D ⊗ D` approximately unitarily equivalent to the
first-factor embedding `ι₁ : d ↦ d ⊗ 1`; hence
`K_0(ι₁) : K_0(D) → K_0(D ⊗ D)`, `x ↦ x ⊗ [1]`, is an isomorphism.
The Künneth sequence for `(D, D)` in degree zero reads

```text
0 → K_0 ⊗ K_0  ⊕  K_1 ⊗ K_1 → K_0(D ⊗ D) → Tor(K_0, K_1) ⊕ Tor(K_1, K_0) → 0,
```

and with `K_1 = 0` it collapses to a natural isomorphism
`K_0(D) ⊗ K_0(D) ≅ K_0(D ⊗ D)`.  Define the ring multiplication
`m := K_0(ι₁)^{-1} ∘ (Künneth) : K_0 ⊗ K_0 → K_0`.  Then
`m(x ⊗ [1]) = x`, so `m` is a two-sided-unital multiplication with
unit `[1]` and is BIJECTIVE, being the composition of two
isomorphisms.  Commutativity: the flip automorphism of `D ⊗ D` is
approximately inner (standard for SSA algebras), hence acts trivially
on `K_0(D ⊗ D)`, and it interchanges `x ⊗ y` with `y ⊗ x` under
Künneth (no sign in even degree); associativity follows from
functoriality of Künneth against `ι₁ ⊗ id` vs `id ⊗ ι₁`, both
approximately unitarily equivalent to the same triple embedding
`D → D^{⊗3}`.

**Classification.**  A ring with `A ⊗_Z A ≅ A` via multiplication is
solid; Bousfield--Kan (Core of a ring, JPAA 1972) classify solid
rings as `Z[J^{-1}]`, `Z/n`, compatible products `Z[J^{-1}] × Z/n`
(`n` with prime factors in `J`), and their colimits.  A torsion-free
solid ring is `Z[J^{-1}]`.

**Model checks.**  `Z, O_∞ : K_0 = Z` ✓; UHF `M_{J^∞}` and
`M_{J^∞} ⊗ O_∞ : Z[J^{-1}]` ✓; `Q, Q ⊗ O_∞ : Q` ✓; `O_2 : 0` (the
zero ring is solid) ✓ — the known SSA list realizes exactly the
torsion-free solid rings that occur.
