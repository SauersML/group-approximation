---
rg: 2
id: ssa-solid-k-theory-proof
kind: route
title: The first-factor isomorphism inverts the Kunneth multiplication
target: ssa-kunneth-forces-solid-k-theory
requires:
  - ssa-self-kunneth-exact-k-theory-criterion
artifacts:
  - research/artifacts/stw99-xv-solid-ring-reduction-2026-08-30.md
  - research/artifacts/ssa-self-kunneth-xiv2-audit-2026-08-31.md
---

**`K_1 = 0` under self-Kunneth.** By
`ssa-self-kunneth-exact-k-theory-criterion`, the first-factor
K-isomorphism factors through the external product and forces
`x |-> x tensor [1]` to be an isomorphism onto the graded tensor square.
The odd summands then force `K_1(D)=0`. Automatic `K_1`-injectivity of SSA
algebras is not K-group vanishing and is not used here.

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

**Torsion-freeness.**  Run Künneth in degree one: the tensor part
`K_0 ⊗ K_1 ⊕ K_1 ⊗ K_0` vanishes since `K_1 = 0`, so the sequence
collapses to a natural isomorphism
`K_1(D ⊗ D) ≅ Tor(K_0(D), K_0(D))` (the degree-one Tor term is
`⊕_{i+j=0} Tor(K_i, K_j) = Tor(K_0, K_0)`).  The first-factor
embedding is a `K_1`-isomorphism, so `K_1(D ⊗ D) ≅ K_1(D) = 0`,
whence `Tor(K_0, K_0) = 0`; for an abelian group this means the
torsion subgroup vanishes.

**Classification.**  A ring with `A ⊗_Z A ≅ A` via multiplication is
solid; Bousfield--Kan (Core of a ring, JPAA 1972) classify solid
rings as `Z[J^{-1}]`, `Z/n`, compatible products `Z[J^{-1}] × Z/n`
(`n` with prime factors in `J`), and their colimits.  A torsion-free
solid ring is `Z[J^{-1}]`.

**Model checks.**  `Z, O_∞ : K_0 = Z` ✓; UHF `M_{J^∞}` and
`M_{J^∞} ⊗ O_∞ : Z[J^{-1}]` ✓; `Q, Q ⊗ O_∞ : Q` ✓; `O_2 : 0` (the
zero ring is solid) ✓ — the known SSA list realizes exactly the
torsion-free solid rings that occur.
