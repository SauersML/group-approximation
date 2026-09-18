---
rg: 2
id: quantum-rigidity-is-product-stable
kind: claim
title: The product of two subshifts of finite type over a product group is quantum rigid iff both factors are, and it is free and minimal iff both factors are, so uncoupled products create no faults
distinct_from:
  quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products: that turns rigidity of one SFT into finite presentation of its crossed product; this compares rigidity of a product SFT with rigidity of its factors.
  fp-v-times-subshift-full-groups-force-quantum-rigidity: that defines quantum rigidity over an arbitrary group and derives it from finite presentation of the full group; this proves a closure property of the notion itself.
  permutive-triangle-sfts-are-quantum-rigid: that proves rigidity of one class of Z^2-SFTs by propagating determinism; this proves rigidity of products from rigidity of the factors, by forcing constancy along the other factor.
---

**ESTABLISHED** through `quantum-rigidity-product-stability-proof` (lane proof, elementary; not
independently reviewed; no priority claimed).

## Setting

Quantum rigidity over a group is as in `fp-v-times-subshift-full-groups-force-quantum-rigidity`:
- `D`-quantum families satisfy (Q1) partitions of unity, (Q2) commutation within distance `2D`,
  and (Q3) vanishing on `B_D`-patterns that do not occur;
- `X` is `D`-quantum rigid over a field `k` if every `D`-quantum family over `k` commutes.

Let `Λ_1 = ⟨S_1⟩` and `Λ_2 = ⟨S_2⟩` be finitely generated groups. Give `Λ = Λ_1 × Λ_2` the word
metric of `S_1 ∪ S_2`, so that `d((g,h),(g',h')) = d_1(g,g') + d_2(h,h')`.

Let `X ⊆ A^(Λ_1)` and `Y ⊆ B^(Λ_2)` be nonempty SFTs. Their **product** is

```text
X ⊠ Y = { z = (x̃, ỹ) ∈ (A × B)^Λ : x̃(g,h) = x(g), ỹ(g,h) = y(h) for some x ∈ X, y ∈ Y },
```

with `Λ` acting diagonally, so that `X ⊠ Y ≅ X × Y` with `(λ_1, λ_2)` acting as `λ_1 × λ_2`.

## Statement

1. **Finite type.** `X ⊠ Y` is an SFT over `Λ`. It is cut out by four local rules:
   - `x̃(g,h) = x̃(g,hs)` for `s ∈ S_2`;
   - `ỹ(g,h) = ỹ(gs,h)` for `s ∈ S_1`;
   - the forbidden patterns of `X` on each row `Λ_1 × {h}`;
   - the forbidden patterns of `Y` on each column `{g} × Λ_2`.
2. **Dynamics.** `Λ` acts freely on `X ⊠ Y` iff `Λ_i` act freely on `X` and `Y`. It acts
   minimally iff both factor actions are minimal.
3. **Rigidity.** Let `D ≥ 1`.
   - If `X` and `Y` are `D`-quantum rigid over `k`, then so is `X ⊠ Y`.
   - Conversely, if `X ⊠ Y` is `D`-quantum rigid over `k`, then so are `X` and `Y`.
4. **Rings.** `LC(X ⊠ Y, k) ⋊ Λ ≅ (LC(X, k) ⋊ Λ_1) ⊗_k (LC(Y, k) ⋊ Λ_2)`. So, with
   `quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`, rigid factors over finitely
   presented groups give a finitely presented crossed product over the one-ended group
   `Λ_1 × Λ_2`.

## Consequences for the master route

- **Faults come from unconstrained directions, not from products.** A product of rigid factors
  is rigid. The independent faults of uncoupled products arise only when some factor is
  non-rigid, for example a direction carrying no constraint (a full-shift or trivial factor).
  So the design rule "couple product factors" of the master route
  (`research/artifacts/gq-bh-synthesis-master-route.md`, §2) is needed for **existence**
  (G1): it transports `Λ_0`-aperiodicity into an SFT. It is not needed for **rigidity**
  (G2).
- **G2 splits along products.** A rigid free minimal SFT over one infinite group `H`, times one
  over `Λ_0`, is a rigid free minimal SFT over the one-ended group `Λ_0 × H`.
  - So the "single most informative object" of the synthesis can be sought factor by factor.
  - For a general decidable `Λ_0` there need not be any SFT at all over `Λ_0` (Cohen:
    one-endedness is necessary). There the coupled simulation of G1 is unavoidable, and its
    rigidity is the open question (h) of the lane table.
- **Calibration.** Products of permutive-triangle SFTs (`permutive-triangle-sfts-are-quantum-rigid`)
  and of Ledrappier's shift are rigid over `Z^2 × Z^2 = Z^4`. None of these is free.

## Lesson for general BH

Quantum rigidity is a local property that factors through products. The obstruction to rigid
codings is never the product structure of `Λ = Λ_0 × H`. It is either a direction with no
constraint, or a coupling that transports freeness from `Λ_0`. The crux G2 is therefore
exactly: **rigidity of the coupling layer**. A route that finds a rigid free minimal SFT over
`H`, and codes `Λ_0` into it deterministically, has nothing further to prove on the product
side.
