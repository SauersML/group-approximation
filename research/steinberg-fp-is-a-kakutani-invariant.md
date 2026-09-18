---
rg: 2
id: steinberg-fp-is-a-kakutani-invariant
kind: claim
title: Finite presentation of the Steinberg algebra is a Kakutani-equivalence invariant of ample groupoids, so quantum rigidity of Z^2 SFTs and premise (E′) are invariants of the groupoid, not of the coding or the acting group
requires:
  - sft-crossed-product-fp-iff-quantum-rigid
  - quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products
  - fp-crossed-products-force-finitely-presented-acting-group
  - fp-crossed-products-force-sft-over-any-group
distinct_from:
  determinism-closure-certifies-quantum-rigidity: that shows fault normals, and so the failure of determinism proofs, are invariant under conjugacy (block recodings); this shows quantum rigidity itself is invariant under Kakutani equivalence of the transformation groupoids, which also allows orbit-equivalence recodings and changes of transversal.
  sft-crossed-product-fp-iff-quantum-rigid: that equates finite presentation of the Z^2 crossed product with quantum rigidity for one coding; this transports that property between all groupoids Kakutani equivalent to it.
  boolean-inverse-monoid-finite-presentation-is-finite-type: that treats the Boolean inverse monoid, where finite presentation is cheap; this treats the Steinberg algebra, where finite presentation is the rigidity gate.
---

**ESTABLISHED** by `steinberg-fp-is-a-kakutani-invariant-proof` (lane bh-invent-03,
2026-09-18; elementary lane proof, not reviewed). Item 1 is a form of Morita invariance and is presumably
folklore; no priority is claimed for it. A search of main found no statement of items 1–3.

## Statement

`k` is a field, and algebras are unital associative `k`-algebras.

1. **Full corners.** Let `R` be an algebra and `f ∈ R` a **full** idempotent (`RfR = R`). Then `R` is finitely
   presented iff the corner `fRf` is. In particular `R` is finitely presented iff `M_n(R)` is.
2. **Kakutani invariance.** Let `𝒢`, `ℋ` be Hausdorff ample groupoids with compact unit spaces. Suppose they are
   Kakutani equivalent, i.e. `𝒢|_U ≅ ℋ|_W` for full clopen `U ⊆ 𝒢^(0)` and `W ⊆ ℋ^(0)`. Then `A_k(𝒢)` is finitely
   presented iff `A_k(ℋ)` is.
3. **Transformation groupoids.** Let `Λ ↷ X` and `Λ' ↷ X'` be actions of finitely generated groups on Cantor sets,
   with Kakutani equivalent transformation groupoids. Continuously orbit equivalent topologically free actions
   qualify. Recall `A_k(Λ ⋉ X) = LC(X, k) ⋊ Λ`.
   - (a) **`Z^2`.** If `Λ = Λ' = Z^2` and `X, X'` are SFTs, then `X` is quantum rigid iff `X'` is.
   - (b) **Change of group.** If `Λ` is finitely presented, `X` is a quantum rigid SFT and `X'` is a subshift over
     `Λ'`, then `LC(X', k) ⋊ Λ'` is finitely presented. Hence `Λ'` is finitely presented and `X'` is of finite type.
   - (c) **Premise (E′)** of `boone-higman-via-leavitt-units-of-rigid-topologically-free-sfts` asks for a finitely
     presented `LC(X, F_2) ⋊ Λ`. That is a property of the Kakutani class of `Λ ⋉ X`, together with the
     requirement `G ≤ Λ`.

## Why it matters

- **Rigidity lives in the groupoid.** Quantum rigidity was defined through site idempotents of one coding over
  one group. Item 3(a) says it is an invariant of the groupoid's Kakutani class. So a G2 lane may test it on any
  model in that class. Two useful kinds of model:
  - a transversal of different shape, such as the supertile corners of a self-similar tiling, or a return-time
    tower;
  - any orbit-equivalent recoding, not only block recodings.
- **Negative certificates transport too.** A wall certificate or non-commuting family in one model refutes
  rigidity of every Kakutani-equivalent `Z^2`-SFT, including recodings not reachable by block maps.
- **The acting group is only a choice of generating bisections.** By 3(b), finite presentation of the acting
  group and the finite-type property are forced on every subshift model of the Kakutani class of a rigid SFT
  over a finitely presented group.

## Lesson for general BH

The master route's gate (E′)/G2 asks for a finitely presented Steinberg algebra, and that is a Morita-type
invariant of the groupoid. So the gate sees only the groupoid up to Kakutani equivalence: neither the coding,
nor the transversal, nor even the group whose translations generate it. Constructions should therefore be
chosen and checked at the groupoid level. The input `G` constrains only which full group must contain it.
The companion node `outer-extensions-of-fp-steinberg-groupoids-need-no-rigidity` says where the rigidity
must then be paid.
