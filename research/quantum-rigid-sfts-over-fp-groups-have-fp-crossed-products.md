---
rg: 2
id: quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products
kind: claim
title: Over any finitely presented acting group, a quantum rigid subshift of finite type has a finitely presented crossed-product algebra
distinct_from:
  sft-crossed-product-fp-iff-quantum-rigid: that is the two-way equivalence for Lambda = Z^2; this is the "if" direction over every finitely presented group, with no freeness, minimality or amenability, by the same universal-algebra argument with the relators of Lambda added.
  fp-v-times-subshift-full-groups-force-quantum-rigidity: that derives quantum rigidity from finite presentation of the V-times full group; this turns quantum rigidity back into finite presentation of the crossed-product algebra, so the two compose to P2 implies ring finite presentation.
  quantum-rigidity-passes-to-sub-sfts: that passes rigidity to sub-SFTs over Z^2; this converts rigidity into a finite presentation over any finitely presented group.
---

**ESTABLISHED (unreviewed).** No novelty is claimed: it is the "if" half of
`sft-crossed-product-fp-iff-quantum-rigid` with `Z^2` replaced by an arbitrary finitely presented
group. The proof is self-contained.

## Statement

Let `Λ = <S | R>` be finitely presented, `S` finite symmetric, `k` a field, `A` a finite alphabet and
`X ⊆ A^Λ` a nonempty SFT with forbidden patterns on `B_r`. Use the notion of `D`-quantum rigidity
over `k` from `fp-v-times-subshift-full-groups-force-quantum-rigidity` (conditions Q1-Q3). If `X` is
`D`-quantum rigid over `k` for some `D >= r`, then `B = LC(X, k) ⋊ Λ` is finitely presented as a
`k`-algebra.

With `fp-crossed-products-force-finitely-presented-acting-group` and
`fp-crossed-products-force-sft-over-any-group`: for fg `Λ`, if `B` is fp then `Λ` is fp and `X` is an
SFT. Conversely, if `Λ` is fp and `X` is a quantum rigid SFT, then `B` is fp. Whether fp `B` forces
quantum rigidity outside `Z^2` is not settled here.

**Idea.** Present `B` by the relators of `Λ`, local commutation of the letter idempotents up to
distance `2D`, and the forbidden `B_D` patterns. Rigidity, applied to the universal algebra acting on
itself by left multiplication, makes all translated idempotents commute. Compactness then identifies
their span with `LC(X, k)`.

## Consequence

**P1 and P2 give a finitely presented crossed product.** Take `Λ`, `X` from P1
(`decidable-groups-embed-in-fp-groups-with-minimal-free-sft`). P2 makes `A(T)` fp. By
`v-times-ample-full-groups-are-generated-by-transpositions`, `A(T) = F(T)`, which contains every
`t_s` and `e_a`. So `fp-v-times-subshift-full-groups-force-quantum-rigidity` makes `X` quantum rigid
over `F_2`, and this claim makes `LC(X, F_2) ⋊ Λ` fp. This is the input of
`decidable-groups-lie-in-fp-free-minimal-crossed-products`.

DERIVATION
quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products-proof
