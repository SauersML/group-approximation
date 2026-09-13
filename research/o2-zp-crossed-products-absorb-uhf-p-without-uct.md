---
rg: 2
id: o2-zp-crossed-products-absorb-uhf-p-without-uct
kind: claim
title: Every Z_p crossed product of O_2 is KK-equivalent to its M_(p^∞)-stabilization, with no UCT input
distinct_from:
  o2-zp-crossed-products-invert-p-in-kk: that is the ring-level fact that p is a unit of KK(C, C); this passes to the inductive limit C ⊗ M_(p^∞) and repairs the Barlak--Li absorption step.
  barlak-li-p-half-iff-zp-actions-fix-cartan: that imports Theorem 4.16; this supplies, without the UCT, the absorption that the proof of its (i) ⟹ (ii) uses.
---

**ESTABLISHED (derivation, no UCT input).**  Let `p` be prime,
`α : Z_p ↷ O_2` any action, and `C = O_2 ⋊_α Z_p`.

1. The unital embedding `ι : C → C ⊗ M_(p^∞)`, `c ↦ c ⊗ 1`, is a
   KK-equivalence.
2. If `α` is outer, then `C ≅ C ⊗ M_(p^∞)`.  This uses in addition the
   Kirchberg--Phillips theorem in its KK form: a unit-preserving KK-equivalence
   between unital Kirchberg algebras is induced by an isomorphism.  That theorem
   needs no UCT, but its number was not re-read here.  It also uses that `C` is a
   unital Kirchberg algebra for outer `α`, which Barlak--Li II derive in the
   proof of Theorem 4.12.

**Repair of the flagged step.**
`research/artifacts/uct-o2-cyclic-actions-2026-09-12.md` §3 marked as
unverified the step of Barlak--Li II Theorem 4.16, (i) ⟹ (ii), that applies
hypothesis (i) ("every separable nuclear `A` KK-equivalent to `A ⊗ M_(p^∞)`
satisfies the UCT") to `O_2 ⋊_α Z_p` before its UCT is known.  Item 1 is exactly
what that application needs, and it holds for every action.  So Theorem 4.16,
(i) ⟹ (ii), is sound as stated.  Its remaining ingredient, Corollary 4.15, is
applied after the UCT is known, where Kirchberg--Phillips may use it.

**Consequence for the UCT-support filter.**  For such `C`, `𝒫(C)` (see
`coprime-uhf-stabilizations-detect-uct`) is invariant under adding or removing
the prime `p`.  So if `C` fails the UCT, no member of `𝒫(C)` is `{p}` or
contains only `p`.

Proof: `o2-zp-crossed-products-absorb-uhf-p-without-uct-proof`.
