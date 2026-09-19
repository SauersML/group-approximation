---
rg: 2
id: clifford-bernoulli-central-summands
kind: claim
title: The Bernoulli and Clifford crossed products are the two central summands of one lamp group
distinct_from:
  kun-thom-clifford-crossed-product-ce: that asks whether the Clifford summand is Connes embeddable; this is the structural identity that places it and the Bernoulli summand inside one group von Neumann algebra, and it decides neither
  kun-thom-clifford-radical-phase: that is the sofic-radical phase detector inside the Clifford crossed product; this is a decomposition of the ambient algebra with no radical or phase in it
artifacts:
  - notes/TRUE_CLIFFORD_LAMP_CENTRAL_SUMMANDS.md
---

Let `X` be a `G`-set and let the **Clifford lamp group** be

```text
C(X) = ⟨ c_x (x ∈ X), z | z² = 1, z central, c_x² = 1, c_x c_y = z c_y c_x (x ≠ y) ⟩,
```

a central `ℤ/2`-extension of `⊕_X ℤ/2` on which `G` acts by `g·c_x = c_(gx)`,
`g·z = z`. Put `W̃ = C(X) ⋊ G`, so `W̃/⟨z⟩ = W`. Then `p_± = (1 ± z)/2` are
`G`-fixed central projections of trace `1/2` and

```text
L(W̃) = ( L^∞({±1}^X) ⋊ G ) ⊕ ( Cl(X) ⋊ G ).
```

Consequences:

1. `W̃` is hyperlinear **iff both** `L(W) = M_KT` and `Cl(X) ⋊ G` are Connes
   embeddable, so jointly they are hyperlinearity of the single group `W̃`.
   They are **not** independent, however, and an earlier version of this line
   said they were: `clifford-ce-implies-bernoulli-ce` proves that Connes
   embeddability of `Cl(X) ⋊ G` implies Connes embeddability of `M_KT`, by
   diagonal doubling `c_x ⊗ c_x` inside a tensor square
   (`TRUE_DOUBLE_CLIFFORD_KUN_THOM_REDUCTION.md`, `(DCK11)`–`(DCK14)`) — a
   cross-summand argument the direct-sum picture does not see. Hence
   `kun-thom-clifford-crossed-product-ce` is by itself equivalent to
   hyperlinearity of `W̃`, and it implies `hyperlinear-wreath-model`. No
   converse is known.
2. `W` is hyperlinear as soon as `W̃` is, although `W` is a **quotient** of
   `W̃`. Hyperlinearity does not pass to quotients in general; it does here
   because a central `ℤ/2` makes the quotient's group algebra a direct summand
   rather than a quotient algebra.
3. `diagonal-normalizer-rigidity` and `invariant-cartan-completion` apply to
   the Bernoulli summand **only**. Their engine is the abelian diagonalization
   lemma, and `Cl(X)` is a `II₁` factor, so no conjugation puts it in a
   diagonal ultraproduct. Kun–Thom Definition 2.2 and Corollary D are
   statements about p.m.p. actions and have no purchase on the Clifford
   summand; it is obstructed only through the repository's own radical-phase
   detector.
4. Conversely Kun–Thom Theorem A's endgame transcribes verbatim to `W̃`, since
   `Γ` fixes the base coset and distinct Majoranas are distinct: `W̃` is
   nonsofic for the same reason `W` is.
