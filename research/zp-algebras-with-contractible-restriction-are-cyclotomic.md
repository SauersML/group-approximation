---
rg: 2
id: zp-algebras-with-contractible-restriction-are-cyclotomic
kind: claim
title: A Z_p-algebra whose underlying algebra is KK-contractible has an equivariant KK-ring over Z[zeta_p, 1/p]
distinct_from:
  order-p-automorphism-kk-cyclotomic-structure: that is the dual statement on the crossed product side, about KK(C, C) and the dual automorphism; this is the equivariant statement on the original algebra, about KK^G(D, D) and the representation ring.
---

**ESTABLISHED (derivation, no UCT input).**  Let `p` be prime, `G = Z/p`, and
`χ ∈ R(G) = KK^G(C, C)` a generating character.  Let `D` be a separable
`G`-C\*-algebra with `Res^G_1 D ≃_KK 0`.  Then in `S = KK^G(D, D)`, acted on by
`R(G)` through exterior products:

1. `1 − χ` acts invertibly;
2. the regular representation `ρ = 1 + χ + ⋯ + χ^(p−1)` acts as `0`;
3. `p` acts invertibly.

So `S`, and every `KK^G(D, E)` and `KK^G(E, D)`, is a module over
`Z[ζ_p, 1/p]` with `ζ_p ↦ χ`.  Equivalently, the augmentation ideal of `R(G)`
acts invertibly, so the Atiyah--Segal completion of `KK^G(D, E)` vanishes.

Applied to `D = (O_2, α)` for any action `α`, this is the equivariant face of
`o2-zp-crossed-products-invert-p-in-kk`.  Its K-theoretic shadow is the normal
form in `bootstrap-zp-actions-realize-every-cyclotomic-k-module`.  It is
probably known to specialists, for example in the Arano--Kubota treatment of
the completion theorem.  That was not checked, and no priority is claimed.

Proof: `zp-algebras-with-contractible-restriction-are-cyclotomic-proof`.
