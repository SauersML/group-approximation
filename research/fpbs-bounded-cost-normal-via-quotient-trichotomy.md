---
rg: 2
id: fpbs-bounded-cost-normal-via-quotient-trichotomy
kind: route
title: Split the infinite quotient into infinite-order, locally finite and finitely generated torsion cases after removing an amenable outer kernel
target: fpbs-normal-subgroup-bounded-cost-fixed-price-one
requires:
  - fpbs-bounded-cost-outer-cyclic-extension-price-one
  - fpbs-bounded-cost-locally-finite-outer-price-one
  - fpbs-bounded-cost-fg-torsion-quotient-price-one
  - fpbs-amenable-outer-kernel-forces-price-one
  - fpbs-wq-normal-price-one-subgroup-forces-price-one
artifacts:
  - research/artifacts/fpbs-normal-bounded-cost-quotient-trichotomy-2026-09-16.md
---

Written derivation. It is Proposition R in Section 3 of the linked artifact.

**Setup.**
- Let `N ◁ Gamma` be infinite, and suppose every free p.m.p. action of `N` has
  cost at most `K`. Call this hypothesis (H).
- Let `Q = Gamma/N` be infinite, with `pi : Gamma -> Q`.
- Let `rho : Q -> Out(N)` be the outer action, and `Q_0 = ker rho`.

**Two facts used throughout.**
- **(F1) Restriction.** For `A <= Q`, the outer kernel of `pi^-1(A)/N = A`
  is `A ∩ Q_0`.
- **(F2) wq-normality.** Every `Lambda` with `N <= Lambda <= Gamma` is
  wq-normal in `Gamma`.
  - Take a proper `K ⊇ Lambda` and any `g notin K`.
  - Then `g K g^-1 ∩ K ⊇ N`, which is infinite.
  - So once `Lambda` has fixed price one,
    `fpbs-wq-normal-price-one-subgroup-forces-price-one` gives `Gamma` fixed
    price one.

**Case 0.** Suppose `Q_0` contains an infinite amenable subgroup. Then
`fpbs-amenable-outer-kernel-forces-price-one` concludes. From now on assume it
contains none.

The infinite group `Q` falls into exactly one of three cases.

**(a) `Q` has an element `q` of infinite order.**
1. **`<q> ∩ Q_0 = 1`.** Otherwise `Q_0` contains an infinite cyclic subgroup,
   which is amenable.
2. **The preimage is a semidirect product.**
   - Pick `gamma in pi^-1(q)` and set `phi = c_gamma` restricted to `N`.
   - The map `(u,k) -> u gamma^k` is an isomorphism
     `N semidirect_phi Z -> Lambda = pi^-1(<q>)`.
3. **`phi` has infinite outer order.** `[phi]^k = rho(q^k) != 1` for `k != 0`.
4. **Conclusion.** `fpbs-bounded-cost-outer-cyclic-extension-price-one` gives
   `Lambda` fixed price one, and (F2) lifts it to `Gamma`.

**(b) `Q` is locally finite.**
- `Q_0` is locally finite, hence amenable.
- It has no infinite amenable subgroup, so it is finite.
- `fpbs-bounded-cost-locally-finite-outer-price-one` concludes.

**(c) `Q` is torsion and has an infinite finitely generated subgroup `A`.**
- Put `Lambda = pi^-1(A)`. Then `N ◁ Lambda` satisfies (H), and `Lambda/N ≅ A`
  is infinite, finitely generated and torsion.
- By (F1) its outer kernel is `A ∩ Q_0`, which has no infinite amenable
  subgroup.
- `fpbs-bounded-cost-fg-torsion-quotient-price-one` gives `Lambda` fixed price
  one, and (F2) lifts it to `Gamma`.

**Converse.** Each of the three open premises is a special case of the target.
So the target is equivalent to their conjunction, given the two established
premises.

This is dependency bookkeeping for a written deduction, not a formal
verification.
