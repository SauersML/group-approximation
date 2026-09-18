---
rg: 2
id: thompson-f-amenable-iff-dyadic-action-extensively-amenable
kind: claim
title: Thompson's group F is amenable exactly when its action on the dyadic rationals is extensively amenable
distinct_from:
  thompson-f-dyadic-action-is-extensively-amenable: that is the open statement that the dyadic action is extensively amenable; this proves it is equivalent to amenability of F, so it is not a weaker target.
  affine-lamplighter-amenable-iff-extensively-amenable: that is the general citation (Juschenko-Monod criterion and JMBMdlS Lemma 2.1, amenable group implies extensively amenable action); this adds the converse for F on the dyadics through the breakpoint cocycle.
  f-dyadic-ea-iff-inverted-orbit-confinement: that reformulates dyadic extensive amenability as inverted-orbit confinement; this identifies the same property with amenability of F.
  thompson-f-is-lea-only-if-amenable: that collapses local embeddability into amenable groups onto amenability; this collapses extensive amenability of the dyadic action onto amenability.
  thompson-f-recurrent-orbits-have-stabilizers-containing-f: that shows recurrence plus stabilizer amenability cannot work for F-orbits; this removes the stabilizer condition entirely for the dyadic orbit, because the lamp cocycle has trivial kernel.
---

**ESTABLISHED** through `thompson-f-amenable-iff-dyadic-action-extensively-amenable-proof` (direct proof
from verbatim results of Juschenko–Matte Bon–Monod–de la Salle, arXiv:1503.04977; not independently
reviewed; no priority claimed, the observation may be folklore).

Let `D` be the set of dyadic rationals in `(0,1)`, with the standard action of Thompson's group `F`.

1. **Equivalence.** `F` is amenable if and only if the action `F ↷ D` is extensively amenable.
2. **Every orbit that maps onto the dyadics.** Let `X` be a transitive `F`-set that admits an `F`-map
   `X → D`. Equivalently, `X = F/H` with `H` fixing some dyadic point. Then `F ↷ X` is extensively
   amenable if and only if `F` is amenable. This covers the regular action, the `k`-element subsets of `D`,
   and the cosets of the pointwise fixers `F_{[0,a]}` and `F_{[a,1]}` with `a ∈ D`.

**Mechanism.** The breakpoint cocycle `c_g = β(g⁻¹) ∈ Z^{(D)}` gives a homomorphism
`F → Z^{(D)} ⋊ F`, `g ↦ (c_g, g)`, with trivial kernel `{g : c_g = 0} = {1}`. So the Juschenko–Monod
twisted-embedding method (JMBMdlS Corollary "prop:functor:amenable:intro", Remark "R: method") needs
nothing besides extensive amenability of `F ↷ D`. The affine action `g ∗ φ = c_g + g·φ` of `F` on
`Z^{(D)}` is moreover free.

## Consequences

- `thompson-f-dyadic-action-is-extensively-amenable` is equivalent to `thompson-f-is-amenable`, and
  through `f-dyadic-ea-iff-inverted-orbit-confinement` so is
  `f-dyadic-inverted-orbit-is-subballistic-on-rare-events`. These nodes are reformulations of the root,
  not weaker prerequisites. Route: `thompson-f-amenable-via-dyadic-extensive-amenability`.
- For `F`, the paradigm "extensive amenability plus a lamp cocycle with amenable kernel" has no independent
  second prerequisite. Its whole content is extensive amenability of an orbit that maps onto `D`.
- Surviving orbits are those whose stabilizers fix no dyadic point, e.g. the orbit of an irrational `t`,
  with stabilizer `F_{[0,t)} × F_{(t,1]}`. There `β` is not valued in a restricted product over the orbit.
- Quantitative form: `thompson-f-dyadic-ea-witnesses-need-tower-size`.
