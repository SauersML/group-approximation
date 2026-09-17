---
rg: 2
id: fpbs-locally-free-groups-have-fixed-price
kind: claim
title: Every countably infinite locally free group has fixed price, equal to one plus its first L2-Betti number
root: true
distinct_from:
  fpbs-locally-free-free-actions-have-finite-cost: that is the finite-cost statement for c* < infinity, which implies this claim; this is fixed price itself, which a priori also allows every free action to have infinite cost.
  fpbs-fixed-price-non-amenably-generated-from-fg: that is the conditional passage for a different class (it contains non-locally-free groups, and misses amenably generated locally free groups such as Q * Q); this is unconditional and restricted to locally free groups.
artifacts:
  - research/artifacts/fpbs-locally-free-fixed-pseudocost-2026-09-17.md
---

**OPEN.** Let `Γ` be a countably infinite locally free group. Prove that `Γ`
has fixed price `1 + beta_1^(2)(Γ) = c*(Γ)`.

**Decomposition.** Route `fpbs-locally-free-fixed-price-from-finite-cost` needs
two inputs:
- the established dichotomy
  `fpbs-locally-free-free-action-costs-are-c-star-or-infinite`;
- the open prerequisite `fpbs-locally-free-free-actions-have-finite-cost`.

Without that prerequisite, the dichotomy already shows that a locally free
group fails fixed price only if costs `c*` and `∞` both occur.

**Relation to the flagship.** Every finitely generated subgroup of `Γ` is free
and has fixed price (Gaboriau). So this claim is the flagship "every countable
group has fixed price", restricted to groups where the hypothesis of the
countable passage holds unconditionally for all finitely generated subgroups.
Any proof of `fpbs-fixed-price-countable-from-finitely-generated` that applies
the hypothesis only to subgroups of `Γ` would prove this claim. A proof that
applies it to finitely generated supergroups would not.

## Attempts

**Cost squeeze (September 17, 2026).** Artifact
`research/artifacts/fpbs-locally-free-fixed-pseudocost-2026-09-17.md`.
- Proved `beta_1^(2) = c* − 1`: minimal-rank stages are compressed, hence
  `L²`-independent (Jaikin-Zapirain).
- Pseudocost is at most `c*`, along the subgroup exhaustion.
- So free costs lie in `{c*, ∞}`.

The squeeze dies at infinite cost. Pseudocost controls cost only when cost is
finite (Tucker-Drob Cor 6.8(1)). An increasing union of relations of cost
`≤ c*` is not known to have finite cost; that is Tucker-Drob Q 7.6. The
missing statement is `fpbs-locally-free-free-actions-have-finite-cost`.

Not usable:
- **Anchors.** Proposition F anchors (infinite finitely generated normal
  subgroups) do not exist, by artifact §6. The exceptions are finitely
  generated `Γ` (free) and locally cyclic `Γ` (amenable), which already have
  fixed price.
- **Weak containment.** Kechris's cost monotonicity under weak containment is
  imported only for finitely generated groups.

This claim was marked `root: true` as a named special case of
`fpbs-fixed-price-universal`, in the same way as
`fpbs-bounded-exponent-two-groups-fixed-price`.
