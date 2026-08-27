---
rg: 2
id: cm-empty-replacement-is-fano-cap-safe
kind: claim
title: Culf--Mastel empty-constraint replacement is exactly Fano-cap safe
distinct_from:
  rstar-two-retained-coordinates-admit-a-fixed-cap-section: that proves the abstract one-row section theorem; this applies it simultaneously to the final empty-constraint replacement in the actual Culf--Mastel non-TVF construction and proves an exact before/after equivalence.
  culf-mastel-rstar-halt-model-has-fano-cap-support: that asks for cap support on every row of the final HALT instance; this removes all rows inserted by the last commutativity-gadget step and leaves only the genuine pp-reduction rows.
  culf-mastel-rstar-fixed-language-gap-is-published: that records soundness and the limitation of contextwise commutation; this concerns perfect-completeness support and does not strengthen neighborhood commutation.
---

**ESTABLISHED SOURCE-SPECIFIC CAP-SAFE STEP.**  Specialize Part 1 of
Culf--Mastel Theorem 4.14 to `Gamma={R_*}`.  Let `S_pre` be the constraint
system immediately before the last application of their non-TVF
empty-constraint replacement, after empty constraints have been subdivided
to arity two.  Thus every row of `S_pre` is either a genuine `R_*` row or a
two-variable empty row.  Let `S_fin` be the final all-`R_*` system.

Then the following are equivalent.

1. `S_pre` has a perfect CE tracial model in which every genuine `R_*` row is
   supported in a maximal Fano cap.
2. `S_fin` has a perfect CE tracial model in which every `R_*` row is
   supported in a maximal Fano cap.

Moreover, the extension from (1) to (2) leaves every old variable observable
and every old `R_*` row unchanged.  Hence the final commutativity-gadget step
cannot create the remaining FC-char obstruction.

## Proof

The forward direction of the equivalence is restriction.  For the reverse
direction, consider one empty row on commuting Boolean variables `x,y`.
Culf--Mastel Proposition 6.2 replaces it by one copy of the chosen non-TVF
relation.  In the present specialization this is one `R_*` row with `x,y` in
two designated coordinate positions `K`, `|K|=2`, and with the other two
coordinates private to this occurrence.

By `rstar-two-retained-coordinates-admit-a-fixed-cap-section`, there is one
maximal cap `C_K subseteq R_*` and a section

```text
s_K:F_2^K -> C_K,
pr_K s_K=id.                                             (CER1)
```

Let `(P_ab)_(a,b in F_2)` be the joint PVM of `x,y` in the perfect model of
the empty row.  Define each private coordinate of the replacement row by its
value under `s_K` on the four joint atoms.  Equivalently, its bit-`1`
projection is

```text
sum_(a,b : s_K(a,b)_j=1) P_ab.                           (CER2)
```

All four new observables belong to the same abelian algebra.  Their joint
PVM is supported on `s_K(F_2^2) subseteq C_K`, and its retained marginals are
exactly the original `x,y`.  Thus the replacement row is perfect and
cap-supported.

The auxiliary variables used for different empty constraints are private in
the construction.  Formula `(CER2)` can therefore be applied independently
to every empty row, without changing any old observable or old context.
The construction stays inside the original finite tracial von Neumann
algebra, so it preserves Connes embeddability.  This proves (1) implies (2).

Consequently the open cap theorem for the actual family is now localized
strictly before the last line of the Culf--Mastel proof: it is a support
theorem for the nonempty `R_*` rows produced by the chosen classical
constraintwise reduction and subdivision.  The explicit non-TVF
commutativity replacements are harmless for FC-char, even though they still
do not supply mutual neighbor--neighbor commutation.
