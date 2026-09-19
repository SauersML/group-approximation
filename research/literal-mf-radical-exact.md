---
rg: 2
id: literal-mf-radical-exact
kind: claim
title: Exact MF radical of the literal non-MF group
root: true
---

For the literal finitely presented group `E` and its marked central
involution `w`,

```text
Rad_MF(E) = {1, w}.
```

**REFUTED 2026-08-16.**  `literal-mark-quotient-not-mf` is established, now
with a zero-input Lean proof
(`GroupApproximation/Sofic/LiteralSignFreeQuotient.lean`,
`signFreeQuotient_not_isCDEOperatorMF`): the unsquared defect
`u = [tct^{-1}, v_1]` is nontrivial in `E/<w>` and lies in
`Rad_MF(E/<w>)`, while `commutator_not_zpow_mark` puts it outside `<w>`.
The radical pullback (`cor:pullback`, formalized) then gives

```text
<w>  <  Rad_MF(E)   strictly.
```

The single route to this claim, `literal-quotient-computes-mf-radical`,
ran through `literal-mark-quotient-mf`, whose negation is what is now
proved; that route is invalidated.  The node is retained as the record of
the question, and the surviving question — whether the collapse rules
compute the radical exactly — is `literal-quotient-computes-mf-radical`'s
successor in the manuscript's Questions list, not this claim.
