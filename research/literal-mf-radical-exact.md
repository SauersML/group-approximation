---
rg: 2
id: literal-mf-radical-exact
kind: claim
title: Exact MF radical of the literal non-MF group
root: true
---

For the literal finitely presented group `E` and its marked central involution
`w`,

```text
Rad_MF(E) = {1,w}.
```

**REFUTED 2026-08-16.**  `literal-mark-quotient-not-mf` is established with a
zero-input Lean proof: the unsquared defect `u=[tct^-1,v_1]` is nontrivial in
`E/<w>` and lies in `Rad_MF(E/<w>)`, while `commutator_not_zpow_mark` puts it
outside `<w>`.  Radical pullback therefore gives `<w><Rad_MF(E)` strictly.

The old route `literal-quotient-computes-mf-radical` ran through
`literal-mark-quotient-mf`, whose negation is proved.  This node is retained as
the record of the refuted guess.

**Correct computation, 2026-08-19.**  The successor claim
`literal-mf-radical-is-unsquared-defect` is established and gives

```text
Res_MF(E) = <<u>> = N_conj.
```

Its quotient is `Sigma *_B(B x C_2)` and is MF by embedding in a Shulman
double.  The same successor claim also shows that the sign-free collapse defect
computes the residual exactly downstairs.
