---
rg: 2
id: sofic-preserving-single-defect-kazhdan-router
kind: claim
title: Route one arithmetic defect onto a sofic torsion-free Kazhdan quotient
distinct_from:
  two-generated-single-element-hull-router: That audited router preserves torsion-freeness, finite presentation, property (T), survival, and normal generation, but it makes no claim that the quotient is sofic.
  sofic-safe-finite-presentation-compiler: That asks for a uniform computable compiler preserving a sofic positive branch across arbitrary inputs; this asks for one concrete arithmetic compression source and one marked defect.
  arithmetic-defect-saturated-kazhdan-group-is-sofic: That is the positive approximation property of the finished quotient; this is the construction theorem that would produce such a quotient while retaining the marked routing data.
artifacts:
  - research/artifacts/arithmetic-single-defect-saturation-2026-08-23.md
---

Let `R` be the torsion-free finitely presented arithmetic free-product source
and `1!=sigma in R` the Britton-certified compression defect used in
`defect-saturation-from-arithmetic-source`.  Construct a surjection

```text
q:R->>Q
```

such that

```text
Q is nontrivial, finitely presented, torsion-free, sofic and property (T),
Q = <<q(sigma)>>^Q.                                    (SPR1)
```

Equivalently, strengthen the existing single-element Hull router only at its
positive approximation output.  Residual finiteness is impossible here:
the downstream normal-Kazhdan theorem makes `Rad_MF(Q)=Q`, whereas every
nontrivial residually finite group is MF.  The required output must therefore
be genuinely sofic but non-MF.

## Attempts

1. **Ordinary Hull--Osin routing.**  It gives every algebraic clause in
   `(SPR1)` but has no finite-model clause.  Soficity cannot be pushed through
   the resulting quotient map.
2. **Finite-quotient routing.**  Requiring the marked relators to survive in
   a cofinal family of finite quotients would make `Q` residually finite and
   contradict the forced full MF radical, so exact finite quotients are the
   wrong model.
3. **Finite-window permutation routing.**  The viable target is weaker and
   genuinely sofic: for each finite word window and tolerance, choose the
   long Hull relators together with a finite permutation model in which the
   routed generator identities hold off a small exceptional set, while the
   protected defect moves a fixed fraction of points.  A diagonal choice
   must preserve torsion-freeness and normal generation at the exact group
   level.  No theorem in the repository currently synchronizes these two
   choices; that synchronization is the precise frontier.
