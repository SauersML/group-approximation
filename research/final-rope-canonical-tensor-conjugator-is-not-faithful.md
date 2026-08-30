---
rg: 2
id: final-rope-canonical-tensor-conjugator-is-not-faithful
kind: claim
title: The canonical tensor-synchronized final-rope conjugator kills a Britton word
invalidates:
  - centralizing-hnn-sofic-strategy-route
distinct_from:
  sofic-safe-finite-presentation-compiler: that asks whether some permutation model proves the positive rope sofic; this rules out only the canonical product-form conjugator.
  centralizing-hnn-perturbed-edge-separation: that is the inner central-rope problem; this obstruction occurs at the outer twisted rope.
  regular-mf-tensor-sync-proves-twisted-rope-mf: that theorem passes through the universal C-star HNN algebra and explicitly does not claim the concrete tensor representation is faithful.
artifacts:
  - research/artifacts/mf-fp-pi2-unconditional-assembly-2026-08-26.md
---

**ESTABLISHED.**  In the actual Mikhailova/graph-witness compiler, every
canonical tensor-synchronized permutation model of the final rope which
represents the stable letter by `U=1 x W` kills one fixed nontrivial
Britton word.

Write

```text
K=K_0 x K_g,
Gamma=<K,v | [v,L]=1>,
S=<i(F),v i(F)v^-1>,
R=<Gamma x Q,u | u(s,1)u^-1=(s,tau(s))>.
```

Choose a nontrivial basis element `a in F` and let
`k=((a,1),1)` be its copy in the first factor of `K_0`, with every
other coordinate trivial.  Then `k notin S`; hence
`w=[u,(k,1)]` is Britton-reduced and nontrivial in `R`.

The synchronizing homomorphisms `lambda_n:Gamma->C_n` kill `K_0`.  If
`pi_n` is any independent permutation model of `Gamma` and the base
model is

```text
Pi_n(g,q)=pi_n(g) x L_n(lambda_n(g),beta_n(q)),
```

then `Pi_n(k,1)=pi_n(k) x 1`.  The canonical edge conjugator is
`U_n=1 x W_n`, so it commutes with `Pi_n(k,1)` and `w` evaluates to
the identity at every scale.

Thus exact edge conjugacy and Fell absorption alone do not prove soficity of
the final rope.  A successful model must use a genuinely mixed intertwiner;
no nonsoficity of `R` is asserted.

DERIVATION
[[final-rope-canonical-tensor-conjugator-is-not-faithful-proof]]
