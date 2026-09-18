---
rg: 2
id: fpbs-hutchcroft-nonunimodular-pc-below-pt
kind: claim
title: For a transitive nonunimodular automorphism group, p_c lies strictly below the half-tilted susceptibility threshold p_t
distinct_from:
  fpbs-hyperbolic-nonunimodular-critical-l2-gap: that imports Hutchcroft's p_c < p_(q->q) (arXiv:1804.10191, thm:nonunimodular), a statement about the untilted two-point operator; this imports p_c < p_c(G,Gamma,lambda) <= p_t (arXiv:1711.02590, thm:pcpt), a statement about the tilted susceptibility chi_(p,lambda), which is what fibre-summed kernels over a tree factor see.
  fpbs-hyperbolic-and-nonunimodular-nonuniqueness: that imports p_c < p_u for the same class; this imports the stronger intermediate inequality p_c < p_t, with the definitions of the modular function and of chi_(p,lambda) it uses.
---

**ESTABLISHED (imported).** Proof route:
`fpbs-hutchcroft-nonunimodular-pc-below-pt-citation`.

**Setting (the source's definitions).** Let `G = (V,E)` be connected and
locally finite. Let `Gamma ⊆ Aut(G)` be transitive.

- The modular function is `Delta(x,y) = |Stab_y x| / |Stab_x y|`.
- The tilted susceptibility is
  `chi_(p,lambda)(v) = sum_(u in V) tau_p(v,u) Delta^lambda(v,u)`.
  It does not depend on `v`.
- The tilted threshold is
  `p_c(G,Gamma,lambda) = sup{p : chi_(p,lambda) < infinity}`.
- The tiltability threshold is
  `p_t(G,Gamma) = sup{p : chi_(p,lambda) < infinity for some lambda}`.
  The source observes that `p_c(G,Gamma,lambda) = p_c(G,Gamma,1-lambda)` and
  that `p_t = p_c(G,Gamma,1/2)`.

**Theorem (Hutchcroft, arXiv:1711.02590v3, thm:pcpt).** If `Gamma` is
transitive and nonunimodular, then

```text
p_c(G) < p_c(G,Gamma,lambda) <= p_t(G,Gamma)     for every lambda in (0,1).
```

**Consequence used on the board.** Take `lambda = 1/2`. Then
`chi_(p_c,1/2) < infinity`, since `chi_(p,1/2)` is nondecreasing in `p` and
is finite for every `p < p_t`, and `p_c < p_t`.

Status records an imported theorem, not independent mathematical
verification.
