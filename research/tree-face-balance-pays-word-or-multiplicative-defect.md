---
rg: 2
id: tree-face-balance-pays-word-or-multiplicative-defect
kind: claim
title: Every triangular ucp balance pays a fixed multiplicativity or group-word distance on one tree face
distinct_from:
  group-word-tree-face-balancing-collapses: that treats exact group-word-valued star homomorphisms; this gives a quantitative neighbourhood no-go around that entire class and forces a fixed defect before exact group-word balance is reached.
  three-face-ucp-balancing-needs-macroscopic-tree-motion: that measures distance from the single canonical tree-face lift; this measures distance from every group-unitary lift simultaneously and also allows the chosen group words to vary from generator to generator.
  km-triangle-relator-kernel-has-no-relative-gap: that rules out a uniform relator-Laplacian inverse in arbitrary unitary representations; this is an operator-norm dichotomy for any ucp local section on the concrete finite face system.
---

**ESTABLISHED (quantitative no-go at the explicit `(3,3,4)` triangle).**
Use the notation of `group-word-tree-face-balancing-collapses`, and let
`Phi:S_Delta->C^*(G_0)` be a ucp right inverse on the three-face operator
system.  For `V in {P_12,P_23}` put

```text
U_g={u_x in C^*(G_0): x in G_0 and q(x)=g},
gamma_V=max_(g in V) dist(Phi(u_g),U_g),
mu_V=max_(g,h in V)
       ||Phi(u_g)Phi(u_h)-Phi(u_(gh))||.                    (WMD1)
```

Then

```text
delta_L=min{sqrt(2),6/L^2},
boxed: max_(V in {P_12,P_23}) (mu_V+3 gamma_V) >= delta_L. (WMD2)
```

Thus a successful simultaneous balance cannot even approach the class killed
by the exact group-word theorem.  On at least one finite tree face it either
has a fixed operator-norm multiplicativity defect, or a canonical generator
stays a fixed distance from **every** group-unitary lift of that generator.

Proof: `tree-face-word-distance-dichotomy-proof`.

**Consequence for the live reservoir.**  Relator coefficients cannot evade
the Bass--Serre no-go by producing increasingly accurate word-valued face
maps.  Any packetwise correction approaching a local ucp section must retain
the non-group-unitary or nonmultiplicative behavior in `(WMD2)` at a fixed
scale.  The remaining problem is therefore not an exactification of hidden
group words; it is a genuinely operator-algebraic complete-positive balance.
The constant is the smaller of the square-root-two word-separation scale and
the three-face Gram floor after the factor `3` in `(WMD1)`; no CP-preserving
exact replacement of the rounded word maps is asserted.

DERIVATION
tree-face-word-distance-dichotomy-proof
