---
rg: 2
id: coarse-fine-selector-covariance-has-quarter-trace-floor
kind: claim
title: One coarse-to-fine selector covariance has a quarter-carrier trace floor
distinct_from:
  one-coarse-to-fine-prefix-isometry-closes-the-reservoir: that compresses a proposed rectangular arrow and detects its source Gram defect; this detects the preceding unitary selector-covariance defect directly and eliminates the arrow from the endpoint.
  even-partial-swap-star-has-canonical-trace-floor: that multiplies an even star of authenticated swaps and reads the trace of the product word; this needs one unitary and two unequal packet selectors.
  atlas-rectangular-wedderburn-isometry-certificate: that asks finite multiplicity selection to construct a rectangular operator; this proves that selector covariance itself is already the complete rectangular certificate once the two packets share a carrier.
---

**ESTABLISHED.**  Let `(M,tau)` be a finite tracial matrix algebra, let `P`
be a projection, and let `e,f<=P` be projections with

```text
tau(e)=tau(P)/2,                 tau(f)=tau(P)/4.       (CSC1)
```

For every unitary `U in M`,

```text
||UeU^*-f||_2^2 >= tau(P)/4.                          (CSC2)
```

More generally, for any two projections `p,q`,

```text
||p-q||_2^2 >= |tau(p)-tau(q)|.                        (CSC3)
```

Thus after exactifying a common-carrier coarse `M_2` packet and fine `M_4`
packet, no off-diagonal block, polar decomposition, or Gram calculation is
needed.  If the fixed Leavitt partial-swap word `J_x` obeys

```text
epsilon_J=||J_x e J_x^*-f||_2,                         (CSC4)
```

then directly

```text
tau(P)<=4 epsilon_J^2.                                 (CSC5)
```

Consequently the entire same-reservoir endpoint is one scalar matrix-only
statement: vanishing presentation defect must make the recovered selector
covariance `(CSC4)` vanish, or charge its failure to already counted packet
boundary energy.

This contraction also sharpens the firewall.  A universal tracial proof of
`(CSC4)=0` is impossible at positive `tau(P)`, because `(CSC2)` holds in
every finite tracial von Neumann algebra, including a group factor.  The
selector recovery must therefore use finite external multiplicity (or an
equivalent canonical-microstate selection); it cannot be a fixed
star-polynomial consequence of the relator ideal.

