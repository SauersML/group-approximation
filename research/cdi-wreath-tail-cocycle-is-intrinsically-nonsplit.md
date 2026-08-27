---
rg: 2
id: cdi-wreath-tail-cocycle-is-intrinsically-nonsplit
kind: claim
title: The CDI property-T wreath-like tail is an intrinsic non-split corona cocycle
distinct_from:
  cdi-property-t-envelope-has-nonabelian-base: that records the operator-valued cocycle crossed product; this proves that its infinite tails cannot all be removed by changing the group section.
  cdi-wreath-extension-preserves-projective-basis-gate: that computes the trace of the extended representation; this treats the algebraic cocycle responsible for the twisted action.
---

Let `G in WR(F_3,B)` be the property-`(T)` wreath-like group used in the CDI
embedding-universality proof.  In the special decomposition of CDI Lemma
2.13 write

```text
G = F_3^(B) rtimes_(alpha,v) B,
alpha_b=Ad(rho_b) sigma_b,
v_(b,c)=rho_b sigma_b(rho_c) rho_(bc)^(-1),             (CDI-C1)
```

where `rho_b in F_3^B`.  In the quotient group

```text
Q_A=F_3^B/F_3^(B),
```

the classes `q_b=[rho_b]` form a nonabelian `1`-cocycle

```text
q_(bc)=q_b sigma_b(q_c).                               (CDI-C2)
```

This cocycle is intrinsic up to the natural simultaneous coordinate gauge,
and it is nontrivial.  Equivalently, no change of section can make every
`rho_b` finitely supported.  If it could, the special embedding would identify
`G` with the ordinary restricted wreath product `F_3 wr B`; that group has
infinite abelianization, whereas a property-`(T)` group has finite
abelianization.

On applying the input representation `pi:F_3->U(M)`, the tails become the
product automorphisms `eta(pi^B(rho_b))` in CDI Proposition 3.8.  Their
nonrestricted nature means they are not implemented by the finite tensor
unitaries `gamma(U(M)^(B))` used inside `M^B`.  Thus ordinary section change
cannot untwist the CDI action to a restricted Bernoulli crossed product.
Any von Neumann exterior equivalence doing so would require genuinely new
infinite-tensor implementers; it is not contained in the source's special
decomposition.

