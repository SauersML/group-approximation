---
rg: 2
id: nested-two-finite-subgroup-idempotents-have-strict-rank
kind: claim
title: Strict nesting between idempotents supported in two finite subgroups forces a strict rational rank gap
invalidates: [modular-nested-equivalence-refutes-leavitt-direct-finiteness]
distinct_from:
  lifted-trace-detects-finite-subgroup-projectives: that directly separates nested idempotents in one common finite subgroup; this permits the two finite support subgroups to generate an arbitrary infinite subgroup and transfers only the nesting equations to a finite-group amalgam.
  leavitt-balanced-corners-separated-modulo-four: that treats one explicit cubic pair in a common finite subgroup; this treats every pair in two possibly different finite subgroups, in all matrix sizes and characteristics.
  subgroup-supported-one-sided-inverse-rigidity: that constrains a factor of the inverse pair; this constrains the source and reverse-product idempotents while allowing both intertwiners arbitrary ambient support.
---

Let k be any field, G any group, H,K <= G finite subgroups, and
e in M_n(k[H]), f in M_n(k[K]) idempotents. Assume

    ef=fe=f,       e!=f.

Then their ordinary rational normalized ranks satisfy

    dim_k(e k[H]^n)/|H| > dim_k(f k[K]^n)/|K|.          (TFR1)

There is no assumption that <H,K> is finite, residually finite, or sofic.

For k=F_p, the lifted p-adic trace therefore separates [eS^n] and
[fS^n] in K_0(S), where S=F_p[G]. Their difference has infinite
additive order. Hence the two induced projectives cannot become
isomorphic after adding any common finitely generated projective
S-module, regardless of the supports of the proposed isomorphisms.

In particular, if a finite-subgroup-supported corner identity e admits
xy=e with yx=f!=e, then f cannot be supported in ANY finite subgroup
of G, even a different subgroup from the one supporting e.

For any u in G, a finite-subgroup-supported idempotent e and its
group conjugate ueu^(-1) cannot be strictly nested in either direction:
conjugation preserves their normalized finite ranks. In particular a
single group-word shift cannot strictly compress such a packet by
literal containment, however complicated that word is.

This last statement concerns literal finite-subgroup support for f.
It does not exclude a proper subidempotent of infinite support-generated
subgroup whose projective is abstractly isomorphic to a finite-subgroup
projective. Such an exclusion would go beyond the argument given here.
