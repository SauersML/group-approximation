---
rg: 2
id: sofic-dyadic-coset-action-makes-hnn-sofic
kind: claim
title: Soficity of the dyadic vertex action makes the SL2 centralizer HNN sofic
distinct_from:
  psl2-bruhat-tits-action-soficity-forces-p-instability: that extracts noncorrectable permutation approximations of the base group; this proves that the proposed HNN witness itself is sofic.
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that uses the commuting finite-lamp quotient; this retains the full free HNN normal form.
---

Let `A=SL_2(Z[1/2])`, `C=SL_2(Z)`, and

```text
G=<A,t | [t,C]=1>.
```

If the action `A curvearrowright A/C` is sofic, then `G` is sofic (and hence
hyperlinear).

Indeed, `A` is residually finite and therefore sofic, `Z` is sofic, and
`sl2-centralizer-hnn-is-free-coset-wreath` identifies `G` with the free
generalized wreath product

```text
Z wr^*_(A curvearrowright A/C) A.
```

Gao--Kunnawalkam Elayavalli--Patchell, *Soficity for group actions on sets
and applications*, Research in the Mathematical Sciences 12 (2025), 48,
Theorem 3.7, proves that a free generalized wreath product of sofic groups
over a sofic action is sofic.

Consequently, proving this HNN group nonhyperlinear necessarily proves that
the dyadic Bruhat--Tits vertex action is nonsofic.  The action-soficity fork
is not merely an obstruction to the commuting-lamp Bernoulli firewall; it is
a firewall for the full canonical HNN group.
