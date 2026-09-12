---
rg: 2
id: kun-thom-actors-have-no-torsion-free-finite-index-subgroups
kind: claim
title: Elementary groups over infinite rings of prime characteristic are not virtually torsion-free
distinct_from:
  kun-thom-nonsofic-wreath: that imports nonsoficity of wreaths over the Theorem E pairs; this shows the actor groups of those pairs cannot be made torsion-free by passing to finite index.
  hyperbolic-groups-virtually-torsion-free: that asks whether every hyperbolic group is virtually torsion-free; this proves that elementary groups over infinite rings of prime characteristic, which are not hyperbolic, are not.
---

**ESTABLISHED.** Let `R` be an infinite commutative ring of prime
characteristic `p`, let `r >= 2`, and let `G` be any group containing
`EL_r(R)`. Then every finite-index subgroup of `G` contains an element of
order `p`.

This applies to the Kun--Thom Theorem E pairs

```text
Gamma = EL_r(F_q[x_1..x_d])  <=  G = EL_r(F_q[x^(+-1)]) semidirect SL_d(Z),
```

and to every group containing them, including their generalized wreaths and
group doubles. None of these has a torsion-free subgroup of finite index, so
none supplies a finite-index torsion-free host for
`kaplansky-zero-divisor-conjecture`. A torsion-free Kun--Thom-type host needs
coefficient rings of characteristic zero.
