---
rg: 2
id: whole-module-covariance-average-equals-character-transport
kind: claim
title: Finite spectral transport energy is an exact whole-module covariance average
distinct_from:
  finite-covariance-energy-sees-only-character-restrictions: that computes what a fixed finite set of module probes can see; this allows an average chosen from the finite occurring spectrum and identifies the complete transport energy exactly.
  infinite-character-actor-word-energy-interface: that asks finite presentation defect to control all virtual module words uniformly; this identity begins only after whole-module covariance is available.
---

**ESTABLISHED.**  Let `M` be an elementary abelian `2`-group, let `s` be an
automorphism of `M`, and let

```text
rho(m)=sum_(chi in Omega_0) chi(m)P_chi
```

be a finite-spectrum unitary representation, where `(P_chi)` is a PVM and
`P_chi=0` outside the finite set `Omega_0`.  For a unitary `C`, put

```text
d_s(m)=||C rho(m) C^*-rho(sm)||_2,
E_s=sum_(chi in hat M)||C P_chi C^*-P_(s chi)||_2^2,  (WCA1)
```

where `(s chi)(m)=chi(s^(-1)m)`.  Only finitely many terms of `E_s` are
nonzero.  There is a finite quotient `q:M->M_0`, determined by `Omega_0`
and `s`, such that

```text
E_s=Average_(u in M_0) d_s(m_u)^2                    (WCA2)
```

for arbitrary representatives `m_u` of the quotient classes.  In
particular,

```text
E_s<=sup_(m in M)d_s(m)^2.                            (WCA3)
```

The average depends on the finite occurring spectrum; it is not a fixed
finite list of presentation words.  Thus `(WCA2)` removes no uniformity gate
from `infinite-character-actor-word-energy-interface`.  It says exactly that
once uniform covariance on the whole module has been obtained, no further
infinite-resolution inequality is needed.
