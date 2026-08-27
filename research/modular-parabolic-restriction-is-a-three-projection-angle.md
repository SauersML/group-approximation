---
rg: 2
id: modular-parabolic-restriction-is-a-three-projection-angle
kind: claim
title: Modular parabolic restriction is exactly a three-projection angle
artifacts:
  - experiments/iwahori_parabolic_split.py
  - experiments/iwahori-parabolic-split.json
distinct_from:
  iwahori-parabolic-boundary-splitting-is-uniform: that asks for a uniform lower bound over all congruence coefficient systems; this identifies the exact finite-dimensional operator whose nonzero singular values must be bounded.
---

Let `Gamma=PSL_2(Z)=<a,b | a^2=b^3=1>`, put `u=ab`, and let `M` be any
finite-dimensional unitary `Gamma`-module.  Write `P_a,P_b,P_u` for the
orthogonal projections onto the fixed spaces of `<a>`, `<b>`, and `<u>`, and
put

```text
K=ker(P_a) cap ker(P_b).                                  (TPA1)
```

With the quotient cellular norm, there is an isometric model of cohomology
(up to the fixed scalar convention on the two generator edges)

```text
H^1(Gamma,M) = K.                                         (TPA2)
```

Under the canonical unitary identification
`H^1(<u>,M)=M/(u-1)M = M^u`, parabolic restriction is

```text
res_u(m)=-2 P_u m,                  m in K.               (TPA3)
```

Consequently the norm of the best Eisenstein lift is one half the reciprocal
of the smallest nonzero singular value of `P_u|K`.  Cuspidal cohomology is
exactly `ker(P_u|K)`.  Near-nontrivial eigenvalues of `u` never need to be
inverted: cyclic coinvariants retain only the exact fixed space `M^u`.
