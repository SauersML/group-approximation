---
rg: 2
id: schur-predicate-is-character-density-difference-proof
kind: route
title: Sum reciprocal-dimension central idempotents sector by sector
target: schur-predicate-is-character-density-difference
requires:
  - clifford-commutator-rank-is-packet-dimension
  - oriented-schur-child-branching-identity
---

Every negative-sector irreducible of `C_f` has dimension `D`. Its primitive
central idempotents sum to the negative-sector identity, hence

```text
Z_(C_f)=p_-/D.                                          (CDF3)
```

In the selector sector `x`, every irreducible of `B_f` has dimension
`D 2^(f(x))`. The primitive central idempotents over that sector sum to
`p_-p_x`, regardless of the number of radical characters. Therefore

```text
Z_(B_f)
 =sum_x p_-p_x/(D 2^(f(x)))
 =(p_-/D)(1-(1/2)sum_(x:f(x)=1)p_x).                   (CDF4)
```

Subtracting `(CDF4)` from `(CDF3)` proves `(CDF2)`.

If `rho|_H` contains `m_pi` copies of `pi` in ambient dimension `d`, then

```text
tau_d(rho(e_pi/dim(pi)))
 =(dim(pi)m_pi/d)/dim(pi)=m_pi/d.
```

Summing proves the multiplicity interpretation. The standard character
formula for `e_pi` proves effectivity and exhibits `(CDF2)` as a fixed finite
linear combination of ordinary group words.

Finally `(CDF2)` is a scalar multiple of the projection `P_f`, so

```text
||rho(Z_C-Z_B)||_2^2
 =tau(rho(P_f^2))/(4D^2)
 =tau(rho(P_f))/(4D^2),
```

which is `(CDF5)`.
