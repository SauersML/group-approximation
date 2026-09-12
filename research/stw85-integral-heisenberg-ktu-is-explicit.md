---
rg: 2
id: stw85-integral-heisenberg-ktu-is-explicit
kind: claim
title: The classification invariant of every infinite-dimensional integral-Heisenberg irreducible quotient is explicit
distinct_from:
  stw85-integral-heisenberg-irrep-quotients-are-torus-powers: that theorem identifies the quotient algebra and the rational boundary; this theorem computes all components and the pairing of its KT_u invariant.
  stw99-problem-lxxxv-polynomial-growth-invariants: that root asks for arbitrary polynomial-growth groups; this theorem solves its complete standard Heisenberg family.
artifacts:
  - research/artifacts/stw85-integral-heisenberg-invariant-audit-2026-08-31.md
---

Let `theta in (0,1)\Q` and put
`B_(n,theta)=A_theta^(tensor n)`.  If
`Theta_(n,theta)` is the block diagonal skew form with `n` blocks

```text
[ 0      theta]
[-theta   0   ],
```

then

```text
K_0(B_(n,theta)) = exterior-even Z^(2n),
K_1(B_(n,theta)) = exterior-odd  Z^(2n),
[1]                = 1 in exterior-degree zero,
T(B_(n,theta))     = {tau},
rho_tau            = exp_wedge(Theta_(n,theta)).        (H85-2)
```

Both K-groups are free of rank `2^(2n-1)`.  More explicitly, write
`a_j,b_j` for the two exterior generators of factor `j`.  On the
standard even exterior basis,

```text
rho_tau(wedge_(j in S)(a_j wedge b_j))=theta^|S|,
rho_tau(e_I)=0 for every other even basis monomial e_I. (H85-3)
```

Thus (H85-2)--(H85-3), with the displayed unit, completely compute the
`KT_u=(K_0,[1],K_1,T,rho)` requested in STW Problem LXXXV.  The ordered
enhancement is also explicit:

```text
K_0(B_(n,theta))_+
 = {0} union {g:rho_tau(g)>0}.                           (H85-4)
```

For every `k>=2` and `i=0,1`,

```text
K_i(B_(n,theta);Z/k)=(Z/k)^(2^(2n-1)),                 (H85-5)
```

with coordinatewise coefficient reduction and zero Bockstein maps into
the torsion-free integral K-groups.  For `n=1`, this specializes to
`K_0=K_1=Z^2`, `rho(m,l)=m+l theta`, unit `(1,0)`, and
`A_theta isomorphic to A_eta` exactly when
`eta=plus-or-minus theta mod Z`.
