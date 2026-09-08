---
rg: 2
id: arithmetic-hnn-nonhyperlinearity-equals-global-collapse
kind: claim
title: Arithmetic HNN nonhyperlinearity is equivalent to global commutant collapse in every rank and prime
distinct_from:
  maximal-subgroup-hnn-equals-commutant-collapse: That is conditional on subgroup maximality; this proves the arithmetic hypotheses and specializes the equivalence to every n at least two and every prime.
  rf-perfect-pair-transfer-equals-regular-rcc: That equates a matrix inequality and regular commutant collapse in higher rank; this identifies their negative group endpoint and also covers rank two.
artifacts:
  - research/artifacts/commutation-stabilizer-relative-embedding-2026-09-07.md
  - research/artifacts/smith-prime-localization-maximality-audit-2026-09-07.md
---

Fix a prime `p` and `n>=2`. Put `C=SL_n(Z)`,
`A=SL_n(Z[1/p])`, and `H=A *_C(C x Z)`. The following are equivalent:

1. `H` is nonhyperlinear.
2. In every canonical trace-preserving embedding `pi:L(A)->Q` into
   a tracial matrix ultraproduct,
   `pi(L(C))' cap Q = pi(L(A))' cap Q`.
3. `L(C)<=L(A)` is not relatively embeddable over scalars.
4. The plain double `A*_C A` is nonhyperlinear.
5. The ordinary binary coset wreath `(direct_sum_(A/C) C_2) rtimes A`
   is nonhyperlinear.
6. No canonical CE actor model carries a `C`-central unitary with
   coefficient `tau(k* u_g k u_g*)=1_C(g)` for all `g in A`.

For `n>=3`, these are also equivalent to a dimension-free inequality

```text
1-|tr([U,rho(h)])|^2
 <= L (sum_(c in S_C)(1-|tr([U,rho(c)])|^2)+delta(rho))
```

for every finite-dimensional assignment `rho` of a fixed finite
presentation of `A` and every unitary `U`, where
`h=diag(p,1,...,1,p^-1)`, with the evident two-coordinate form when
needed, `S_C` generates `C`, and `delta` is the maximum normalized-HS
relator defect. Existence of some finite `L` is asserted to be
equivalent, not proved unconditionally.

Alternatively, the coefficient of the subgroup-energy sum can be
prescribed to be `K=4/kappa^2`, for a chosen Kazhdan constant of
`S_C`, if the defect term is allowed to be a qualitative modulus
`eta(delta)->0`. This is also equivalent to the same six assertions.
For every `K'>4/kappa^2`, the defect term can further be taken to be
`L_(K') delta` with a finite coefficient depending on the slope.
No effective coefficient or linear defect term at the exact limiting
slope is claimed.

In particular, for `n=3,p=2`, the open full quantitative statement
`projective-trace-square-transfer-for-sl3-pair` and the open
amalgamated-free-Haar exclusion have the same truth value. For
`n=2,p=2`, global RCC, exact quasi-regular exclusion, and free-Haar
exclusion have the same truth value. The equivalence can change the
actor embedding; it imposes no extra moments on a supplied projection
inside its original model. None of these common negative statements
is established here.
