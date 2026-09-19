---
rg: 2
id: odd-maslov-homogeneous-split-ucp-retract-is-impossible
kind: claim
title: An odd-to-even homogeneous split ucp retract is impossible
invalidates:
  - odd-maslov-llp-via-vanishing-defect-homogeneous-retract
distinct_from:
  odd-maslov-homogeneous-coefficients-have-a-uniform-folner-gap: that proves a dimension-uniform positive coefficient defect for arbitrary homogeneous ucp maps; this uses the split left inverse to extract a nonzero exact finite projective coefficient and rules out the retract altogether.
  matrix-homogeneous-ucp-retracts-can-hide-defect: that same-twist example has trivial difference multiplier and therefore an allowed invariant coefficient support; here the odd difference multiplier makes every nonzero support forbidden by Deligne invisibility.
  scalar-covariant-odd-even-ucp-retract-is-impossible: that assumes scalar-valued coefficients and obtains multiplicativity directly; this allows arbitrary matrix-valued homogeneous coefficients and extracts their finite projective subrepresentation from the canonical trace support.
---

**ESTABLISHED.**  Let `alpha` be one of the odd Maslov twists
`1/3,2/3,1/6,5/6`, let `epsilon` be an even twist `0` or `1/2`, and suppose
there are ucp maps

```text
i:A_alpha -> M_n(A_epsilon),
r:M_n(A_epsilon) -> A_alpha,       r i=id,             (OHS1)
```

such that `i` is exactly homogeneous on canonical projective unitaries:

```text
i(u_g^alpha)=C_g tensor u_g^epsilon.                   (OHS2)
```

No equivariance or homogeneity is assumed of `r`.

Put `x_g=i(u_g^alpha)`.  It is a contraction and `r(x_g)=u_g^alpha` is
unitary.  Schwarz's inequality, applied on both sides, gives

```text
r(x_g^*x_g)=r(x_gx_g^*)=1.                            (OHS3)
```

Thus every `x_g` lies in the multiplicative domain of `r`.  Define
`phi(m)=r(m tensor 1)`, let `tau_alpha` be the canonical twisted trace, and
write

```text
(tau_alpha phi)(m)=Tr(rho m),       p=supp(rho) !=0.    (OHS4)
```

Multiplicative-domain covariance gives, for every coefficient matrix `m`,

```text
phi(C_g m C_g^*)=u_g phi(m)u_g^*,
phi(C_g^* m C_g)=u_g^*phi(m)u_g.                       (OHS5)
```

Taking the canonical trace yields

```text
C_g^*rho C_g=rho=C_g rho C_g^*.                       (OHS6)
```

Moreover `(OHS3)` says that `phi` kills the positive contractions
`1-C_g^*C_g` and `1-C_gC_g^*`.  Their pairing with the faithful state on
the support of `rho` is zero, so both defects annihilate `p`.  Equations
`(OHS6)` then show that `p` reduces every `C_g` and

```text
U_g=C_g|_(p C^n)
```

is unitary.

Both `x_gx_h` and `i(u_g^alpha u_h^alpha)` belong to the multiplicative
domain of `r` and have the same image under `r`.  Hence their difference

```text
z_(g,h)=[epsilon(g,h)C_gC_h-alpha(g,h)C_(gh)]
          tensor u_(gh)^epsilon                         (OHS7)
```

also lies in that multiplicative domain and satisfies
`r(z_(g,h)^*z_(g,h))=0`.  Pairing with `tau_alpha` and using `(OHS4)` gives

```text
[epsilon(g,h)C_gC_h-alpha(g,h)C_(gh)]p=0.              (OHS8)
```

Therefore the nonzero finite-dimensional unitaries `U_g` form an exact
projective representation with multiplier

```text
delta=alpha epsilon^(-1).                              (OHS9)
```

This difference is one of the four odd Maslov classes, contradicting
`finite-metaplectic-morita-shifts-cannot-reach-odd-maslov-fibres` and
Deligne finite-dimensional invisibility.

Consequently an LLP proof through a split odd-to-even ucp retract cannot
retain exact matrix homogeneity at all.  The formerly surviving
"macroscopic boundary killed by a nonfaithful retract" does not rescue an
exactly homogeneous embedding; any surviving retract must break that
homogeneity before the multiplicative-domain support extraction applies.

DERIVATION
canonical-trace-support-extracts-finite-projective-coefficient
