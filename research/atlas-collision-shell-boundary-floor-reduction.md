---
rg: 2
id: atlas-collision-shell-boundary-floor-reduction
kind: route
title: Use collision centrality to enter the nontrivial S3 shell
target: atlas-six-relator-regular-face-defect-floor
requires:
  - atlas-finite-nontrivial-s3-shell-pays-boundary
  - atlas-19243-centrality-forces-s3-distance
---

Let

```text
e_c(U)=||pi_U(c_19243)-1||_2,
m_nt(U)=||U-E_K(U)||_2^2,
D_6(U)=B_5(U)+e_c(U)^2.
```

The collision-distance theorem gives

```text
dist_2(U,U(rho(K)'))
 >= max(0,(sqrt(2)-e_c(U))/16).                       (CSB1)
```

Polar rounding of the conditional expectation `E_K(U)` gives a unitary
`V in rho(K)'` satisfying

```text
||U-V||_2^2<=2||U-E_K(U)||_2^2=2m_nt(U).              (CSB2)
```

If `e_c(U)^2>=1/2`, then already `D_6(U)>=1/2`.  Otherwise
`e_c(U)<sqrt(2)/2`, so `(CSB1)--(CSB2)` imply

```text
2m_nt(U)
 >= dist_2(U,U(rho(K)'))^2
 >= (sqrt(2)/32)^2=1/512,
```

and hence

```text
m_nt(U)>=1/1024.                                      (CSB3)
```

Apply `atlas-finite-nontrivial-s3-shell-pays-boundary` to obtain
`B_5(U)>=beta_5`.  Therefore every finite regular common frame satisfies

```text
D_6(U)>=min(1/2,beta_5),                              (CSB4)
```

which is the claimed multiplicity-independent scalar floor.
