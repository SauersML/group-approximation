---
rg: 2
id: atomic-schreier-multiplicity-leakage-proof
kind: route
title: Compare projection overlap with scalar square-root multiplicity and apply the Schreier gap
target: one-sided-pvm-leakage-controls-schreier-multiplicity
requires: []
---

Fix `s` and abbreviate

```text
P=U_sQ_chi U_s^*,              R=Q_(s chi).
```

Both are projections, with traces `q_chi` and `q_(s chi)`.  Tracial
Cauchy--Schwarz gives

```text
tau(PR)<=sqrt(tau(P)tau(R))=sqrt(q_chi q_(s chi)).     (1)
```

Therefore

```text
(sqrt(q_chi)-sqrt(q_(s chi)))^2
 <=q_chi+q_(s chi)-2tau(PR)
 =||P-R||_2^2.                                         (2)
```

Because `Omega` is invariant, `chi |-> s chi` permutes it.  Summing the
last expression in `(2)` and using orthogonality of the PVM gives

```text
sum_chi ||P-R||_2^2
 =sum_chi(q_chi+q_(s chi)-2tau(PR))
 =2sum_chi(q_chi-tau(PR))
 =2sum_chi||(1-R)U_sQ_chi||_2^2
 =2L_s.                                                 (3)
```

The left side of `(2)`, summed over `chi`, is precisely
`||f-sf||_2^2`.  This proves `(ASL3)`.

The scalar vector `f` is finitely supported because the matrix PVM is.
Apply `(ASL4)` and then `(ASL3)` for every actor generator:

```text
kappa mass(Omega)
 =kappa||f||_2^2
 <=sum_s||f-sf||_2^2
 <=2sum_sL_s.                                           (4)
```

Division by `kappa` proves `(ASL5)`.  Under the additional marked-packet
lower bound `mass(Omega)>=c mu`, the same inequality gives `(ASL6)`.
Nothing in `(1)--(4)` constructs the PVM, estimates `L_s` from finitely many
group words, or supplies the uniform proper-stabilizer gap, which proves the
scope fence in the claim.
