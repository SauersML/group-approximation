---
rg: 2
id: six-moving-squares-give-el20-multicut
kind: route
title: Lock the seven moving stage gauges with six authenticated coefficient squares
target: growing-multicut-el20-order-seven-inheritance
requires:
  - six-ungauged-moving-squares-lock-seven-gauges
  - el20-six-moving-coefficient-square-bridges
  - native-whitehead-hecke-head-has-order-seven-anchor
---

The coefficient interface independently supplies the common positive source,
the seven moving cuts and charts, the native transitions, and the ungauged
bridges.  Apply `(ESB3)` to the six-square estimate `(SGL5)`.  Put

```text
delta_(i,k)=epsilon_(i,k)+eta_(i,k+1)+eta_(i,k)
             +zeta_(i,k+1)+zeta_(i,k).
```

Then

```text
||D_(i,j)-D_(i,0)||_2 <= sum_(k<j) delta_(i,k).       (GMC8)
```

The moving-cut telescope and the literal seventh-power relation give

```text
rho_i <= seventh-power defect
         +sum_(k=0)^5 ||(1-E_(i,k+1))T_iE_(i,k)||_2
         +sum_(k=0)^6 eta_(i,k),                     (GMC9)
```

with the exit sum optionally replaced by the corresponding Cauchy--Schwarz
bound.  Therefore `(SGL7)` yields the explicit dimension-free estimate

```text
||D_(i,0)-1||_2
 <= rho_i+sum_(k=0)^5 (6-k) delta_(i,k).              (GMC10)
```

For globally normalized norms divide by `sqrt(tr(E_0))`; the interface's
uniform positive lower bound on `tr(E_0)` keeps the modulus dimension-free.
Thus `D_(i,0)=1+o_2(1)` for both rows.  Since both cycles start on the same
signed Hecke source, the common-source cross-Gram and mixed Pauli typing are
preserved.
