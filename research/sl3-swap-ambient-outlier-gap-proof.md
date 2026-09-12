---
rg: 2
id: sl3-swap-ambient-outlier-gap-proof
kind: route
title: Insert the swap involution into the unbalanced-torus projective estimate
target: sl3-swap-fold-gap-forces-ambient-outlier
requires:
  - unbalanced-torus-extracts-near-central-denominator-coordinate
---

Fix an exact representation `sigma:A->U(d)` and put

```text
xi=max_(t in S)||X_t-sigma(t)||_2.
```

All words below are fixed.  Hence there are constants `L,L_R` depending
only on the chosen representatives such that

```text
||X_c-sigma(c)||_2<=L xi                              (SAG5)
```

for every lattice word occurring in `S_+`, in `h^(-1)S_+h`, or in
`R_tor`, and changing the lattice letters in the torus word costs at most
`L_R xi`.

Apply `(NCD2)` of
`unbalanced-torus-extracts-near-central-denominator-coordinate` with
`U=S_0`.  For a lattice generator `t`,

```text
||[S_0,sigma(t)]-1||_2
 =||S_0 sigma(t)-sigma(t)S_0||_2
 <=||S_0 X_t-X_t S_0||_2+2 xi.                        (SAG6)
```

Here the bracket on the left is the multiplicative group commutator.
Since `1-|tr(Y)|^2<=||Y-1||_2^2` for a unitary `Y`, summing `(SAG6)` gives

```text
q_C(S_0)<=2b+8|S|xi^2.                                (SAG7)
```

For `c in S_+`, write `c'=h^(-1)c h` and
`W=H sigma(h)^*`.  The exact identity
`sigma(h)^*sigma(c)=sigma(c')sigma(h)^*` gives

```text
||[W,sigma(c)]||_2
 =||H sigma(c')-sigma(c)H||_2
 <=||H X_(c')H^*-X_c||_2+2L xi.                       (SAG8)
```

Therefore

```text
a_+(W)<=2r+8L^2|S_+|xi^2.                             (SAG9)
```

If `eta_sigma` denotes the torus defect with the exact lattice packet
`sigma|_C`, fixed-word telescoping also gives

```text
eta_sigma<=eta+L_R xi,
eta_sigma^2<=2eta^2+2L_R^2xi^2.                       (SAG10)
```

Substitute `(SAG7)`, `(SAG9)`, and `(SAG10)` into `(NCD2)`.  Enlarging one
constant yields

```text
1-|tr([S_0,H])|^2<=C_0(b+r+eta^2+xi^2).               (SAG11)
```

The fold unitary `F=H S_0 H^*S_0` satisfies

```text
[S_0,H]=S_0 H S_0 H^*=F^*,                            (SAG12)
```

so the trace moduli in `(SAG2)` and `(SAG11)` agree.  Taking the infimum
over exact same-dimensional ambient `sigma` proves `(SAG2)` (use an
infimizing sequence if the infimum is not attained).  Rearranging and
passing to a liminf proves `(SAG4)`.

For a double-swap microstate, `b`, `r`, and `eta` tend to zero because they
are defects of fixed consequences of its finite presentation, while the
canonical trace of the nontrivial reduced fold word tends to zero.  Thus
`(SAG4)` applies.  Notice that no implication from ambient extendability to
lattice correctability was used; making that implication would erase the
primary-conductor obstruction and is precisely why this argument stops at
the advertised ambient-extension outlier.
