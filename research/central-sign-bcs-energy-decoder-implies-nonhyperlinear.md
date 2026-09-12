---
rg: 2
id: central-sign-bcs-energy-decoder-implies-nonhyperlinear
kind: claim
title: A positive-mass central-sign BCS energy decoder implies nonhyperlinearity
distinct_from:
  central-packet-sign-supplies-marked-carrier: that rounds a separated central involution and quantifies the negative carrier; this combines that carrier with the robust non-CE BCS energy gap and records the normalized-versus-unnormalized trace factor needed for the final contradiction.
  non-ce-bcs-has-robust-approximate-energy-gap: that proves a dimension-independent energy floor for a fixed BCS in its own normalized matrix trace; this is the verifier-to-group criterion after the BCS tuple has been decoded on a central-sign corner.
  perfect-lcs-gap-implies-nonhyperlinear: that specializes the argument to the native solution group of a linear system; this permits an arbitrary finite verifier and arbitrary finitely presented central-sign decoder.
---

**ESTABLISHED.**  Fix a finite BCS `B` with robust normalized-HS energy gap
`beta_B>0` from `non-ce-bcs-has-robust-approximate-energy-gap`.  Let
`Gamma=<S|R>` be finitely presented and contain a central involution word
`J`.  Suppose:

1. `Gamma` has an exact tracial representation in which `J=-I` and the
   intended decoded BCS tuple has zero energy;
2. for every sufficiently accurate finite-dimensional tuple `U`, central
   spectral rounding and block correction produce an exact reducing negative
   projection `Q_U`, corner unitaries `Z_x(U)`, and constants `kappa,C>0`
   such that

   ```text
   kappa E_B^amb(Q_U,Z(U))
      <= C Def_R(U)^2+eta(Def_R(U)),                    (VGC1)
   ```

   where `eta(t)->0` and the energy is measured in the **ambient normalized
   trace**:

   ```text
   E_B^amb(Q,Z)=sum_(P in R_B) ||P(Z)Q||_(2,d)^2.       (VGC2)
   ```

Then `Gamma` is nonhyperlinear.

The exact representation in clause 1 proves `J!=1`.  If `Gamma` were
hyperlinear, take canonical-trace matrix microstates `U_n`.  The central
involution exactification theorem gives

```text
tau_d(Q_(U_n))->1/2.                                    (VGC3)
```

For all large `n` the corner is nonzero.  Applying the robust BCS gap with
the corner's own normalized trace gives the exact normalization formula

```text
E_B^amb(Q_(U_n),Z(U_n))
  =tau_d(Q_(U_n)) E_B^corner(Z(U_n))
  >=beta_B tau_d(Q_(U_n)).                              (VGC4)
```

Thus the left side of `(VGC1)` has liminf at least
`kappa beta_B/2`, while its right side tends to zero.  This contradiction
proves the claim.

## Normalization and rounding audit

The factor `tau(Q)` in `(VGC4)` is mandatory.  A normalized corner gap
`beta_B` does not become an ambient gap of size `beta_B`; it becomes
`beta_B tau(Q)`.  Conversely no additional division by `tau(Q)` is allowed
in `(VGC1)`, which is stated using ambient normalized Hilbert--Schmidt norm.

One may replace canonicality by a fixed mark-separation assumption.  If
`||J(U)-I||_2>=alpha` and the relator defect is small, then
`central-packet-sign-supplies-marked-carrier` gives
`tau(Q)>=alpha^2/16`; the lower bound in `(VGC4)` becomes
`beta_B alpha^2/16`.

The raw operator `(I-J(U))/2` need not be a projection or reduce the decoded
letters.  Spectral rounding must first replace `J(U)` by an exact involution,
and the generator blocks must be diagonalized and polar-corrected as in
`central-involution-corner-exactification`.  These perturbations are harmless
only because the fixed BCS energy is a finite sum of fixed-degree
polynomials.  The decoder hypothesis `(VGC1)` must include their cost; it
cannot silently treat the raw negative carrier as exact.

