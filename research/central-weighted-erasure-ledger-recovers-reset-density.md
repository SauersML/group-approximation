---
rg: 2
id: central-weighted-erasure-ledger-recovers-reset-density
kind: claim
title: Central-weighted erasure cleaning charges block-adaptive reset density to bad parity energy
distinct_from:
  soundness-unique-neighbors-give-erasure-cleaning: that produces one support S(E) for one unweighted erased-row set in the cleaning range; this integrates block-dependent sets and handles blocks outside the cleaning range by charging their entire trace.
  block-adaptive-sparse-reset-is-cheap: that bounds displacement and induced balanced energy once blockwise coordinate sets are given; this bounds their trace-weighted density from the parity energy.
  all-dual-unique-neighbors-contract-operator-tails: that contracts coordinate tail cardinalities down to a bad-row floor on one block; this converts the resulting block-dependent bad-row sets into a globally summable reset ledger.
---

Let `H:F_2^L->F_2^M`, `C=ker H`, satisfy `(SUN1)--(SUN2)`, put

```text
kappa=min(alpha/(2a),gamma alpha/2),       nu=M/L,       (CWE1)
```

and assume `nu<=nu_+`.  Let `(z_omega)` be a finite or countable reducing
PVM with weights `lambda_omega=tau(z_omega)`.  On each nonzero block use the
normalized trace `tau_omega=lambda_omega^(-1)tau(z_omega .)` and let
`e_(h,omega)>=0` be its parity-row residual amplitudes.  For `rho>0` put

```text
E_omega={h:e_(h,omega)>rho},
E_par=(1/M)sum_(omega,h) lambda_omega e_(h,omega)^2.     (CWE2)
```

There are block-dependent coordinate sets `S_omega` such that

```text
ker H_(rows outside E_omega)
 <=C+F_2^(S_omega)                                      (CWE3)
```

on every block, and

```text
sum_omega lambda_omega |S_omega|/L
 <=nu_+ max(gamma^(-1),kappa^(-1)) E_par/rho^2.          (CWE4)
```

For blocks with `|E_omega|<kappa L`, take the set supplied by `(SUN4)`, so
`|S_omega|<=|E_omega|/gamma`.  For every remaining block take ALL `L`
coordinates.  This makes `(CWE3)` trivial there, but does not lose control:
the weight of an exceptional block is charged by
`|E_omega|/(kappa L)`.

The estimate remains valid for a reducing direct integral by measurable
approximation (or by integrating the same pointwise inequalities).  No
common coordinate set is required.

There is also a weighted AUT ledger.  On every block in the small-tail
range, `(AUT2)` integrates verbatim:

```text
sum_omega lambda_omega |U_((w-1)t+2rho),omega|/L
 <=(1-gamma/D) sum_omega lambda_omega |U_(t,omega)|/L
   +(M/(DL)) E_par/rho^2,                               (CWE5)
```

where the sums may be restricted to the small-tail blocks.  Blocks outside
that range are handled by the full-block reset above and are charged by the
same Markov ledger.  Thus central decomposition does not destroy the unique-
neighbor contraction factor or its bad-row normalization.

Finally apply `block-adaptive-sparse-reset-is-cheap`.  Resetting the
coordinates `S_omega` has average squared generator displacement and
induced balanced-overlay energy at most

```text
C_H E_par/rho^2,                                        (CWE6)
```

with `C_H` depending only on `a,alpha,gamma,nu_+` and the bounded incidence
constants.  In the balanced quadratic overlay, every original parity row is
repeated `Theta(M)` times among `Theta(M^2)` faces, so its normalized layer
energy is comparable to `(1/M)sum_h e_h^2`; hence `E_par<=C_bal E_bal`.
This is the promised recovery of the `L` factor: although the chosen reset
set varies with the central block, `M=Theta(L)` converts weighted bad-row
fraction directly into weighted coordinate density.

This theorem solves only counting and summability AFTER a common reducing
decomposition and its blockwise bad-row sets have been constructed.  It
does not manufacture those projections; that remains exactly
`central-adaptive-peeling-or-noncentral-stopping`.

