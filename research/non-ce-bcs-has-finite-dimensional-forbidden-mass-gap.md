---
rg: 2
id: non-ce-bcs-has-finite-dimensional-forbidden-mass-gap
kind: claim
title: A BCS with a tracial but no Connes-embeddable tracial state has a dimension-free forbidden-mass floor
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
distinct_from:
  mipstar-bcs-tracial-nonru-exists: that is the existence, from MIP*=RE, of a finite BCS with a tracial model but no R^U model; this is what such a system then forces on every finite-dimensional contextwise-commuting tuple, and it is a compactness statement with no complexity input of its own.
  zpc-context-overlap-mismatch-transducer: that asks a compiler to charge selector overlap and cross-context mismatch to the loss of a specific game; this is an unconditional lower bound on forbidden spectral mass and asks for no compiler.
  perfect-zpc-irs-quantum-gap-game: that is a finite game separation forced by TailoredMIP*=RE; this is an elementary ultraproduct consequence once such a separation is fixed.
---

Let `B` be a finite Boolean constraint system with variable set `X`, contexts
`c` with variable sets `U_c`, and forbidden assignment sets `F_c`.  Assume the
BCS algebra of `B` has a tracial state but **no Connes-embeddable** tracial
state; `mipstar-bcs-tracial-nonru-exists` supplies such a `B` unconditionally.

Then there is a constant `beta_B > 0`, depending only on `B`, such that for
every dimension `d` and every tuple `(Z_x)_(x in X)` of self-adjoint involutions
in `M_d(C)` whose members commute exactly within each context,

```text
sum_c sum_(a in F_c)
   tau_d( prod_(x in U_c) (I + (-1)^(a_x) Z_x)/2 )  >=  beta_B.    (FMG)
```

Each summand is the normalized trace of a genuine joint spectral projection, so
the left side is exactly the total forbidden-assignment mass of the tuple.

**What this is for.**  It is the sharpest available form of "failure cannot be
diluted": no single context need be badly violated, and no relation need carry
large error, but the *total* forbidden mass is bounded below uniformly in the
dimension.  It supplies the positive local violation mass that
`bounded-overlap-syndrome-energy-accounting` needs as input, without any PCP,
soundness amplification, or expander construction.

**Read the hypothesis carefully.**  Exact contextwise commutation is assumed;
this is a statement about tuples that already satisfy the commutation half of
the BCS exactly, and only the constraint half is being measured.  A version
allowing approximate commutation would need a separate perturbation argument
and is not claimed here.
