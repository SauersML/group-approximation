---
rg: 2
id: canonical-trace-does-not-weaken-thin-commutant-transfer
kind: claim
title: Residual-finite tensor camouflage makes canonical and unrestricted thin-subgroup commutant transfer equivalent
distinct_from:
  canonical-iwahori-transfer-is-equivalent-to-full-transfer: that proves the analogous statement for the two-vertex Iwahori transfer problem; this is the one-vertex auxiliary-unitary statement needed by the thin SL_n(Z) HNN route.
  residual-finite-tensor-camouflages-iwahori-transfer-failures: that treats failed Iwahori projection transfer; this proof applies directly to arbitrary auxiliary unitaries and subgroup commutators.
---

Let `A = <S | R>` be finitely presented and residually finite, let
`C = <c_1,...,c_k> <= A`, and fix `a in A`.  The following are equivalent.

1. Every sequence of unitary tuples `U_n` with defining-relator defect
   tending to zero, and every sequence `v_n in U(d_n)`, satisfies

   ```text
   max_i ||[v_n,c_i(U_n)]-1||_2 -> 0
       implies ||[v_n,a(U_n)]-1||_2 -> 0.               (CT1)
   ```

2. The same assertion holds after restricting to sequences with canonical
   character:

   ```text
   tr(g(U_n)) -> 0 for every 1 != g in A.               (CT2)
   ```

The forward implication is immediate.  For the converse, suppose `(CT1)`
fails.  Enumerate the nonidentity elements of `A` as `g_1,g_2,...`.  By
residual finiteness, for every `n` choose a finite quotient `q_n:A->Q_n`
such that

```text
q_n(g_j) != 1 for 1 <= j <= n.                         (CT3)
```

Let `lambda_n` be the left regular representation of `Q_n` and put

```text
U_tilde_n(s) = U_n(s) tensor lambda_n(q_n(s)),
v_tilde_n    = v_n tensor 1.                            (CT4)
```

Every defining relator has exactly the old normalized-HS defect, and every
subgroup or marked commutator has exactly the old normalized-HS norm.  But

```text
tr(g_j(U_tilde_n))
 = tr(g_j(U_n)) tr(lambda_n(q_n(g_j))) = 0              (CT5)
```

whenever `j <= n`.  Thus `(U_tilde_n,v_tilde_n)` is a canonical-character
failure of `(CT1)`, contradicting item 2.

For `A = SL_n(Z)` this applies because the lattice is residually finite.
Consequently canonical group-trace side tests select useful local finite
types but cannot remove a failure of the terminal thin-subgroup commutant
transfer: an arbitrary failure can be hidden behind a regular finite-quotient
tensor factor at zero normalized-HS cost.
