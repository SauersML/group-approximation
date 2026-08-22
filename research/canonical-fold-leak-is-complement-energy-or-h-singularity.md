---
rg: 2
id: canonical-fold-leak-is-complement-energy-or-h-singularity
kind: claim
title: A canonical fold leak pays complement synchronization energy or h-singularity
distinct_from:
  projective-transfer-reduces-to-complement-unitary-extension: that gives the upper transfer estimate for an arbitrary nondegenerate polar compression; this applies its contrapositive to the maximal mixed moment forced by a canonical arithmetic-double model.
  fixed-projective-leak-forces-polar-singular-collapse: that extracts a bad singular band for some named ambient generator from aggregate compression leakage; this gives the sharper alternative between singularity of the fold generator h itself and a fixed lower bound for every complement extension.
  sl3-regular-double-bass-serre-rigidity-firewall: that exhibits the exact infinite regular block-swap counterconfiguration; this quantifies the obstruction faced by finite exact-dilation/polar realizations of that configuration.
---

**ESTABLISHED DICHOTOMY.**  Use

```text
C=SL_3(Z)<A=SL_3(Z[1/2]),
h=diag(2,1,1/2),                                        (CFL1)
```

and the exact projective-transfer constant `K` of
`projective-transfer-reduces-to-complement-unitary-extension`.  Let
`pi_n:A->U(H_n)` be exact, let `P_n` have rank `m_n>0`, and let `rho_(n,s)`
be the polar unitary of

```text
T_(n,s)=P_n pi_n(s)P_n.                                 (CFL2)
```

Suppose `U_n in U(P_nH_n)` has the canonical fold-leak profile

```text
sum_(c in S_C) [1-|tr([U_n,rho_(n,c)])|^2] -> 0,
1-|tr([U_n,rho_(n,h)])|^2 -> 1.                         (CFL3)
```

For every fixed `sigma>0`, one of the following holds:

1. the least singular value of `T_(n,h)` is below `sigma` for infinitely
   many `n`; or
2. eventually `|T_(n,h)|>=sigma P_n`, and the scaled
   complement-extension energy satisfies

   ```text
   liminf_n J_C(U_n)>=sigma^2/(8K),                     (CFL4)
   ```

   where

   ```text
   J_C(U_n)=(dim(H_n)/m_n) inf_(Z in U((1-P_n)H_n))
      sum_(c in S_C)[1-|tr_Hn([U_n direct_sum Z,pi_n(c)])|^2]. (CFL5)
   ```

Indeed, on a subsequence with `|T_(n,h)|>=sigma P_n`, the established
complement-transfer estimate gives

```text
1-|tr([U_n,rho_(n,h)])|^2 <=(8K/sigma^2)J_C(U_n).       (CFL6)
```

Taking the lower limit and using `(CFL3)` proves `(CFL4)`.

The hypothesis `(CFL3)` is exactly the mixed canonical moment of the full
arithmetic double when its two vertex tuples are put on the diagonal and
`U_n` is the factor swap: the amalgamating words make the `C` energy vanish,
while canonical trace of the nontrivial fold word makes the `h` commutator
trace vanish and its projective energy tend to one.

Thus full canonicality does **not** provide the missing complement unitary.
On every nondegenerate exact-dilation sector it quantitatively certifies that
no such low-energy complement exists.  A successful correction theorem must
instead show that this fixed complement floor, or the alternative failure of
a uniform lower singular bound for `T_h`, is paid by the original
normalized-HS presentation defect.  No positive density of the low-singular
space is asserted here.  Singular-value data alone cannot provide the needed
payment, by
`canonical-exact-polar-models-have-flat-singular-loss`; the payment must use
the joint block-swap/boundary incidence.

This remains a reduction rather than a proof of fold collapse.  Arbitrary
canonical double microstates need not come from polar compressions of exact
ambient `A`-representations, and no current estimate charges `(CFL4)` to
their relator energy.

There is now an explicit raw form of the missing charge.
`complement-energy-is-bounded-by-polar-modulus-and-boundary` tests the
complement infimum with the identity and proves that `(CFL4)` forces a fixed
amount of either lattice-compression modulus mismatch under the block swap or
lattice boundary leakage.  Thus the complement variable itself can be
eliminated from the terminal; what remains is to control those two raw
matrix-coordinate quantities by full-double relator energy.
