---
rg: 2
id: sl2-half-explicit-strict-flexible-separation
kind: claim
title: PSL2(Z[1/2]) has an explicit rank-one Weil sequence separating strict from flexible HS stability
distinct_from:
  iwahori-local-global-defect-question: that asks for flexible repair of every almost-compatible modular pair; this gives a sequence that defeats strict repair but is flexibly repaired by exactly one dimension.
  even-weil-fixed-line-compression: that supplies the packet calculation; this packages it as a global stability statement and adds the uniform same-dimensional separation.
  iwahori-torsion-multiplicity-stratum-reconciliation: that asks for a general padding theorem; this is the sharp one-missing-dimension model any such theorem must contain.
---

There is a sequence of unitary tuples `phi_p` for
`PSL_2(Z[1/2])`, indexed by primes `p=1 mod 4`, with

```text
dim(phi_p)=(p-1)/2,
presentation_defect(phi_p)=O(p^(-1/2)),               (SFS1)
```

such that:

1. the `BS(1,4)` relation is exact in every `phi_p`;
2. for one constant `c>0`, every exact representation `sigma` of the same
   dimension satisfies
   
   ```text
   max_(g in {x,r,s}) ||phi_p(g)-sigma(g)||_2 >= c;   (SFS2)
   ```
   
   after allowing arbitrary unitary conjugacy of `sigma`;
3. the exact `(p+1)/2`-dimensional even Weil representation `pi_p` satisfies

   ```text
   d_2(phi_p,pi_p)=O(p^(-1/2))                        (SFS3)
   ```

   in the generalized flexible Hilbert--Schmidt metric.

Thus `PSL_2(Z[1/2])` is explicitly not **strictly** HS stable, while this
sequence creates no obstruction at all to flexible HS stability.  The defect
is a single deleted fixed line: normalized defect is `Theta(d^(-1/2))` and
the necessary relative dimension change is exactly `1/d`.

This gives a concrete arithmetic witness for the general strict-instability
phenomenon behind Becker--Lubotzky, but with the additional feature that the
entire amenable `BS(1,4)` skeleton remains exact.
