---
rg: 2
id: gauge-weyl-fanizza-incidence-rounding
kind: claim
title: Place two-sided gauge bridges along the Fanizza incidence without losing shared-word payment
distinct_from:
  two-sided-pauli-gauge-bridge-preserves-spin-scale: that proves one conditional finite connector; this must choose the logical overlap at every Fanizza transition and sum the corrected-word losses.
  c18-source-cut-has-sparse-relator-certificate: that transfers C18 forbidden mass on the original shared words; this must keep those words fixed while renewing only private gauges.
---

Gauge-double the variables in the fixed Fanizza BCS and order its finitely many
packet incidences so that each reset edge carries the logical variables used
by the adjacent source/child certificate. Attach the two-sided Pauli bridge
conditional on that logical overlap, and prove:

1. each original logical word is the product of its two local shares up to the
   defining relator error;
2. the bridge renews only the private gauge coordinate and leaves all logical
   products fixed;
3. the source-local forbidden-mass estimates, including the sparse C18 cut,
   survive packet exactification with total loss `C_M sqrt(E)`; and
4. every packet occurrence has bounded overlap in the finite presentation.

The constants may depend on the compiled machine but not on matrix dimension
or computation runtime. The exact marked model is obtained by gauge-orbit
covariantization and arbitrary infinite amplification, so no tracial
extension through the bridge is required.

## Attempts

- Sharing only the spin packet loses every old/new selector correlation.
- Direct Weyl translation of an original BCS variable does not preserve its
  other constraints. Gauge doubling fixes both failures at the algebraic
  level.
- The remaining audit is combinatorial and quantitative: choose the logical
  overlap for the three factored predicate shapes and verify that no original
  word is omitted from the source-cut payment when its private gauge is
  renewed.

`fanizza-product-gram-reduces-to-one-state-holonomy` now separates this audit
into a tree part and one cycle part.  After rooting at `C_D`, the `O_Q` leaf
and tree transports have no holonomy loss.  The only extra state-dependent
moment is

```text
||(V_R^*U_(Z->R)V_Z-I)G||_2^2.
```

An exact common multiplicity amplification can make this term maximal while
all present finite gauge and HNN edge relations remain exact.  Therefore the
four edgewise checks above cannot by themselves complete the incidence
rounding; one mixed triangle relation or positive verifier compression must
charge this moment on the same `G`.

There is a literal minimal triangle repair.  With transports oriented
`D->Z`, `D->R`, and `Z->R`, add the two-cell

```text
U_ZR U_DZ=U_DR.
```

It is compatible with the exact marked model after common countable
amplification: choosing `U_cd=V_dV_c^*` makes the equality tautological.
This removes cycle holonomy but still leaves the load-bearing task of
producing one positive-norm Gram block accepted by all rooted context rows.
