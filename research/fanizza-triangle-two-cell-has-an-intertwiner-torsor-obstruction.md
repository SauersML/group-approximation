---
rg: 2
id: fanizza-triangle-two-cell-has-an-intertwiner-torsor-obstruction
kind: claim
title: The global Fanizza triangle two-cell is developable exactly when three intertwiner torsors close
distinct_from:
  fanizza-product-gram-reduces-to-one-state-holonomy: that proves the analytic value of killing the triangle holonomy and proposes the literal two-cell; this audits whether that global relation preserves an exact marked extension.
  gauge-doubling-gives-selector-flip-symmetries: that provides automorphisms of each private incidence chart and finite-orbit covariantization; this shows why nonempty edge intertwiner spaces do not automatically satisfy their cycle equation.
  common-source-hnn-bridges-need-one-gram-saturation-identity: that audits common selected source projections; this is an exact representation/developability condition before any finite-dimensional Gram estimate.
---

Consider the native triangle with oriented edge embeddings

```text
D->Z, D->R, Z->R.                                     (FTC1)
```

Fix exact vertex representations `pi_D,pi_Z,pi_R` on one Hilbert space after
any desired common amplification.  For an edge `e:c->d`, let

```text
I_e(pi)
 ={U unitary:
     U pi_c(h) U^*=pi_d(phi_e(h)) for every h in H_e}  (FTC2)
```

be its unitary-intertwiner torsor.  Here `H_e` includes the actual finite
logical/private-gauge edge data, not merely its central sign.

## Exact developability criterion

The three edge representations extend across the global triangular two-cell

```text
U_ZR U_DZ=U_DR                                        (FTC3)
```

if and only if

```text
I_DR(pi) intersects I_ZR(pi) I_DZ(pi) nontrivially.   (FTC4)
```

This is immediate: an extension supplies a product in the intersection;
conversely a factorization of an element of `I_DR` as a product of elements
of the other two torsors supplies the three stable-letter unitaries.  In
terms of arbitrary initial choices, `(FTC4)` is the assertion that their
cycle holonomy can be removed by multiplying the edge implementers by
unitaries in the corresponding edge-restriction commutants.  It is a
double-coset/cocycle condition, not a dimension condition.

Countable amplification proves at most

```text
I_DZ(pi), I_ZR(pi), I_DR(pi) are individually nonempty. (FTC5)
```

It does not imply `(FTC4)`.  A two-dimensional model already shows the
logical gap.  Let the first two torsors consist of unitaries preserving the
spectral decomposition of a balanced involution `Z`, while the direct torsor
consists of unitaries conjugating `Z` to an anticommuting balanced involution
`X`.  All three torsors are nonempty, but a product of the first two still
preserves `Z` and cannot lie in the third.  Infinite common amplification
does not change that covariance obstruction.

## What is valid for the native Fanizza data

At the level of the three logical separator signs

```text
(O_Q,O_P,Z_tilde),                                    (FTC6)
```

the obstruction vanishes.  The native triangle is classically flat: all
eight triples extend to its four contexts.  After infinite replication one
may realize the three signs on one common diagonal triple-character space
and choose the separator intertwiners flat.  Thus `(FTC3)` does not impose a
forbidden global Boolean assignment and does not identify the full context
selector algebras.

What has **not** been proved is `(FTC4)` for the full two-sided Pauli gauge
bridges.  Their edge implementers also identify private diagonal and
transverse Weyl charts.  Gauge-orbit covariantization makes every individual
edge torsor nonempty and fixes the retained logical words, but it does not
show that the product automorphism on the private multiplicity/Weyl
coordinates equals the direct-edge automorphism.  That is precisely the
cycle cocycle in `(FTC4)`.

There is, however, no inherent obstruction when the gauge registers are
literally incidence-private tensor factors.  Suppose

```text
H=H_logical tensor K_DZ tensor K_ZR tensor K_DR tensor K_aux, (FTC6a)
```

the edge group for `e` acts trivially on `K_f` for `f!=e`, and its required
private reset is a unitary `W_e` on `K_e`.  Suppose also that the logical
separator implementers have been chosen flat:

```text
L_DR=L_ZR L_DZ.                                       (FTC6b)
```

Choose `U_ZR` to implement `L_ZR` and `W_ZR`.  Choose `U_DZ` to implement
`L_DZ` and `W_DZ`, and additionally let it act by `W_DR` on the unconstrained
factor `K_DR`.  Then put

```text
U_DR=U_ZR U_DZ.                                       (FTC6c)
```

The product has logical action `L_DR`, has the required private action
`W_DR` on `K_DR`, and its extra actions on `K_DZ,K_ZR` are invisible to the
direct edge group.  Thus all three edge covariance laws and the two-cell hold
exactly.

This factorized construction shows that `(FTC3)` need not identify the full
context packet algebras or destroy the marked representation.  To turn it
into a completed HALT-extension proof, one must still exhibit the simultaneous
Schur/Pauli packet extension in which the gauge-doubled incidence registers
really have the factorization `(FTC6a)`.  Gauge doubling makes that design
plausible, but the current finite packet incidence note has not proved the
simultaneous factorization.

Accordingly the literal relation `(FTC3)` is a valid candidate, but exact
HALT completeness is conditional on an explicit full-packet solution of
`(FTC4)`.  The shortcut

```text
U_cd=V_d V_c^*                                        (FTC7)
```

is valid only after constructing context identifications `V_c` which
simultaneously realize every finite edge chart.  Assuming such `V_c` is
equivalent to assuming `(FTC4)`; countable amplification alone does not
construct them.

## What remains even if `(FTC4)` is solved

If the two-cell is developable, its relator makes the triangle term in
`(FPG19)` vanish identically.  The following rows remain load-bearing:

1. **One nonzero Gram block:** construct a fixed word/Hecke block `G` with
   ```text
   ||G||_2^2>=gamma q-o(1).                            (FTC8)
   ```
   Consecutive positive packet overlaps do not imply this; their product may
   be zero.
2. **Predicate acceptance on that same state:** prove
   ```text
   sum_c||F_cV_cG||_2^2<=K E_rel+o(1).                (FTC9)
   ```
   Local existence of allowed packet types is insufficient.
3. **Anchor-to-Bob covariance on that same state:** prove
   ```text
   sum_x||A_(a(x),x)V_(a(x))G
                    -V_(a(x))GB_x||_2^2
      <=K E_rel+o(1).                                 (FTC10)
   ```
   This includes the private prescribed Fanizza words, not only the three
   separators.
4. **Tree-edge covariance:** finish the fixed Fanizza incidence wiring so
   that the `e_edge` row is bounded.  Individual fixed context/tag bridges
   have the required telescoping estimates, but
   `gauge-weyl-fanizza-incidence-rounding` is still open as a complete
   assembly.

Thus a successful global two-cell removes exactly one obstruction: cycle
gluing.  It does not supply Gram mass, selected-predicate acceptance, or the
semantic anchor rows.  Those three state-dependent rows remain the actual
projection-free groupification problem.
