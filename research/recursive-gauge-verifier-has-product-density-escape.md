---
rg: 2
id: recursive-gauge-verifier-has-product-density-escape
kind: claim
title: Identical tensor-natural gauge verifiers have exact marked prefixes and only product-density common carriers
distinct_from:
  exact-code-prefixes-have-matrix-ultraproduct-model: that diagonalizes any supplied sequence of exact marked prefixes; this proves that installing the same verifier in every independent multiplicity gauge supplies such prefixes and computes the resulting carrier density.
  recursive-clifford-tail-supplies-anchor-but-not-contraction: that gives a concrete Clifford-tree stationary model; this isolates the general tensor-natural mechanism and the exponential loss in the common verifier carrier.
  extensive-cosystolic-index-defect: that asks bounded-overlap local syndromes to pay relator energy; this proves why merely repeating one positive-density local anomaly cannot provide that payment.
---

**ESTABLISHED NO-GO.**  Let `R_n` be an increasing sequence of finite unitary
relation packets with a fixed marked word `w`.  Suppose there is a
finite-dimensional exact verifier packet `(V,e)`, where `e` is a reducing
verifier spectral projection of normalized trace `alpha in (0,1]`, and a tensor-natural
extension operation with the following property.  Assume `R_0` has an exact
finite-dimensional seed model in which `w` has normalized-HS separation at
least `beta>0`.  From every exact marked
model `U` of `R_n` on `H`, it constructs an exact model of `R_(n+1)` on
`H tensor V`, the old named words act as their old values tensored with the
identity, and

```text
w(U^(n+1)) = w(U) tensor I_V.                            (TRG1)
```

The new level may use arbitrary simultaneous multiplicity gauges: conjugating
all new verifier data by `I_H tensor G`, `G in U(V)`, still gives an exact
extension.  Then every finite depth has an exact finite-dimensional model with
exactly the same normalized-HS marked separation as the seed.  Consequently
the full recursive library has a marked tracial matrix-ultraproduct model.

Moreover, in the depth-`N` tensor model the `N` level carriers

```text
e_j = I tensor ... tensor e tensor ... tensor I
```

commute and each has trace `alpha`, but their common reducing carrier has

```text
tau(e_1 e_2 ... e_N) = alpha^N.                         (TRG2)
```

Thus a fixed positive verifier density at every level does not produce a
fixed positive-density carrier on which all levels act.  If `alpha<1`, the
common carrier vanishes exponentially.  If `alpha=1`, the exact tensor-prefix
models still show that repetition alone charges no relator energy.  Independent
gauge conjugations do not alter either conclusion.

This rules out the bare self-aware prescription “make every uncontrolled
multiplicity gauge carry the same verifier.”  It can succeed only after adding
a genuinely non-tensor-natural, cross-level mechanism: for example summable
losses on jointly reducing carriers, a bounded-overlap index syndrome tied to
the fixed mark and paid by relator energy, or a finite semantic transducer
which has no marked matrix completion.  Merely copying the verifier, even at
positive local density and even recursively, gives the finite-prefix/CAR
escape rather than a matrix-only anomaly.
