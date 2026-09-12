---
rg: 2
id: stw82-raw-two-cut-reuse-iff-quasidiagonal
kind: claim
title: Raw complementary-cut colour reuse is equivalent to a quasidiagonal extension
distinct_from:
  stw82-complementary-cutdowns-merge-iff-near-projections: that is a pointwise criterion for a sequence of positive contractions in arbitrary unital algebras; this theorem globalizes it along a quasicentral approximate unit and identifies the resulting extension property exactly as quasidiagonality.
  stw82-order-zero-direct-sum-support-criterion: that detects when two already chosen order-zero maps merge; this detects when the standard complementary cut supports can be made mergeable along an extension.
---

Let

```text
0 -> I -> E -> D -> 0
```

be an extension of separable C*-algebras.  The following conditions are
equivalent.

1. The extension is quasidiagonal: `I` has an approximate unit `(p_n)` of
   projections which is quasicentral in `E`.
2. There is a positive contractive quasicentral **almost-idempotent**
   approximate unit `(h_n)` for `I` relative to `E`, meaning
   `h_(n+1)h_n=h_n`, such that

   ```text
   norm(h_n(1-h_n)) -> 0.                              (Q1)
   ```

3. There is such an almost-idempotent `(h_n)` and positive contractions
   `a_n,b_n` in the
   unitization of `E` satisfying

   ```text
   a_n b_n=0,
   norm(a_n-h_n) -> 0,
   norm(b_n-(1-h_n)) -> 0.                            (Q2)
   ```

Thus the raw two-piece Winter--Zacharias cut can have its complementary
supports perturbed into orthogonal supports asymptotically exactly in the
quasidiagonal-extension regime.  In particular, this method gives no
strictly larger class than the already known quasidiagonal-extension
maximum theorem.

This equivalence concerns only perturbation of the **raw complementary
cuts**.  It is not an obstruction to the nuclear-dimension maximum formula:
non-quasidiagonal extensions such as the Toeplitz extension can obey that
formula after their transition region is reorganized.
