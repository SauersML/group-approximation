---
rg: 2
id: tensor-products-cannot-cancel-noncentral-hs-defect
kind: claim
title: Tensor products cannot cancel genuinely noncentral Hilbert--Schmidt defect
distinct_from:
  balanced-parity-excludes-perfect-matching-pauli-mixtures: that rounds exact projective Pauli sectors; this proves that an arbitrary tensor cancellation is quantitatively projective before any Pauli classification.
  bounded-participation-tensor-networks-are-not-diffuse-far: that counts factor supports and invokes bounded type; this controls cancellation between arbitrarily many tensor factors without a participation bound.
  diagonal-tensor-trace-powers-forget-full-gns-tensor: that concerns diagonal character powers and loss of a bad GNS algebra; this is an elementary normalized-HS scalarization inequality for independent tensor factors.
---

Let `(M_f,tau_f)`, `f in F`, be finite tracial algebras and let `U_f` be
unitaries.  Put `U=tensor_f U_f` and

```text
d_f^2 = min_(lambda in T)||U_f-lambda I||_2^2
      = 2(1-|tau_f(U_f)|),
d_tensor^2 = min_(lambda in T)||U-lambda I||_2^2
           = 2(1-prod_f |tau_f(U_f)|).                    (TSC1)
```

If `||U-I||_2^2<=1`, then

```text
sum_f d_f^2 <= 2 d_tensor^2 <= 2||U-I||_2^2.             (TSC2)
```

The same assertion holds with any scalar target in place of `I`.
In particular, exact cancellation

```text
tensor_f U_f=lambda I
```

forces every `U_f` to be scalar.  Tensor factors can cancel scalar phases,
but they cannot cancel genuinely noncentral operator content.

For tensor-product reflection tuples

```text
Q_i=tensor_f Q_i^(f),
```

apply `(TSC2)` to each factor parity word.  Apply it to a pair `(i,j)` with

```text
U_f=(Q_i^(f)Q_j^(f))^*(Q_j^(f)Q_i^(f));                  (TSC3)
```

then `||tensor_f U_f-I||_2^2=||[Q_i,Q_j]||_2^2`.  Thus
vanishing global parity and complete-pair defect forces the summed distance
of all factor parity words and relative commutators from **some scalar** to
vanish.  Cross-factor cancellation leaves only scalar phase/coherence data;
it cannot itself create the genuinely noncentral diffuse sector.

This does not exactify the resulting approximate scalar phases into one
coherent projective representation when the number of coordinates and
factor types grow.  That approximate-projective coherence problem is the
remaining possible instability.
