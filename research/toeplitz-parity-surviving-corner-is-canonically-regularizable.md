---
rg: 2
id: toeplitz-parity-surviving-corner-is-canonically-regularizable
kind: claim
title: Every surviving Toeplitz parity corner admits a canonical old-group regularization
artifacts:
  - research/toeplitz-parity-balanced-regularization-proof.md
distinct_from:
  canonical-marked-corner-nonamenable-density-vanishes: that starts with canonical marked-corner traces; this manufactures that trace profile from an arbitrary surviving norm-corona or tracial-ultraproduct corner.
  weak-mf-embedding-not-reusable: that rules out padding and ordinary amplification of a hostile embedding; this changes the character by retained balanced tensor powers and uses the concrete trivial-scalar-kernel theorem.
---

**ESTABLISHED PROPERTY-`(T)`-FREE.**

Suppose a norm-matrix-corona homomorphism of `H_T` retains `J`. Cut to the
nonzero negative spectral corner and polar-correct coordinates so that

```text
U_n(J)=-I.
```

There are integers `k_n->infinity` and asymptotic representations

```text
V_n(s)
 =U_n(s) tensor
  (U_n(s) tensor conjugate(U_n(s)))^(tensor k_n)         (TPR1)
```

such that

```text
V_n(J)=-I,
tr(V_n(g))->delta_(g,1)       for every g in Lambda.     (TPR2)
```

The same conclusion holds starting from normalized-HS microstates instead
of operator-norm microstates.

Consequently, the adjoint moments of `V_n|Lambda` converge to those of the
regular representation. Since `Lambda` is nonamenable, Kesten's criterion
gives zero low-energy adjoint density for every fixed cutoff below its
regular spectral gap. No Property `(T)` input is used.

DERIVATION
toeplitz-parity-balanced-regularization-proof
