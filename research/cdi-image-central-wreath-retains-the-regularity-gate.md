---
rg: 2
id: cdi-image-central-wreath-retains-the-regularity-gate
kind: claim
title: The CDI image is a central wreath quotient and is regular exactly when its input image already is
distinct_from:
  cdi-wreath-extension-preserves-projective-basis-gate: that transfers vanishing modulo the scalar kernel, for use in a twisted central sector; this computes the honest kernel quotient and the untwisted regular character.
  standard-permanence-does-not-rigidify-the-cdi-image: that rules out importing rigidity by external group operations; this gives the intrinsic normal form of the actual CDI image and tests its distinguished character.
  cdi-standard-generator-choice-fails-projective-gate: that exhibits one intermediate input coefficient; this shows exactly what that coefficient does after passing to the actual image quotient.
---

Use CDI Proposition 3.8 with a homomorphism

```text
pi_0:A -> U(M),             pi_0(A)''=M,
pi_tilde:G -> U(N),         G in WR(A,B),
N=M^B rtimes_(beta,w) B.
```

Put `Gamma=pi_0(A)`, `S=Gamma intersect T1`, and
`Lambda=pi_tilde(G)`.  Then `Lambda` has an exact sequence

```text
1 -> D -> Lambda -> B -> 1,                              (CIW1)
D = gamma(Gamma^(B)),
ker(gamma:Gamma^(B)->D)
  = {(s_b): s_b in S, finite support, product_b s_b=1}. (CIW2)
```

In particular `S` is central in `Lambda`,

```text
D/S ~= (Gamma/S)^(B),
Lambda/S in WR(Gamma/S,B).                              (CIW3)
```

Let `chi_Gamma=tau_M|Gamma` and let `chi_Lambda` be the faithful
distinguished character inherited from `N`.  Then

```text
chi_Lambda is the regular character of Lambda
iff
chi_Gamma is the regular character of Gamma.            (CIW4)
```

Consequently the CDI image construction preserves, rather than creates, the
untwisted canonical-trace gate.  If `M` contains a non-Connes-embeddable
tracial algebra, then `N` is non-CE.  Thus any assertion that every
nonregular factorial character of this actual `Lambda` is CE, applied to
`chi_Lambda` itself, forces `(CIW4)` and already makes
`M=L(Gamma)` non-CE.  It has therefore produced a nonhyperlinear group at the
input image before character classification of `Lambda` is used.

For the legitimate Ge--Popa generator choice in
`cdi-standard-generator-choice-fails-projective-gate`, `chi_Gamma` has a
strictly intermediate coefficient.  Hence `chi_Lambda` is an explicit
nonregular non-CE extremal character of the corresponding actual CDI image.
The open image-classification route can only concern a specially engineered
choice of generators; it is false for this standard allowed choice, and
engineering a choice for which the distinguished character is regular is
already the nonhyperlinear-group problem.
