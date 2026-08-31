---
rg: 2
id: tfd-finite-corner-collapse-and-rfd-firewall
kind: claim
title: Property TFD collapses finite corner dilations but excludes RFD without T
distinct_from:
  tfd-low-leakage-compressions-flexibly-reduce: that rounds one low-leakage projection inside a given finite-dimensional representation; this derives the global very-flexible-to-flexible consequence and identifies the RFD obstruction to producing such finite dilations.
  regular-iwahori-exactification-is-regular-branch-liftability: that identifies the open Iwahori theorem with flexible regular-microstate correction; this proves that arbitrary finite dilation size is not the obstruction and that the LLP/RFD route cannot supply the missing dilation.
  authenticated-core-union-basin-is-relative-liftability: that is the relative coordinate-lifting target; this separates it from existential MF embeddings and ucp lifts.
---

Let `Gamma=<S>` have property `(T;FD)`.

1. If the full group algebra `C^*(Gamma)` is residually
   finite-dimensional, then `Gamma` has property `(T)`.
2. Suppose maps `phi_n:Gamma->U(d_n)` admit finite-dimensional exact
   corner dilations

   ```text
   pi_n:Gamma->U(D_n),       V_n:C^(d_n)->C^(D_n)
   ```

   with no bound on `D_n/d_n`, but

   ```text
   ||phi_n(s)-V_n^* pi_n(s) V_n||_(2,d_n) -> 0          (FCR1)
   ```

   for every `s in S`. Then there are exact representations

   ```text
   sigma_n:Gamma->U(E_n),    E_n>=d_n,    E_n/d_n->1,  (FCR2)
   ```

   whose generator tuples are at generalized Hilbert--Schmidt distance
   `o(1)` from `phi_n`. If each `pi_n` factors through a finite
   quotient (or through a specified congruence quotient), the
   `sigma_n` may be chosen with the same property.

Consequently, for property-`(T;FD)` groups, finite-dimensional very
flexible Hilbert--Schmidt stability already implies flexible
Hilbert--Schmidt stability. Arbitrarily large padding is not an additional
escape hatch once the dilating representation is finite-dimensional.

For

```text
Gamma=SL_2(Z[1/2]),
```

Dogon--Vigdorovich prove property `(T;FD)`, while `Gamma` is not a
property-`(T)` group. Hence `C^*(Gamma)` is **not RFD**. Fournier-Facio and Willett, `arXiv:2603.18456v2`, Theorem 7.11,
prove very flexible stability when `Gamma` has LLP and the desired family
of endpoint representations is Fell-dense and closed under finite sums,
unitary equivalence, and subrepresentations. Taking all finite-dimensional
representations requires RFD; taking finite-quotient representations requires
property FD. Neither choice is available here because `C^*(Gamma)` is not
RFD. Thus their finite-dimensional corner theorem cannot be applied to the
regular Iwahori microstate. LLP alone gives a ucp lift, or a corner in a
possibly infinite-dimensional representation; property `(T;FD)` cannot
round that infinite-dimensional Stinespring corner because its spectral gap
is only asserted for finite-dimensional representations.

The 2026 MF amalgam theorems do not replace RFD here. MF is the existence of
a norm-microstate embedding, whereas
`authenticated-core-union-basin-is-relative-liftability` asks to lift a
**prescribed** tracial-ultraproduct homomorphism by exact coordinates.
Shulman, `arXiv:2603.13564v2`, Theorem 10, proves that
`A *_C A` is MF for an MF algebra `A` and an arbitrary subalgebra `C`,
but explicitly uses the same inclusion of `C` into both factors. The
Iwahori amalgam is twisted by the commensuration sending a primitive
parabolic to its square; that edge map does not extend to an automorphism of
`SL_2(Z)`. Her Theorem 20 characterizes a general MF amalgam by the
existence of compatible embeddings of the two factors into one norm
matrix-ultraproduct. It does not lift the prescribed tracial embedding, keep
the supplied core coordinates, or produce exact coordinate representations.

A general 2025 no-lift theorem makes the logical limitation of ultrapower
exactness explicit. Gao and Jekel, `arXiv:2512.10129`, Theorem A, construct
separable II1 factors with elementary self-ultrapower embeddings that admit
no sequence of ucp lifts. This is not an Iwahori counterexample and does not
concern finite matrix coordinates, but it rules out the generic inference
that an exact or even elementary ultrapower embedding automatically has ucp
coordinate lifts. Any positive result here must use the concrete relative
group structure.

Thus the terminal boundary is exact: any theorem that supplies a
finite-dimensional corner of the given regular microstate immediately
reduces to the desired `d_n+o(d_n)` endpoint, but neither current LLP/RFD
nor MF amalgam results supply that corner.
