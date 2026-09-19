---
rg: 2
id: hs-full-rank-scalar-defect-blocks-naive-rank-decoding
kind: claim
title: Full-rank scalar defects defeat amplification, quotient, and multiplicative threshold HS-to-rank decoders
distinct_from:
  growing-rank-decoder-is-linear-soficity: that identifies the approximation property a successful growing decoder would produce; this gives exact counterexamples to three proposed constructions of such a decoder.
  hs-steinberg-root-kernel-is-linear-sofic: that is an open structured decoder using Steinberg root-character orbits; this obstruction applies to unstructured singular-value or defect-kernel procedures and does not refute the root-character route.
  spherical-defect-congruence-preserves-separation: that asks whether geometric permutation defect congruence preserves word separation; this concerns direct conversion of HS-small operator defects to rank-small linear defects before any spherical matching.
artifacts:
  - research/artifacts/hs-to-rank-naive-decoder-no-go-2026-08-21.md
---

There is no dimension-free conversion from normalized-HS-small matrix defects
to normalized-rank-small defects by any combination of:

1. direct-sum or tensor amplification;
2. restriction to the common kernels of the defects, or quotient by their
   images; and
3. a multiplicative spectral clipping rule which is locally constant at the
   identity.

Choose arbitrarily small `epsilon` with `epsilon/(2 pi)` irrational.  The
scalar defect `D_epsilon=(exp(i epsilon)-1)I_d` has HS norm tending to zero but
normalized rank one.  Every direct-sum and positive tensor amplification of
the underlying scalar unitary still has full-rank defect, while its defect
kernel is zero and its image is the whole space.  Finally any group
homomorphism out of `U(1)` that kills a neighbourhood of the identity is
trivial, since that neighbourhood generates `U(1)`.  Thus relationwise
spectral clipping cannot be made multiplicatively coherent while retaining
any scalar separation.
