---
rg: 2
id: homomorphic-codes-cannot-compress-bernoulli-shifts
kind: claim
title: No equivariant homomorphic or affine code compresses a uniform Bernoulli shift into a smaller alphabet
distinct_from:
  measurable-certificate-routing-preserves-bernoulli-measure: that excludes codes routing each output datum from one input datum; this excludes codes combining many input symbols through a group homomorphism or a linear map, the synergistic codes routing cannot produce.
  linear-invariant-output-automata-fail-augmentation: that excludes linear automata with involution-invariant output over F_2; this excludes every homomorphic or affine alphabet-compressing code over every countable group, almost everywhere.
artifacts:
  - research/artifacts/measurable-alphabet-compression-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Let `G` be a countable group, `A, B` finite groups with `|B| < |A|`, and `tau: A^G -> B^G`
equivariant and a homomorphism for the pointwise product, possibly followed by a translation of
`B^G`. Then `tau` is not injective on any set of full uniform product measure. In particular no
`F`-linear or affine equivariant code `(F^m)^G -> (F^n)^G` with `m > n` over a finite field is
injective almost everywhere.

*Proof sketch.* `tau` maps constants to constants, so it restricts to a homomorphism `A -> B` on
them, which has a nontrivial kernel element `a`. Right multiplication by the constant configuration
`c_a` is measure-preserving and never changes `tau`. Section 5 of the artifact.

So a measurable compression over the Leavitt units, the open prerequisite of
`leavitt-zero-supremum-via-measurable-compression`, must be genuinely nonlinear, even when it combines
many input symbols.

**ESTABLISHED 2026-09-12** by [[homomorphic-codes-cannot-compress-proof]].
