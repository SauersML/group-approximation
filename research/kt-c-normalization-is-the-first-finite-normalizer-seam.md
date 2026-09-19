---
rg: 2
id: kt-c-normalization-is-the-first-finite-normalizer-seam
kind: claim
title: The first mixed Kun--Thom normalizer seam is a finite family of maximally open C-normalization words
distinct_from:
  kt-ab-normalizer-row-forces-wall-gauge-propagation: that estimates two candidate copies after the C-normalization row has been imposed; this proves that the row is a genuinely new quotient relation and has maximal defect in the canonical compatible AFP paste.
  kt-full-actor-cocycle-loops-admit-exact-wreath-wall: that closes every actor loop in the exact non-CE wreath model; this works in a Connes-embeddable amalgam model before the mixed normalization kernel is killed.
  kt-one-compressor-and-sl3-normalizer-lifts-paste: that constructs the compatible lift of the two vertex groups; this identifies an explicit finite kernel family that the lift must additionally annihilate in order to descend to `G`.
---

**ESTABLISHED FINITE SEAM.**  Retain

```text
P_A=H_A *_<A> S,         C=A B^(-1) in S,              (KCS1)
```

and choose a finite generating set `T` of the Kazhdan group `Gamma`.  Since
`C` cyclically permutes the polynomial variables, it normalizes `Gamma`.
For `gamma in T` define

```text
w_gamma=C gamma C^(-1) alpha_C(gamma)^(-1) in P_A.     (KCS2)
```

Every `w_gamma` is nontrivial in `P_A`, but its image under the natural
quotient `P_A->G` is trivial.  In the trace-correct normalizer lift of
`kt-one-compressor-and-sl3-normalizer-lifts-paste`,

```text
tau(u(w_gamma))=0,
||u(w_gamma)-1||_2^2=2.                                (KCS3)
```

Thus the known one-compressor and `SL_3(Z)` splittings do not merely fail to
come with a preferred identification: they admit a common exact
Connes-embeddable paste, and each first mixed normalization row is maximally
open in its canonical trace.  Descending that paste to the full actor
requires a macroscopic kernel-closing operation.

Because `T` is finite, `(KCS2)` is a finite nonabelian cocycle seam.  Killing
these words enforces `C`-covariance on all of `Gamma`; it is a necessary but
not asserted sufficient condition for killing the full kernel of
`P_A->G`.  Accordingly this result neither constructs nor obstructs the full
normalizer lift.  It localizes the first genuinely mixed finite equations
after all subgroup and overlap compatibility has been discharged.

DERIVATION
kt-c-normalization-seam-proof
