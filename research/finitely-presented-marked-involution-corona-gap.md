---
rg: 2
id: finitely-presented-marked-involution-corona-gap
kind: claim
title: Killing one marked involution in every norm-matrix corona is equivalent to a uniform presentation gap
artifacts:
  - GroupApproximation/Sofic/ApproxInvolutionCorner.lean
distinct_from:
  finitely-presented-full-radical-uniform-relator-gap: that characterizes total MF-radical collapse by forcing every generator close to the identity; this is the one-mark version and detects only the negative spectral cut of a prescribed involution.
  atomic-three-row-compiler-is-prototype-gap-equivalent: that packages the same compactness mechanism together with a particular three-row compiler and a normal-generation conclusion; this isolates the presentation-gap statement needed before any decoder is chosen.
---

Let

```text
Gamma=<s_1,...,s_k | r_1,...,r_m>
```

be a finitely presented group, let `w` be a word whose value in `Gamma` is
an involution, and put

```text
Def_R(U)=max_j ||r_j(U)-I||_op.
```

For a unitary tuple `U`, let `w_hat(U)` be the canonical rounded involution
of `w(U)` and let `P_-(U)` be its negative spectral projection.  The
following statements are equivalent.

1. Every homomorphism from `Gamma` to a sequential norm-matrix corona sends
   `w` to the identity.
2. There is a constant `gamma>0`, independent of the matrix dimension, such
   that

   ```text
   P_-(U)!=0  =>  Def_R(U)>=gamma                         (MIG1)
   ```

   for every finite-dimensional unitary tuple `U`.

Thus invisibility of one finite-order mark is already a uniform finite-stage
gap.  In particular, any proposed decoder whose only small-defect obligation
is conditional on `P_-(U)!=0` can become vacuous below `gamma`; occurrence
typing alone does not prevent that circularity.

