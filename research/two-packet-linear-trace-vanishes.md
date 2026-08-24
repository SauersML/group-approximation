---
rg: 2
id: two-packet-linear-trace-vanishes
kind: claim
title: Both linear terms in the Leavitt two-packet correction have zero identity coefficient globally
distinct_from:
  both-rank-three-factors-must-be-packet-corrected: that derives the full bilinear packet equation but imposes no coefficient constraint; this proves a global identity-coefficient vanishing theorem for its two linear terms.
  two-packet-solution-requires-relative-double-coset-folding: that excludes relatively free conjugators by syllable support; this applies to every conjugator and uses a conjugacy invariant of square-zero endomorphisms.
artifacts:
  - research/artifacts/leavitt-packet-trace-and-compression-2026-08-24.md
  - research/artifacts/check_linear_identity_invariant.py
  - research/artifacts/verify-kl-gate-c3-corner.py
---

Let `tau:S->F_2` be coefficient of the identity.  For the explicit corner
factors `A,B` and every `x in G`,

```text
tau(A P_x)=0,        tau(P_x B)=0.
```

The quantifier is over the entire Leavitt unit group.  Exact Bergman normal
form reduces a possible identity monomial to seven involutions in either of
two finite double-coset sets: the identity and six elementary or symmetric
nilpotent perturbations with coefficient `t_i` on the `A` side or `s_i` on
the `B` side.  A nontrivial constant transposition is conjugate to none of
them because its square-zero difference from the identity has equal image and
kernel, while each of the six candidates has image properly contained in
kernel.
