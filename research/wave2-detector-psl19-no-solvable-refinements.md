---
rg: 2
id: wave2-detector-psl19-no-solvable-refinements
kind: claim
title: The explicit PSL2(19) first quotient has no nontrivial solvable-kernel refinement, including for every nonzero central five-twist
distinct_from:
  hrf-alt-psl2-detectors-need-new-composition-factors: that excludes a composition-factor class without fixing a quotient map; this excludes arbitrary mixed-prime solvable-kernel refinements of one explicit canonical quotient using integral perfectness of its kernel
artifacts:
  - research/artifacts/hyperbolic-rf-wave2-detectors-2026-09-20.md
---

For the explicit `Λ -> Q=PSL_2(19)` and kernel `N` of
[[wave2-detector-psl19-perfect-first-kernel]], every factorization

```
Λ ->> F ->> Q
```

with solvable kernel of `F -> Q` has trivial kernel: it is the canonical
quotient up to isomorphism. This excludes all finite refinements with
solvable kernel, regardless of its primes or derived length.

For every nonzero twist `c in F_5^3`, let `Λ_c` be the edge-twisted
central `C_5` extension. Its preimage `N_c` of `N` is also perfect.
Consequently every factorization `Λ_c ->> F ->> Q` with solvable kernel
of `F -> Q` kills the entire kernel of `Λ_c -> Q`, including its central
`C_5`. No such finite refinement detects the twist.

This is relative to the stated canonical map. A finite detector may
still exist with a nonsolvable kernel over that map, including a perfect
kernel having a nontrivial solvable radical. Those cases remain open.

**Status:** independently reviewed written theorem using the exact kernel
computation, which was also independently reproduced; see Section 7
of `research/artifacts/hyperbolic-rf-wave2-audit-2026-09-20.md`.

Proof: [[wave2-detector-psl19-no-solvable-refinements-proof]].
