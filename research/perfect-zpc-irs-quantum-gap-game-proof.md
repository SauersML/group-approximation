---
rg: 2
id: perfect-zpc-irs-quantum-gap-game-proof
kind: route
title: TailoredMIP diagonalization forces perfect ZPC-IRS completeness on a soundness instance
target: perfect-zpc-irs-quantum-gap-game
requires:
  - zpc-irs-value-computable-upper-hierarchy
artifacts:
  - research/artifacts/perfect-zpc-irs-gap-2026-08-18.md
---

Bowen--Chapman--Vidick TailoredMIP*=RE (arXiv:2501.00173, Theorem 2.31)
effectively sends a Turing machine `M` to a finite tailored game `G_M` with

```text
M halts    => a perfect finite ZPC permutation strategy exists,
M diverges => omega*(G_M)<1/2.
```

For every finite game, the inclusion `MIP* subset RE` supplies computable
increasing lower bounds `beta_t -> omega*`, exactly as used in Manzoor
Theorem 3.13.  The prerequisite supplies computable decreasing upper bounds
`alpha_t^Z -> omega_ZIRS`.

If every non-halting `M` had `omega_ZIRS(G_M)<1`, dovetail the two sequences:
accept when `beta_t>=1/2`, reject when `alpha_t^Z<1`.  Halting instances have
ZPC-IRS value and quantum value exactly one, so they eventually accept and
never reject.  Non-halting instances have quantum value below one half and,
under the supposition, ZPC-IRS value below one, so they eventually reject and
never accept.  This decides halting, contradiction.

Hence some non-halting `M_0` has `omega_ZIRS(G_M0)=1`; TailoredMIP soundness
gives `omega*(G_M0)<1/2`.  The ZPC-IRS strategy set is a closed subset of the
compact IRS strategy space and game value is continuous, so the value one is
attained.
