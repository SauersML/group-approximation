---
rg: 2
id: hrf-nonrf-via-stable-kazhdan-central-prime
kind: route
title: A stable hyperbolic Kazhdan group with positive second Betti number gives invisible prime central extensions
target: non-residually-finite-hyperbolic-group
requires:
  - kazhdan-hyperbolic-b2-group-flexibly-hs-stable
  - hrf-audit-stability-forces-prime-central-finite-residuals
artifacts:
  - research/artifacts/hyperbolic-rf-stability-audit-2026-09-20.md
---

Choose the group Gamma in the first premise. The second premise constructs
an integral central cover E with property (T) and an integer M such that
all finite quotients kill z^M. For any prime p not dividing M, E/<z^p>
is word-hyperbolic and its nontrivial central C_p is invisible in every
finite quotient. It is therefore not residually finite.

The existence of the stable Gamma is OPEN. GHB7's congruence kernel is a
specific candidate, through the existing route
`kazhdan-hyperbolic-b2-stability-via-ghb7-kernel`. This deduction does not
use nonhyperlinearity, hyperlinearity, or any assumed residual finiteness
of Gamma. It is a direct route to the user's residual-finiteness target.
