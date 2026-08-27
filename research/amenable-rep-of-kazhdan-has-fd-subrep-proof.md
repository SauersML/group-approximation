---
rg: 2
id: amenable-rep-of-kazhdan-has-fd-subrep-proof
kind: route
title: Powers–Størmer into the Hilbert–Schmidt representation, then property (T)
target: amenable-rep-of-kazhdan-has-fd-subrep
requires: []
artifacts:
  - notes/TRUE_CHARGE_EXTENSION_NEEDS_COAMENABILITY.md
---

# Powers–Størmer into the Hilbert–Schmidt representation, then property (T)

Direct establishment; the complete argument is Proposition 3 of the artifact.
`requires: []` is a proof commitment, not a placeholder.

Four standard ingredients, none specific to this problem: weak-\* density of
normal states in the state space of `B(H)`; Day's convexity trick, upgrading
weak-\* almost invariance to `‖·‖₁` almost invariance; the Powers–Størmer
inequality `‖a^{1/2} − b^{1/2}‖₂² ≤ ‖a − b‖₁`, which converts almost invariant
density operators into almost invariant unit vectors of `Ad π` on
`HS(H) ≅ H ⊗ H̄`; and the spectral theorem for trace-class operators, which
makes a nonzero spectral projection of `T^*T` finite rank.

Property (T) is used once, in its defining form — almost invariant vectors give
a nonzero invariant vector — applied to the Hilbert–Schmidt representation
rather than to `π` itself. That is the whole trick, and it is why the
conclusion is finite-dimensionality rather than the existence of an invariant
vector in `π`.

**No citation is being carried.** The corresponding published statement is
Bekka's, and it was not readable; the route establishes the claim rather than
importing it, so nothing here inherits a trust surface.
