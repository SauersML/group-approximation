---
rg: 2
id: oracular-affine-support-replacement-dichotomy-proof
kind: route
title: Incidence reconstruction forces one unsafe edge and finite affine profiles give the LCS OR
target: oracular-affine-support-replacement-has-no-intermediate-regime
requires:
  - matrix-conj-forces-unsafe-support
  - finite-linear-commutation-system-to-lcs
  - finite-lcs-product-sign-is-exact-or
---

Apply the constraint-variable incidence conversion to the unique-trace
magic-square--AND block of `matrix-conj-forces-unsafe-support`.  On every
incidence edge, zero loss and faithfulness identify the variable PVM with the
appropriate marginal of the constraint PVM.  Hence every perfect tracial
incidence model reconstructs a representation of the block algebra
`M_4(C)` and has its normalized trace.  The AND-context--`A` edge therefore
has support

```text
{(000,0),(010,0),(100,1),(111,1)}.
```

The odd xor of its first three points is `(110,1)`, which is outside the
accepted incidence relation.  Thus no perfect model of this fixed finite
oracular `2`-CSP is affine-safe on every sampled edge.

For an instance-changing compiler, enumerate at every edge every affine
subset of its finite accepting truth table.  For each global choice, impose
the defining affine equations and all required within-question and
cross-edge commutators.  The first required claim converts that finite
linear/commutation system to an LCS.  An affine-safe perfect model selects one
enumerated profile and satisfies its LCS.  Conversely every model of a
profile LCS has joint edge spectrum in a subset of the original accepting
relation, and so forgets to a model of the compiler output.  Therefore all
profile branches remain matrix-ultraproduct-unsatisfiable on a sound input.

Use the exact product-sign OR to combine the finite list.  It preserves the
complete branch and decodes every marked ultraproduct model to a nonzero
corner of one branch.  This produces one effective perfect-completeness LCS
family.  The reverse reduction regards an LCS as an oracular Boolean CSP;
all of its accepted relations are affine, so every positive support is
automatically affine-safe.
