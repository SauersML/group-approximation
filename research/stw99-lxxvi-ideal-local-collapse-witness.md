---
rg: 2
id: stw99-lxxvi-ideal-local-collapse-witness
kind: claim
title: A pure algebra has ideal-local K0-equal compact classes that collapse under Z
artifacts:
  - research/artifacts/stw99-lxxvi-second-depth-audit-2026-08-30.md
---

There exist a separable pure C*-algebra `A`, projections `p,q` in
`A tensor K`, and their generated ideal `J=Ideal(p,q)` such that

```text
[p] = [q] in K_0(J),
[p] != [q] in Cu(A),
[p tensor 1_Z] = [q tensor 1_Z] in Cu(A tensor_min Z).
```

This remains open.  Such data would refute STW Problem LXXVI by failure of
injectivity of the first-factor Cu map.

## Attempts

The Toeplitz/index-boundary construction gives pure ambient-K0
noncancellation after tensoring the Toeplitz algebra with Z, but its two
classes differ in the generated ideal's `K_0`; it is therefore excluded by
`stw99-lxxvi-ideal-local-k0-protection` because the compact ideal remains
stably finite, and does not collapse.

There is a second, genuinely infinite corridor not covered by the displayed
local-K0 condition: after tensoring with Z, distinct projection classes might
become Cuntz equivalent as infinite projections without becoming
Murray--von Neumann equivalent.  Such a collapse need not preserve their
`K_0` classes.  No example of this type is known here.

Unstable vector bundles can give nonisomorphic projections with equal stable
`K_0` class in a full ideal, but the elementary homogeneous algebras carrying
the standard examples are not pure.  Tensoring them with Z makes the ambient
algebra Z-stable, so it cannot yield the required before/after failure by
simply taking the Z-stabilized algebra as `A`.

Nonseparable products such as `prod_n Z` are outside the separable convention
of the problem and also require uniform, rather than coordinatewise, Cuntz
witnesses.  No product or reduced-product example is asserted.

On the positive side, the witness cannot occur in the non-simple class
`stw99-lxxvi-locally-subhomogeneous-positive-class`, since every pure member
of that class is already Z-stable.

The proposed geometric route
`stw99-lxxvi-local-collapse-via-s6-clutching` is now closed: its scalar
rank-two survival premise is refuted by
`stw99-lxxvi-pure-coefficients-kill-scalar-unstable-homotopy`.
All stably trivial scalar clutching classes already die in simple pure
coefficients. A higher-dimensional projection counterexample would have
to use coefficient-dependent unstable homotopy, rather than scalar bundles.
