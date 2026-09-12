---
rg: 2
id: finite-involution-corner-width-is-power-of-two
kind: claim
title: The full negative corner of a finite-group involution admits only power-of-two unital matrix widths
distinct_from:
  noncentral-frobenius-negative-corner-is-rational-matrix-algebra: that explicitly constructs full negative corners of specified noncentral involutions; this bounds the possible unital matrix widths for every involution in every finite group.
  agent-leavitt-local-spin-corner: that constructs a local matrix block using a central spin mark; this allows arbitrary noncentral involutions and proves a universal divisibility restriction on their entire negative corner.
artifacts:
  - research/artifacts/finite-involution-corner-width-is-power-of-two-2026-09-08.md
---

Let `F` be finite, let `J in F` have order two, and put
`q=(1-J)/2`. For each complex irreducible representation `rho`,
write `m_rho=rank((I-rho(J))/2)`, and let `g_J` be the gcd of
the positive integers among these ranks.

If `2^a` is the exact power of two dividing `|F|`, then

```text
g_J=2^s for some 0<=s<=a-1.
```

A unital star homomorphism `M_D(C)->q C[F] q` exists if and
only if `D` divides `g_J`. In particular `D` must be a power
of two. No centrality assumption on `J` is needed.

The unit is the whole negative projection `q`. The claim imposes
no such condition on a smaller selected corner, an infinite-group
corner, or the full augmentation complement of a larger finite
subgroup. Complexification makes the width restriction necessary
over the rationals as well, without asserting rational sufficiency.

DERIVATION
finite-involution-corner-sylow-permutation-proof
