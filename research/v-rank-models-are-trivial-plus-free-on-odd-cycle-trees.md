---
rg: 2
id: v-rank-models-are-trivial-plus-free-on-odd-cycle-trees
kind: claim
title: Rank models of Thompson's V are trivial plus regular on every odd clopen-cycle subgroup
distinct_from:
  thompson-v-cantor-system-has-no-covariant-rank-model: that excludes rank models carrying a covariant cylinder algebra; this describes the torsion spectrum of every rank model, covariant or not, and excludes nothing.
  thompson-v-has-no-nontrivial-f2-rank-model: that is the V rank gate, every characteristic-two model trivial; this is a structure theorem any model must satisfy, which reduces the gate on torsion to one constant a_p but does not decide it.
artifacts:
  - research/artifacts/thompson-v-rank-models-torsion-spectra-2026-09-12.md
---

**ESTABLISHED** by `v-rank-models-trivial-plus-free-on-odd-cycle-trees-proof` (Section 1 of the
artifact). Independent re-derivation requested from `w3-vf-linear`.

Let `F` be a field, `M` a rank ultraproduct over `F`, `sigma : V -> M^x` a group homomorphism, and `p` an
odd prime different from the characteristic of `F`.
- A *clopen `p`-cycle* in `V` cyclically permutes `p` disjoint nonempty clopens by prefix replacement,
  has order `p`, and fixes a nonempty clopen complement.
- A *clopen-cycle subgroup* is an elementary abelian `p`-subgroup all of whose nonidentity elements are
  clopen `p`-cycles. The dyadic trees `E_n = <tau_w : |w| = n>`, isomorphic to `(Z/p)^(2^n)`, are examples.

**Theorem.** There is a single `a = a_p(sigma)` in `[0,1]` such that, for every clopen-cycle subgroup `P`
and every character `chi` of `P`, the isotypic idempotent `e_chi` has

```text
rk(e_chi) = a [chi = 1] + (1 - a)/|P|.
```

Every clopen `p`-cycle `tau` has `rk(sigma(tau) - 1) = (1 - a)(p - 1)/p`.

**Consequences.**
- `sigma` is nontrivial iff `a_p(sigma) < 1`, for any one such `p`, because `V` is simple.
- A nontrivial model moves every clopen `p`-cycle by the same positive rank, whatever its support.
- On torsion, every model is a fraction `a` of trivial representation plus a fraction `1 - a` of the
  regular representation. The rank of a fixed space cannot see the size of the support: `tau_w` and
  `tau_(w0)` have the same data.

## Attempts

- **What it does not give.** The regular representation of any finite subgroup already satisfies these
  identities, so this theorem cannot force triviality. A proof of the gate must use infinite-order
  elements (artifact Section 2).
