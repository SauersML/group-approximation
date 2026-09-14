---
rg: 2
id: kazhdan-representations-have-no-hs-compression-models
kind: claim
title: Finite-rank compressions of a Kazhdan representation with no finite-dimensional subrepresentation are uniformly far from Hilbert–Schmidt almost-representations
distinct_from:
  kazhdan-almost-invariant-corner-near-invariant-projection: that is the operator lemma replacing an almost-invariant finite-rank projection by an invariant one; this applies it to compressions and records the firewall for spatial hyperlinear models.
  kazhdan-irreducible-compressions-have-quadratic-defect: that bounds the defect when a few dimensions are removed from a finite-dimensional irreducible representation of a finitely presented Kazhdan group; this treats compressions of infinite-dimensional representations with no finite-dimensional part, where the defect is bounded below by a constant.
artifacts:
  - research/artifacts/sk-hyperlinear-boundary-a-reduction-2026-09-13.md
---

ESTABLISHED by `kazhdan-representations-have-no-hs-compression-models-proof` (unreviewed).

Let `Gamma` have a Kazhdan pair `(S, kappa)` with `S = S^(-1)` finite, and let `pi : Gamma -> U(H)` have no nonzero
finite-dimensional subrepresentation. Put `epsilon_0 = min(1/968, kappa^2/242)`.

For every projection `P != 0` of finite rank `d`, the compression `C(g) = P pi(g) P` satisfies

```text
max_(s in S) || C(s) C(s^(-1)) - P ||_(2,d)  >=  epsilon_0,        || X ||_(2,d) = d^(-1/2) || X ||_HS .
```

**Firewall.** An infinite simple finitely generated group has no nontrivial finite-dimensional unitary
representation, by Mal'cev and simplicity. So for an infinite simple Kazhdan group, any unitary representation
without invariant vectors satisfies the hypothesis.

Examples: the regular representation, `ℓ^2(Gamma/H)` for `H` of infinite index, and the permutation representations on
boundary orbits and on orbit modules. Hilbert–Schmidt models of such a group are therefore never compressions of one
fixed representation. For `S_∂` they must moreover be non-permutational, since `S_∂` is nonsofic.
