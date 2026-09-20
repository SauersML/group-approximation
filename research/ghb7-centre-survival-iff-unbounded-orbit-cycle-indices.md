---
rg: 2
id: ghb7-centre-survival-iff-unbounded-orbit-cycle-indices
kind: claim
title: The GHB_2(7) centre-survival premise is equivalent to unbounded indices of integer 2-cochains on pushed-forward cycles of finite orbit complexes
distinct_from:
  ghb7-finite-index-z-extension-center-survives: that is the open premise stated with group-theoretic central extensions; this is an equivalent purely combinatorial form on finite orbit complexes of the triangle complex, exact up to a factor 7
  z-extension-centre-orders-are-restricted-evaluation-indices: that is the general identity for any central Z-extension; this specialises it to GHB_2(7) and replaces group homology of finite-index subgroups by cellular homology of their orbit complexes
---

**ESTABLISHED.** Let `G = G_{HB_2}(7)` act on its triangle complex `Y`
(`cckw-ghb2-kms-group-structure`). For a finite-index subgroup `N` write `N\Y` for the finite orbit
complex (2-cells `N\G`, 1-cells `N\G/<x>` for `x ∈ {a,b,c}`, boundary
`∂(gT) = [g e_b] + [g e_c] − [g e_a]`), and `Z_2(N\Y;Z) = Ker ∂_2`. For `N <= K` let
`p : N\Y → K\Y` be the projection.

Fix a finite-index `K <= G` and an integer 2-cochain `ω` on `K\Y`. For finite-index `N <= K` put

```text
m_ω(N) = [ Z : ω( p_* Z_2(N\Y;Z) ) ].
```

1. **Comparison.** Let `c = e^*(ω) ∈ H^2(K;Z)` be the pullback along the edge map
   `H^2(K\Y;Z) → H^2(K;Z)`, and `e(N)` the index of
   `z-extension-centre-orders-are-restricted-evaluation-indices`. Then `m_ω(N)` divides `e(N)`, and
   `e(N)` divides `7·m_ω(N)`.
2. **Finite abelianization.** The central extension `K~` attached to `c` has finite abelianization
   iff `ω` is nonzero on `Z_2(K\Y;Z)`.
3. **Equivalence.** `ghb7-finite-index-z-extension-center-survives` holds iff there are a
   finite-index `K <= G` and an integer 2-cochain `ω` on `K\Y`, nonzero on `Z_2(K\Y;Z)`, with
   `sup_N m_ω(N) = ∞`, the supremum over finite-index normal subgroups `N` of `G` contained in `K`.

So the premise, and with it `ghb7-is-not-flexibly-hs-stable` through
`ghb7-instability-via-visible-central-extension`, is a statement about finite quotients `G → G/N`
and integer linear algebra on the complexes `N\Y`, with no group homology left.

DERIVATION
ghb7-centre-survival-orbit-cycle-index-proof

For the specified index-seven subgroup K7 and its face-zero cochain,
[[wave3-canonical-k7-class-has-primitive-evaluation]] now proves the
initial integral evaluation index e(K7)=1. It does not bound, or show
unboundedness of, the indices e(N) at deeper finite-index subgroups.
