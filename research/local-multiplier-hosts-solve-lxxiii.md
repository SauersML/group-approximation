---
rg: 2
id: local-multiplier-hosts-solve-lxxiii
kind: claim
title: Local properly infinite multiplier hosts solve individual LXXIII cutdowns
artifacts:
  - research/artifacts/problem-lxxiii-literature-audit-2026-08-30.md
distinct_from:
  finite-packets-fuse-after-one-stabilization: that constructs the fused nilpotent in M_2(A); this theorem returns it inside any local host containing the reserved spectral cutdown.
  chain-ideal-lattice-solves-lxxiii: that selects one packet member by comparability of ideals; this uses no ideal-lattice hypothesis and instead destabilizes the entire packet locally.
---

Let `A` be any C-star algebra, let `a in A_+`, and let `epsilon>0`.  Put

```text
c=(a-epsilon/2)_+.
```

Suppose that `c` belongs to a C-star subalgebra `B subset A` whose multiplier
unit is properly infinite.  Then there is `x in B` such that

```text
x^2=0,
(a-epsilon)_+ in Ideal_B(x) subset Ideal_A(x).
```

No representation-theoretic hypothesis on `A` is needed.  Consequently
Problem LXXIII has a positive answer for every `A` such that each nonzero
spectral cutdown `(a-delta)_+` is contained in some C-star subalgebra with
properly infinite multiplier unit.

This strictly extends the global multiplier theorem: one may take `B=A`
when `1_(M(A))` is properly infinite, but the host may instead depend on the
cutdown.  In particular, the conclusion applies whenever the cutdown lies in
a stable subalgebra, even if `1_(M(A))` is finite.

Thus any counterexample to Problem LXXIII has a nonzero spectral cutdown
which is contained in no C-star subalgebra with properly infinite multiplier
unit.  In particular, neither its generated hereditary subalgebra nor its
generated ideal has properly infinite multiplier unit.
