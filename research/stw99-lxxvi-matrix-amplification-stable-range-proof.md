---
rg: 2
id: stw99-lxxvi-matrix-amplification-stable-range-proof
kind: route
title: Compare tensor amplification with block sum inside the pi5 stable range
target: stw99-lxxvi-unital-matrix-subalgebra-kills-s6-class
requires: []
artifacts:
  - research/artifacts/stw99-lxxvi-fourth-depth-audit-2026-08-30.md
---

Let

```text
rho_k:U(2)->U(2k),             rho_k(u)=u tensor 1_k.
```

After conjugating by a fixed permutation unitary, `rho_k(u)` is the block
sum of `k` copies of `u`.  Therefore, after mapping to the stable unitary
group `U`,

```text
(s_(2k) o rho_k)_*(alpha)=k (s_2)_*(alpha).             (3)
```

The stable group `pi_5(U)=Z` is torsion free by Bott periodicity.  Since
`alpha` has order two, `(s_2)_*(alpha)=0`, and hence the right side of (3)
is zero.  This use of block sum is essential: tensor amplification is not
the ordinary corner stabilization, but it becomes `k`-fold addition after
passing to the stable unitary group.

It remains to return from `U` to the finite target `U(2k)`.  The standard
fibration

```text
U(n) -> U(n+1) -> S^(2n+1)
```

shows from its long exact homotopy sequence that

```text
pi_j(U(n)) -> pi_j(U(n+1))
```

is an isomorphism for `j<2n`.  With `n=2k` and `j=5`, the inequality

```text
5<4k
```

holds for every `k>=2`.  Every later stabilization map is also an
isomorphism in degree five.  Thus

```text
(s_(2k))_*:pi_5(U(2k))->pi_5(U)
```

is an isomorphism, in particular injective.  Equation (3) now forces

```text
(rho_k)_*(alpha)=0 in pi_5(U(2k)).                      (4)
```

Finally, a unital embedding `M_k->D` makes the scalar inclusion
`C->D` factor through `M_k`.  Applying `M_2`, unitary groups, and `pi_5` to
that factorization sends (4) to zero in `pi_5(U(M_2(D)))`, proving the
claim.
