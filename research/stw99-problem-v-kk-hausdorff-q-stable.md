---
rg: 2
id: stw99-problem-v-kk-hausdorff-q-stable
kind: claim
title: KK(A, B) is Hausdorff for separable nuclear A and separably Q-stable B (STW Problem V)
root: true
distinct_from:
  stw99-problem-iii-r-omega-uct: that computes KK(A, R-omega) exactly; this asks only for Hausdorffness of the KK-topology, for all separably Q-stable targets, and the R-omega instance follows from that problem.
artifacts:
  - research/artifacts/stw99-uct-cluster-2026-08-30.md
  - research/artifacts/stw-operator-literature-exact-imports-2026-08-30.md
---

**Problem V of Schafhauser--Tikuisis--White, arXiv:2506.10902.**  For
separable nuclear `A` and (separably) `Q`-stable `B` (`Q` the universal
UHF algebra), is `KK(A, B)` Hausdorff — i.e. `KL(A, B) = KK(A, B)`?

`Q`-stability makes `K_*(B)` a `Q`-vector space, hence divisible, so
under the UCT `α : KK(A,B) → Hom(K_*A, K_*B)` is an isomorphism into a
Hausdorff group and the closure of zero dies
(`stw99-uct-implies-kk-hausdorff`).  The `B = R^ω` instance follows from
Problem III.  Carrión--Schafhauser's UCT-free continuity of `KL(·, B)`
is the adjacent known unconditional result.

Carrion, arXiv:2608.06496v1, Theorem 1.1, Corollary 4.3, and Proposition
4.5, now identify the obstruction exactly.  For nuclear `A` and any shape
system `(C_n)` for `SA tensor K`, the closure of zero in `KK(A,B)` is

```text
lim^1 [C_n,S^2 B tensor K].
```

Thus `KK(A,B)` is Hausdorff exactly when this group vanishes
(`carrion-shape-milnor-detects-kk-hausdorffness`).  What remains in Problem V
is the precise assertion that separable `Q`-stability of `B` forces that
vanishing; the Milnor theorem itself does not supply it.

## Attempts

Divisibility of `K_*(B)` alone cannot suffice (STW: "should not put many
restrictions on KK"), so any unconditional proof must use `Q`-stability
of the algebra `B` itself, presumably through Dadarlat--Winter-type
absorption as in the strongly self-absorbing case of Problem III.  A
counterexample would be a nonzero `κ ∈ KK(A, B)` in the closure of zero
— approximately trivial but nontrivial — against a `Q`-stable target,
which no known construction produces for nuclear `A`.
