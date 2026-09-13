---
rg: 2
id: local-restricted-burnside-partial-burnside-proof
kind: route
title: Finite quotients of partial Burnside groups, a stabilizing chain of finite residuals, and the Coulon stages
target: local-restricted-burnside-iff-partial-burnside-finite-quotients
requires:
  - restricted-burnside-finiteness
  - free-burnside-is-a-limit-of-hyperbolic-groups
---

Notation as in the target. A finite group `Q` with generating tuple `s` whose
words of length `<= R` satisfy the law is exactly a finite quotient `F/L` of
`Π_R(m,N)`: the map `x_i -> s_i` kills every `h^N` with `|h| <= R`, hence `N_R`.

**Clause 1.** If `LRB(R, C)`, every finite-index normal subgroup of `Π_R` has
index `<= C`. A finitely generated group has only finitely many homomorphisms
to `Sym(C)`, so only finitely many normal subgroups of index `<= C`.
Conversely, if `Π_R` has finitely many finite-index normal subgroups, their
intersection `M` has finite index, every finite quotient factors through
`Π_R/M`, and `C = |Π_R/M|` works.

**Clause 2.** `N_R ⊆ N_{R'}`, so `Π_{R'}` is a quotient of `Π_R` and its finite
quotients are finite quotients of `Π_R`.

**Clause 3, forward.** Assume `LRB(R_0, C)`. For `R >= R_0` let `M_R` be the
intersection of all finite-index normal subgroups of `F` containing `N_R`.
- By clauses 1 and 2, `M_R` is an intersection of finitely many subgroups, so
  it has finite index in `F`.
- If `R <= R'`, every finite-index normal subgroup containing `N_{R'}` contains
  `N_R`, so `M_R ⊆ M_{R'}`.
- The subgroups of `F` containing `M_{R_0}` are finitely many, since `M_{R_0}`
  has finite index. So the chain stabilizes: there is `R*` with `M_R = M_{R*}`
  for all `R >= R*`.
- For any `h in F` take `R >= max(R*, |h|)`. Then `h^N in N_R ⊆ M_R = M_{R*}`.
  So `F/M_{R*}` has exponent dividing `N`.
- A finite quotient `F/L` of `Π_{R*}` has `L ⊇ M_{R*}`, so it is a quotient of
  `F/M_{R*}` and has exponent dividing `N`.
- `F/M_{R*}` is a finite `m`-generated group of exponent dividing `N`, so by
  clause 2 of `restricted-burnside-finiteness` it is a quotient of `R(m,N)`.
  `R(m,N)` is a finite quotient of `B(m,N)`, hence of `Π_{R*}`, hence of the
  largest finite quotient `F/M_{R*}`. Two finite groups that are quotients of
  each other are isomorphic.

**Clause 3, backward.** If every finite quotient of `Π_{R*}` has exponent
dividing `N`, each is a quotient of `R(m,N)`
(`restricted-burnside-finiteness`, clause 2), so `LRB(R*, |R(m,N)|)`.

**Clause 4.** Let `F^N = ∪_R N_R`, the normal closure of all `N`-th powers. If
`B(m,N) = F/F^N` is finite, `F^N` has finite index, so it is finitely generated
(Schreier). Each generator lies in some `N_R`, and the `N_R` increase, so
`N_{R*} = F^N` for some `R*`. Then `Π_{R*} = B(m,N)` is finite, and
`LRB(R*, |B(m,N)|)` holds.

**Clause 5.** Use items 1, 3 and 4 of `free-burnside-is-a-limit-of-hyperbolic-groups`:
the kernels `K_k = ker(F -> G_k)` increase with union `F^N`, and each `G_k` is
non-elementary hyperbolic, hence infinite.
- **Stages are partial Burnside quotients.** Fix `R`. The finite set
  `{h^N : |h| <= R}` lies in `F^N = ∪_k K_k`, so it lies in `K_{k_0}` for some
  `k_0 = k_0(R)`. For `k >= k_0`, `N_R ⊆ K_k`, so `G_k` is a quotient of `Π_R`.
- **Forward.** Assume `LRB(R, C)` and `k >= k_0(R)`. Every finite quotient of
  `G_k` is a finite quotient of `Π_R`, so it has order `<= C`. By clause 1 applied
  to `G_k`, the finite-index normal subgroups of `G_k` are finitely many. Their
  intersection `T` has finite index. If `G_k` were residually finite, `T = 1`
  and `G_k` would be finite, a contradiction.
- **Converse.** Suppose `LRB(R, C)` for some `R, C`. Take a residually finite
  `G_k` with `k >= k_0(R)`. It is infinite, so it has a finite quotient
  injective on a set of `C + 1` elements. That quotient satisfies the law on
  words of length `<= R`, contradicting `LRB(R, C)`. So `LRB(m,N)` fails. ∎

**Remark.** Attempt 5 of `hyperlinear-fg-bounded-exponent-groups-are-finite`
proved the forward direction for one stage. This route gives it for all large
`k`, with the converse and the exponent-`N` reformulation.
