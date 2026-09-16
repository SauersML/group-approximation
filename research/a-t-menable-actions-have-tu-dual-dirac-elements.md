---
rg: 2
id: a-t-menable-actions-have-tu-dual-dirac-elements
kind: claim
title: An a-T-menable action of a countable group on a locally compact space has a Tu dual-Dirac inverse through a proper algebra
distinct_from:
  monster-bc-detector-lives-on-a-proper-orbit-ideal: that imports Finn-Sell's a-T-menability of the monster boundary groupoid and names Tu 1999 only as a reference; this imports the dual-Dirac statement for a-T-menable actions itself, in the form Baum--Guentner--Willett use.
  bernoulli-shift-weak-k-equivalence-and-going-down: that imports going-down and Baum--Connes for proper coefficients; this imports the Dirac--dual-Dirac factorization that reduces an a-T-menable coefficient to a proper one.
---

**ESTABLISHED (citation)** by `a-t-menable-actions-have-tu-dual-dirac-elements-citation`.

**Setting.** `G` is a countable discrete group acting on a second countable locally compact space `X`. Following
Baum--Guentner--Willett (BGW), Definition 6.1, the action, written on the right, is **a-T-menable** if there is a
continuous `h : X × G -> R` such that:
1. `h(x, e) = 0`;
2. `h(x, g) = h(xg, g^(-1))`;
3. `Σ_(i,j) t_i t_j h(x g_i, g_i^(-1) g_j) <= 0` for all `x`, all `g_1, ..., g_n` and real `t_i` with `Σ t_i = 0`;
4. for every compact `K ⊆ X`, `h` restricted to `{(x, g) : x ∈ K, xg ∈ K}` is proper.

**Statement.** If the action is a-T-menable, there are:
- a proper `X ⋊ G`-algebra `A`: there are a locally compact proper `G`-space `Y`, an equivariant *-homomorphism
  `C_0(Y) -> ZM(A)` and an equivariant, open, continuous map `Y -> X`;
- elements `α ∈ KK^G(A, C_0(X))` and `β ∈ KK^G(C_0(X), A)` with `β ⊗_A α = 1` in `KK^G(C_0(X), C_0(X))`.

For such a proper `A`, all crossed products `A ⋊_τ G` agree, and the assembly map at `A` is an isomorphism.

**Scope.**
- BGW state (6.1) in equivariant E-theory and add that Tu works in equivariant KK-theory. The KK form above rests on that
  parenthetical remark.
- Tu's paper itself was not fetched, so its theorem numbers are as cited by BGW and unverified at the source.
- The consumer `cnd-support-shift-bc-and-k-amenability-proof` needs the KK form, for reduced descent over non-exact
  groups.
