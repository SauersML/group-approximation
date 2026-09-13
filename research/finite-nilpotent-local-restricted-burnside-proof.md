---
rg: 2
id: finite-nilpotent-local-restricted-burnside-proof
kind: route
title: A Frattini argument inside the kernel of F_m onto R(m,p^a), then Sylow decomposition
target: finite-nilpotent-groups-satisfy-local-restricted-burnside
requires:
  - restricted-burnside-finiteness
  - local-restricted-burnside-iff-partial-burnside-finite-quotients
---

Let `F = F_m`. For an integer `e >= 1` and `R >= 1`, let `N^(e)_R` be the normal
closure of `{h^e : 1 <= |h| <= R}`, and `F^(e) = ∪_R N^(e)_R` the normal closure
of all `e`-th powers.

**Step 0: one prime.** Let `p` divide `N` and `q = p^a` be the exact power of
`p` dividing `N`.
- `T_p = ker(F -> R(m,q))` has finite index (`restricted-burnside-finiteness`),
  and `F/T_p` has exponent dividing `q`, so it is a `p`-group.
- `T_p` is free of finite rank (Schreier). Put `Φ_p = T_p^p [T_p, T_p]`. It is
  characteristic in `T_p`, hence normal in `F`, and `T_p/Φ_p` is a finite
  elementary abelian `p`-group. So `F/Φ_p` is a finite `p`-group.

**Step 1: `F^(q) Φ_p = T_p`.**
- `F^(q) ⊆ T_p`, since `R(m,q)` has exponent dividing `q`, and `Φ_p ⊆ T_p`.
- `F / F^(q)Φ_p` is a quotient of the finite group `F/Φ_p` and has exponent
  dividing `q`. By clause 2 of `restricted-burnside-finiteness`, the map onto it
  kills `T_p`. So `T_p ⊆ F^(q)Φ_p`.

**Step 2: a finite radius suffices.** The subgroups `N^(q)_R Φ_p / Φ_p` of the
finite group `T_p/Φ_p` increase with `R`. Their union is `F^(q)Φ_p/Φ_p = T_p/Φ_p`.
So there is `R_p` with `N^(q)_{R_p} Φ_p = T_p`.

**Step 3: Frattini.** Let `P = F/L` be a finite `p`-group with `N^(q)_{R_p} ⊆ L`.
Put `T̄ = T_p L / L`, a normal subgroup of `P`.
- By Step 2, `T̄ = N^(q)_{R_p} Φ_p L / L = Φ_p L / L`.
- The image of `Φ_p = T_p^p [T_p, T_p]` in `P` is `T̄^p [T̄, T̄]`. For the finite
  `p`-group `T̄`, that is its Frattini subgroup `Φ(T̄)` (Burnside basis theorem).
- So `T̄ = Φ(T̄)`. A nontrivial finite group has a maximal subgroup, so
  `Φ(T̄) != T̄` unless `T̄ = 1`. Hence `T̄ = 1` and `L ⊇ T_p`.
- So `P` is a quotient of `R(m,q)` and has exponent dividing `q`.

**Step 4: nilpotent groups (clause 1).** Put `R_nil = max(1, max_{p | N} R_p)`.
Let `Q`, `s` be as in clause 1, and write `Q = ∏_ℓ Q_ℓ` (Sylow subgroups, each a
quotient of `Q` through which the images of `s` generate `Q_ℓ` and satisfy the
same law).
- **`ℓ` not dividing `N`.** The image of `s_i` has `ℓ`-power order dividing `N`,
  so it is trivial, and `Q_ℓ = 1`.
- **`ℓ = p` dividing `N`.** Every `w` with `|w| <= R_nil` has image of `p`-power
  order dividing `N`, hence dividing `q`. So the kernel `L_p` of `F -> Q_p`
  contains `N^(q)_{R_nil} ⊇ N^(q)_{R_p}`. By Step 3, `Q_p` has exponent dividing `q`.
- So the exponent of `Q` divides `∏_{p | N} q_p = N`. By clause 2 of
  `restricted-burnside-finiteness`, `Q` is a quotient of `R(m,N)`.

**Step 5: Coulon stages (clause 2).** By clause 5 of
`local-restricted-burnside-iff-partial-burnside-finite-quotients` (first bullet
of its route), there is `k_0` such that `G_k` is a quotient of `Π_{R_nil}(m,N)`
for all `k >= k_0`.
- A finite nilpotent quotient of such a `G_k` satisfies the law on words of
  length `<= R_nil`, so by Step 4 it has exponent dividing `N`.
- The pro-p completion of `G_k` is the inverse limit of its finite `p`-group
  quotients. Each is a quotient of `R(m,q)` (trivial if `p` does not divide `N`),
  so their orders are bounded, and the inverse limit is finite.

**Clause 3** restates clauses 1 and 2: a finite `p`-group satisfying the law on
words of length `R >= R_nil` is a quotient of `R(m,q)`, so its order is bounded. ∎
