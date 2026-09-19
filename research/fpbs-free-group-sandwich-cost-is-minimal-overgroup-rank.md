---
rg: 2
id: fpbs-free-group-sandwich-cost-is-minimal-overgroup-rank
kind: claim
title: In every free action of a finitely generated free group, the cheapest relation sandwiched over a finitely generated subgroup H costs exactly the least rank of a subgroup containing H, so the free-group slice of the relative Bernoulli sandwich bound holds
distinct_from:
  fpbs-sandwich-cost-fox-rank-lower-bound: that proves the lower bound C(E) >= rk(A) for every sandwich and evaluates rk(A) only for compressed H; this evaluates rk(A) for every finitely generated H as the least overgroup rank and shows the bound is attained, so the sandwich cost is computed for all H.
  fpbs-free-group-sandwich-cost-is-two: that is the rank-2 case F = F_2 with non-cyclic K, value 2; this is every finite rank and every finitely generated H, including H that are not compressed and whose value is below rk H.
  fpbs-relative-sandwich-cost-bernoulli-lower-bound: that asks for the Bernoulli lower bound for all finitely generated groups; this proves it, with an exact value, when the ambient group is free of finite rank.
---

**ESTABLISHED** through
`fpbs-free-group-sandwich-cost-is-minimal-overgroup-rank-proof`.

Let `F` be a free group of finite rank `q` and `a` a free p.m.p. action of
`F` on `(X, μ)`. Let `S ⊆ F` be finite and `H = ⟨S⟩`. Put

```text
π̄(H ≤ F) = min { rk L : H ≤ L ≤ F },
p^F_S(a) = inf { C(E) : E_{a|H} ⊆ E ⊆ E_a }.
```

Then

```text
p^F_S(a) = π̄(H ≤ F).
```

The infimum is attained by `E = E_{a|L}` for every `L` of rank `π̄(H ≤ F)`
containing `H`, for example the `L²`-closure of `H`. Also, if `S` is
`h_1, …, h_p` and `A = (∂h_j/∂f_k)` is its Fox matrix over a basis of `F`,
then `rk_{N(F)}(A) = π̄(H ≤ F)`. So the Fox rank bound of
`fpbs-sandwich-cost-fox-rank-lower-bound` is sharp for every finitely
generated subgroup.

**Consequences.**
- **Free-group slice of RSB.** The value does not depend on the free action.
  So `fpbs-relative-sandwich-cost-bernoulli-lower-bound` holds for every
  ambient group `Δ = F_q`, every finite `F ⊆ Δ` and every free action. The
  Bernoulli shift is one free action, which gives
  `p^Δ_F(s_Δ) = p^Δ_F(a)`.
- **Subgroup attainment.** In free groups, every measurable sandwich is at
  least as expensive as the cheapest subgroup sandwich `E_{a|L}`. This is
  `fpbs-sandwich-cost-attained-by-subgroup-relations` for ambient free
  groups of finite rank.
- **Measured Hanna Neumann form.** A relation squeezed between `E_{a|H}` and
  `E_a` cannot be cheaper than every subgroup between `H` and `F`. This
  holds even though such a relation need not come from any subgroup, or from
  any finite cover.

**Example.** Let `F = ⟨x, y⟩` and `H = ⟨x², y², xy⟩`. `H` has rank 3 and
index 2. It is contained only in `H` and `F`, so `π̄ = 2`. Every sandwich over
`H` costs at least 2, and `E_a` costs exactly 2.
