---
rg: 2
id: thompson-v-torsion-centralizers-are-rationally-acyclic-proof
kind: route
title: Centralizer structure theorem, locally finite kernels and Szymik--Wahl give rational acyclicity of torsion centralizers
target: thompson-v-torsion-centralizers-are-rationally-acyclic
requires:
  - thompson-v-is-integrally-acyclic
---

**Literature import.** C. Bleak, H. Bowman, A. Gordon, G. Graham, J. Hughes,
F. Matucci, M. Sapir, "Centralizers in R. Thompson's group V_n", arXiv:1107.0672
(journal reference not re-checked). Read from the arXiv PDF on
2026-09-19. Verbatim, up to typesetting:

> "Theorem 1.1 Let n > 1 be a positive integer and suppose α ∈ V_n. Then,
> there are non-negative integers s, t, m_i, and r_i and groups K_{m_i},
> G_{n,r_i}, A_j, and P_t, for i ∈ {1,...,s} and j ∈ {1,...,t}, so that
> C_{V_n}(α) ≅ (∏_{i=1}^s K_{m_i} ⋊ G_{n,r_i}) × (∏_{j=1}^t ((A_j ⋊ Z) ≀ P_{q_j}))"

> "For each m_i, we have K_{m_i} = (Maps(C_n, Z_{m_i}))^{r_i}, where
> Maps(C_n, Z_{m_i}) is the group of continuous maps from C_n to Z_{m_i}
> under point-wise multiplication, and where Z_{m_i} is the cyclic group
> Z/(m_i Z) under the discrete topology."

> "The groups G_{n,r_i} are the Higman-Thompson groups from [14]."

> "The number t is the number of equivalence classes of components carrying
> infinite orbits under the action of ⟨α⟩."

The text also says `r_i` is "a minimal number of nodes carrying a fundamental
domain", so `r_i ≥ 1`. Here `V = V_2` and `C_2` is the Cantor set.

**Proof.** Let `g ∈ V` have finite order.

*Step 1: `t = 0`.* The group `⟨g⟩` is finite, so every orbit of `⟨g⟩` is
finite. No component carries an infinite orbit, so `t = 0` and

```text
C_V(g) ≅ ∏_{i=1}^s ( K_{m_i} ⋊ G_{2,r_i} ),    K_{m_i} = Maps(C_2, Z_{m_i})^{r_i}.
```

*Step 2: each `K_m` is locally finite.* A continuous map from the Cantor set
to a finite discrete group is locally constant. So it factors through the
partition of `C_2` into the `2^d` cylinders of some depth `d`. Hence
`Maps(C_2, Z_m)` is the increasing union over `d` of the finite groups
`(Z_m)^(2^d)`, and a finite power of it is again such a union. Group homology
commutes with directed unions, and a finite group has `H_q(F; Q) = 0` for
`q ≥ 1` (multiplication by `|F|` is zero on it and invertible on `Q`). So
`H_q(K_m; Q) = 0` for `q ≥ 1` and `H_0(K_m; Q) = Q`.

*Step 3: each factor is rationally acyclic.* The Lyndon--Hochschild--Serre
spectral sequence of `K ↪ K ⋊ G ↠ G` with `Q` coefficients is

```text
E^2_{p,q} = H_p(G; H_q(K; Q))  ⟹  H_{p+q}(K ⋊ G; Q).
```

By Step 2 the rows `q ≥ 1` vanish, and the row `q = 0` is
`H_p(G; Q)`, since `G` acts trivially on `H_0(K; Q) = Q`. So
`H_*(K ⋊ G; Q) ≅ H_*(G; Q)`. Here `G = G_{2,r}` with `r ≥ 1`, and by
`thompson-v-is-integrally-acyclic` (Szymik--Wahl: "For all r ≥ 1, the
Thompson group V ≅ V_{2,r} is integrally acyclic") `H_p(G; Z) = 0` for
`p ≥ 1`. By universal coefficients `H_p(G; Q) = 0` for `p ≥ 1`.

*Step 4: products.* Over the field `Q` the Künneth formula gives
`H_*(A × B; Q) ≅ H_*(A; Q) ⊗ H_*(B; Q)`. A finite product of rationally
acyclic groups is therefore rationally acyclic. (If `s = 0` the group is
trivial, which is also acyclic.)

*Step 5: cohomology.* Over a field, `H^k(C; Q) ≅ Hom_Q(H_k(C; Q), Q)`, which
is `0` for `k ≥ 1`. QED.
