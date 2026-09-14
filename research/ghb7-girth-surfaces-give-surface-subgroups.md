---
rg: 2
id: ghb7-girth-surfaces-give-surface-subgroups
kind: claim
title: A labelled girth surface for GHB_2(7) gives a quasiconvex closed surface subgroup
distinct_from:
  one-ended-hyperbolic-groups-contain-surface-subgroups: that is Gromov's question for every one-ended hyperbolic group; this is a finite combinatorial sufficient condition for the single group GHB_2(7)
  cckw-ghb2-kms-group-structure: that imports the triangle of groups and the complex Y; this derives from it a local-to-global criterion that produces surface subgroups
artifacts:
  - research/artifacts/ideas-growth-hyperbolic-2026-09-14.md
---

**ESTABLISHED.** Let `G = G_{HB_2}(7)` with generators `a, b, c` as in `cckw-ghb2-kms-group-structure`.

**Notation.**
- `g_0 = c`, `g_1 = a`, `g_2 = b`.
- `X_0 = <a,b>`, `X_1 = <c,b>`, `X_2 = <c,a>`.
- `m_0 = 3` and `m_1 = m_2 = 4`.
- For a type `i ∈ {0,1,2}`, let `j < k` be the other two types.

**Girth surface.** A girth surface of size `T` consists of the following data.
- Fixed-point-free involutions `r_0, r_1, r_2` of `{0, …, T−1}` that generate a transitive group.
  For each `i`, every orbit of `<r_j, r_k>` must have exactly `2m_i` points.
- An exponent `x(t,k) ∈ {1, …, 6}` for every `t` and `k`, with `x(r_k t, k) ≡ −x(t,k) (mod 7)`.
- The vertex condition. Fix `t` and `i`. Put `t_0 = t` and `t_{p+1} = r_{k_p} t_p`, where
  `k_p = j` for even `p` and `k_p = k` for odd `p`. Then

  ```text
  g_{k_0}^{x(t_0,k_0)} g_{k_1}^{x(t_1,k_1)} ⋯ g_{k_{2m_i−1}}^{x(t_{2m_i−1}, k_{2m_i−1})} = 1   in G.
  ```

Each such word lies in `X_i`. So by item 5 of `cckw-ghb2-kms-group-structure`, the condition may
be checked in `SL_4(F_7)` through `ψ`.

**Claim.** Take `T` copies `Δ_t` of the hyperbolic triangle with angles `π/3, π/4, π/4` at corners
`v_0, v_1, v_2`, and call the side opposite `v_k` its side `e_k`. Glue side `e_k` of `Δ_t` to side
`e_k` of `Δ_{r_k t}` by the identity of `e_k`, and call the result `S`.
1. `S` is a closed hyperbolic surface with `χ(S) = −T/12`.
2. There is an injective homomorphism `φ : π_1(S) → G` whose image is quasiconvex.
3. So `G` contains the fundamental group of a closed orientable surface of genus `1 + T/12`. When
   `S` is orientable, it contains one of genus `1 + T/24`.

Proof: `ghb7-girth-surfaces-give-surface-subgroups-proof`.

## Sources

- CCKW Theorem 3.1(i),(v), read in the MSI text extract used by
  `cckw-ghb2-kms-group-structure-citation`.
- Bridson–Haefliger, *Metric Spaces of Non-Positive Curvature* (1999), read at source:
  Definition I.5.6, Definitions I.7.37–7.38, Theorem I.7.39, Theorem I.7.50, Proposition I.8.19,
  Proposition II.1.4(1),(2), and Theorems III.H.1.7 and III.H.1.9.

Instances: `ghb7-contains-a-genus-two-surface-subgroup`.
