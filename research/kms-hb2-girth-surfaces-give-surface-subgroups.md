---
rg: 2
id: kms-hb2-girth-surfaces-give-surface-subgroups
kind: claim
title: For every odd prime p, a labelled girth surface for the KMS group G_HB2(p) gives a quasiconvex closed surface subgroup
distinct_from:
  ghb7-girth-surfaces-give-surface-subgroups: that is the criterion for p = 7 only, with the vertex group intersections computed in SL_4(F_7); this is the criterion for every odd prime, with vertex groups, intersections and link girths proved from symbolic normal forms
  one-ended-hyperbolic-groups-contain-surface-subgroups: that is Gromov's question for every one-ended hyperbolic group; this is a finite combinatorial sufficient condition inside one infinite family of KMS groups
  cckw-kms-triangle-groups-structure: that imports the structure theorem for triangles of groups and the KMS presentations; this derives from it a local-to-global criterion producing surface subgroups
artifacts:
  - research/artifacts/hl-surface-subgroups-2026-09-14.md
  - experiments/kms-hb2-surface-subgroups/verify_integer_certificate.py
  - experiments/kms-hb2-surface-subgroups/girth_bounds.py
---

**ESTABLISHED.** Let `p` be an odd prime and `G = G_{HB_2^{(2)}}(p)`:

```text
<a,b,c | a^p, b^p, c^p, [a,b,a], [a,b,b], [c,b,c], [c,b,b,c], [c,b,b,b], [c,a,c], [c,a,a,c], [c,a,a,a]>
```

with `[x,y] = x^{-1}y^{-1}xy` and left-normed iterated commutators (item 2 of
`cckw-kms-triangle-groups-structure`).

**Notation.**
- `g_0 = c`, `g_1 = a`, `g_2 = b`.
- `X_0 = <a,b>`, `X_1 = <c,b>`, `X_2 = <c,a>`, subgroups of `G`.
- `m_0 = 3` and `m_1 = m_2 = 4`.
- For a type `i ∈ {0,1,2}`, let `j < k` be the other two types.

**Girth surface.** A girth surface of size `T` for `G` consists of the following data.
- Fixed-point-free involutions `r_0, r_1, r_2` of `{0, …, T−1}` that generate a transitive group.
  For each `i`, every orbit of `<r_j, r_k>` has exactly `2m_i` points.
- An integer exponent `x(t,k)` not divisible by `p` for every `t` and `k`, with
  `x(r_k t, k) ≡ −x(t,k) (mod p)`.
- The vertex condition. Fix `t` and `i`. Put `t_0 = t` and `t_{q+1} = r_{k_q} t_q`, where
  `k_q = j` for even `q` and `k_q = k` for odd `q`. Then

  ```text
  g_{k_0}^{x(t_0,k_0)} g_{k_1}^{x(t_1,k_1)} ⋯ g_{k_{2m_i−1}}^{x(t_{2m_i−1}, k_{2m_i−1})} = 1   in G.
  ```

**Claim.** Take `T` copies `Δ_t` of the hyperbolic triangle with angles `π/3, π/4, π/4` at corners
`v_0, v_1, v_2`, and call the side opposite `v_k` its side `e_k`. Glue side `e_k` of `Δ_t` to side
`e_k` of `Δ_{r_k t}` by the identity of `e_k`, and call the result `S`.
1. `S` is a closed hyperbolic surface with `χ(S) = −T/12`.
2. There is an injective homomorphism `φ : π_1(S) → G` whose image is quasiconvex.
3. So `G` contains the fundamental group of a closed orientable surface of genus `1 + T/12`. When
   `S` is orientable, it contains one of genus `1 + T/24`.

Proof: `kms-hb2-girth-surfaces-give-surface-subgroups-proof`.

Instances: `kms-hb2-groups-contain-genus-two-surface-subgroups`.
