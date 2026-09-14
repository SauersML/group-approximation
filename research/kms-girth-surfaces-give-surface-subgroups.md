---
rg: 2
id: kms-girth-surfaces-give-surface-subgroups
kind: claim
title: For every hyperbolic rank-three KMS group over an odd prime, a labelled girth surface gives a quasiconvex closed surface subgroup
distinct_from:
  kms-hb2-girth-surfaces-give-surface-subgroups: that is the criterion for the family G_HB2(p), with intersections proved through a quotient to SL_4(F_p); this covers all six hyperbolic KMS families, with intersections derived by counting chambers and edges at a vertex
  ghb7-girth-surfaces-give-surface-subgroups: that is the criterion for the single group G_HB2(7); this covers every hyperbolic KMS group over every odd prime
  one-ended-hyperbolic-groups-contain-surface-subgroups: that is Gromov's question for every one-ended hyperbolic group; this is a finite combinatorial sufficient condition inside the hyperbolic KMS groups
artifacts:
  - research/artifacts/hl-surface-subgroups-2026-09-14.md
---

**ESTABLISHED.** Let `p` be an odd prime, and let `G` be one of the six hyperbolic KMS groups over `F_p` of
`cckw-kms-triangle-groups-structure` item 2. Write:
- `g_0 = c`, `g_1 = a`, `g_2 = b`;
- `X_0 = <a,b>`, `X_1 = <b,c>`, `X_2 = <a,c>`, so the vertex of type `i` does not contain `g_i`.

Each `X_i` carries the relators `x^p, y^p` for its two generators, together with either
- `U_3`: `[x,y,x], [x,y,y]`, with `m_i = 3`; or
- `U_4`: `[x,y,x], [x,y,y,x], [x,y,y,y]`, with `m_i = 4`, for a designated generator `x`.

| family | `(m_0,m_1,m_2)` | `X_0` | `X_1` | `X_2` |
|---|---|---|---|---|
| `G_HC2(1)` | `(3,3,4)` | `U_3` | `U_3` | `U_4`, `x = a` |
| `G_HB2(2)` | `(3,4,4)` | `U_3` | `U_4`, `x = c` | `U_4`, `x = c` |
| `G_HC2(2)` | `(3,4,4)` | `U_3` | `U_4`, `x = b` | `U_4`, `x = a` |
| `G_HBC2(2)` | `(3,4,4)` | `U_3` | `U_4`, `x = b` | `U_4`, `x = c` |
| `G_HB2(3)` | `(4,4,4)` | `U_4`, `x = a` | `U_4`, `x = b` | `U_4`, `x = a` |
| `G_HBC2(3)` | `(4,4,4)` | `U_4`, `x = a` | `U_4`, `x = b` | `U_4`, `x = c` |

**Girth surface.** A girth surface of size `T` for `G` consists of the following data. For a type `i`, let
`j < k` be the other two types.
- Fixed-point-free involutions `r_0, r_1, r_2` of `{0, …, T−1}` that generate a transitive group, such that
  every orbit of `<r_j, r_k>` has exactly `2m_i` points.
- An integer `x(t,k)` not divisible by `p` for every `t` and `k`, with `x(r_k t, k) ≡ −x(t,k) (mod p)`.
- The vertex condition. Put `t_0 = t` and `t_{q+1} = r_{k_q} t_q`, where `k_q = j` for even `q` and `k_q = k`
  for odd `q`. Then

  ```text
  g_{k_0}^{x(t_0,k_0)} ⋯ g_{k_{2m_i−1}}^{x(t_{2m_i−1}, k_{2m_i−1})} = 1   in G,   for every t and i.
  ```

**Claim.** Take `T` copies of the hyperbolic triangle with angles `π/m_0, π/m_1, π/m_2`, and glue side `e_k` of
copy `t` to side `e_k` of copy `r_k t` by the identity. Call the result `S`.
1. `S` is a closed hyperbolic surface with `χ(S) = T (1/(2m_0) + 1/(2m_1) + 1/(2m_2) − 1/2)`.
2. There is an injective homomorphism `π_1(S) → G` with quasiconvex image.

Proof: `kms-girth-surfaces-give-surface-subgroups-proof`.

The commutator words of the families other than `G_HB2(2)` were read from the CCKW text extraction (see
`cckw-kms-triangle-groups-structure-citation`). The claim is stated for the groups those presentations
define.

Instances: `kms-hb2-groups-contain-genus-two-surface-subgroups`,
`kms-hc2-hb3-hbc3-contain-genus-two-surface-subgroups`.
