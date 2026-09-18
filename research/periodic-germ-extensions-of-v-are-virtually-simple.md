---
rg: 2
id: periodic-germ-extensions-of-v-are-virtually-simple
kind: claim
title: Thompson's V extended by period-shift and family-permutation germs at finitely many periodic tail classes is of type F_infinity with a simple commutator subgroup of finite index, and it embeds in that commutator subgroup
distinct_from:
  germ-complex-and-bux-gonzalez-morse-inputs: that imports the Belk--Hyde--Matucci germ complex and the finite-index case of their finiteness theorem; this uses the normal case of their theorem for a new family of germ groups, Z wr S_l at periodic points.
  normal-germ-extensions-of-thompson-v-contain-no-sl3z: that is an obstruction for every germ extension of V in which V's germs are normal; this is a positive construction inside that class.
  rover-nekrashevych-finite-presentation-criteria: that concerns groups V_d(H) with a self-similar H; this group has no self-similar input, and its germs act on the side cones of a periodic point.
---

**ESTABLISHED** by `periodic-germ-extensions-of-v-are-virtually-simple-proof` (lane proof). *Reviewed:* gq-referee-a PASS (`research/artifacts/gq-referee-a-periodic-germ-extensions-of-v-and-breakpoint-consumers.md`, 135cfebbf), nits N1–N3 applied. The theorems of Belk--Hyde--Matucci it uses were read at source
(arXiv:2407.03149v1, `main.tex`). The construction is new as far as this lane knows. The priority
search was bounded (arXiv search on "piecewise projective" and "simple"), so no priority is claimed.

## Setting

- `C = {0,1}^N`, and `V` acts on it by prefix replacement.
- `Π` is a finite set of primitive words, each of length `ℓ_v >= 2`, one chosen in each rotation
  class.
- `Ω_Π` is the set of eventually periodic points with period in `Π`. Each such point is `u v^∞` with
  `v ∈ Π`, and `u` is unique up to `u ↔ uv`.
- **Side cones.** For `p = u v^∞` the side cones are `D_{k,j}(p) = C_{u v^k v_1⋯v_{j-1} v̄_j}` for
  `k >= 0` and `1 <= j <= ℓ_v`, where `v̄_j` is the other letter. The cone `C_{uv^K}` is
  `{p} ⊔ ⨆_{k>=K, j} D_{k,j}(p)`.
- **Admissible germs.** A germ at `p` to `q = u' v^∞` (same `v`) is *admissible* if, for some `K`,
  some `m ∈ Z^{ℓ_v}` and some `π ∈ S_{ℓ_v}`, it maps each `D_{k,j}(p)` with `k >= K` onto
  `D_{k+m_j, π(j)}(q)` by prefix replacement.
- **The group.** `G_Π` is the set of homeomorphisms `g` of `C` such that:
  - `g` agrees with a prefix replacement near every point outside a finite set `P_g ⊂ Ω_Π`;
  - for each `p ∈ P_g`, the point `g(p)` is tail equivalent to `p` and the germ of `g` at `p` is
    admissible.

## Statement

1. `G_Π` is a group. It is a finite germ extension of `V` with `sing(G_Π) = Ω_Π`, and it has the
   same orbits as `V`, namely the tail classes.
2. At `p ∈ Ω_Π` with period `v`, the group of germs is `(G_Π)_p ≅ Z^{ℓ_v} ⋊ S_{ℓ_v} = Z ≀ S_{ℓ_v}`.
   The subgroup `(V)_p` is the central diagonal `Z`.
3. `G_Π` has type `F_∞`.
4. The commutator subgroup `G_Π'` is simple, and every proper quotient of `G_Π` is abelian.
5. `G_Π / G_Π' ≅ ⊕_{v ∈ Π} (Z/ℓ_v ⊕ Z/2)`, which is finite. So `G_Π'` has finite index, is of type
   `F_∞`, and in particular is **finitely presented and simple**.
6. Let `E = lcm_{v∈Π} lcm(ℓ_v, 2)`, and let `c_1, …, c_E` be disjoint cones. Then
   `Δ(g) = ∏_i g^{(c_i)}`, the product of the copies of `g` transplanted into the cones `c_i`, is an
   injective homomorphism `G_Π → G_Π'`.
7. **So every subgroup of `G_Π` embeds in the finitely presented simple group `G_Π'`, and satisfies
   the Boone--Higman conjecture.**

**Why the permutations matter.** With shifts alone, the germ group would be `Z^{ℓ}`, `A_p` would be
`Z^{ℓ}/diag`, and the abelianization would be infinite. That is the situation of the
Belk--Hyde--Matucci example of piecewise linear circle maps with breakpoints at non-dyadic
rationals, where `G/G'` is free abelian. Permuting the families forces the germ coinvariants down to
`Z`, and then the diagonal `(V)_p` has finite index `ℓ`.

**Consumers.** `quadratic-breakpoint-psl2z-groups-satisfy-boone-higman` and
`rational-breakpoint-dyadic-pl-groups-satisfy-boone-higman`.
