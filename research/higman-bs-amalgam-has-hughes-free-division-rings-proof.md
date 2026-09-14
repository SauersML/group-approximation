---
rg: 2
id: higman-bs-amalgam-has-hughes-free-division-rings-proof
kind: route
title: Split off BS(1,2) with a locally free kernel, give the kernel its Hughes-free ring, and pass to the elementary amenable extension
target: higman-bs-amalgam-has-hughes-free-division-rings
requires:
  - fsp-graph-of-rings-and-linnell-extension-imports
  - hughes-free-division-rings-pass-to-directed-unions
artifacts:
  - research/artifacts/gk3-nonrf-hosts-2026-09-14.md
---

## Proof

Write `V_1 = <a,b>` and `V_2 = <b,c>`, both copies of `BS(1,2)`, and `E = <b> ≅ Z`, so `G_1 = V_1 *_E V_2`, the
normal form theorem for amalgams embedding `V_1`, `V_2` and `E`.

**Step 1: the split extension.** Sending `a -> a`, `b -> b`, `c -> 1` respects both relations (the second becomes
`1 = 1`). So it defines a retraction `rho : G_1 -> V_1` that is the identity on `V_1`. Hence `G_1 = K ⋊ V_1`
with `K = ker rho`.

**Step 2: `K` is locally free.** `K` acts on the Bass--Serre tree of `V_1 *_E V_2`, and stabilizers are
intersections of `K` with conjugates of `V_1`, `V_2`, `E`. Since `K` is normal, `K ∩ gXg^(-1) = g(K ∩ X)g^(-1)`.
* `K ∩ V_1 = 1` and `K ∩ E = 1`, because `rho` is injective on `V_1`.
* `K ∩ V_2` is the kernel of `rho` on `V_2 = <b, c | c^b = c^2>`, which is `c -> 1, b -> b`. It is the normal
  closure of `c` in `V_2`, the dyadic group `Z[1/2]`.

So `K` acts on a tree with trivial edge stabilizers and vertex stabilizers trivial or conjugate to subgroups of
`Z[1/2]`. Let `L <= K` be finitely generated. By Bass--Serre theory, `L` is the free product of a free group and
of vertex stabilizers `L_v` of orbit representatives. Free factors of a finitely generated group are finitely
generated retracts, so only finitely many `L_v` are nontrivial and each is a finitely generated subgroup of
`Z[1/2]`, hence cyclic. So `L` is free.

**Step 3: `G_1` is locally indicable.** Let `L <= G_1` be finitely generated and nontrivial. If `rho(L) != 1`,
then `rho(L)` is a nontrivial finitely generated subgroup of `BS(1,2) = Z[1/2] ⋊ Z`. Either it lies in `Z[1/2]`
and is infinite cyclic, or it maps nontrivially to `Z`; either way `L` maps onto `Z`. If `rho(L) = 1`, then
`L <= K` is a nontrivial free group and maps onto `Z`.

**Step 4: `D_(kK)` exists.** `K` is locally free, so it has a Hughes-free division ring over every division ring
`k` ([[hughes-free-division-rings-pass-to-directed-unions]], "Locally free groups").

**Step 5: `D_(kK) * [V_1]` is a domain.** By item 4 of [[fsp-graph-of-rings-and-linnell-extension-imports]] the
crossed product exists. Write `D = D_(kK)` and `V_1 = N ⋊ <a>`, where `N = Z[1/2]` is the normal closure of `b`.
* `N` is the directed union of the infinite cyclic groups `N_m = <a^m b a^(-m)>`, because
  `b = (a^m b a^(-m))^(2^m)`.
* Each `D * N_m` is a crossed product of a division ring with `Z`, a twisted Laurent polynomial ring
  `D[s, s^(-1); alpha]`, which is a domain by comparing leading terms.
* So `D * N = ∪_m D * N_m` is a domain, and `D * V_1 = (D * N) * [<a>]` is a twisted Laurent polynomial ring over
  a domain with an invertible stable letter, again a domain by leading terms.

**Step 6: the Hughes-free ring of `G_1`.** `G_1` is torsion-free (Step 3), `K ⊴ G_1` is locally indicable,
`G_1/K ≅ BS(1,2)` is solvable, hence elementary amenable, `D_(kK)` exists (Step 4), and `D_(kK) * [G_1/K]` is a
domain (Step 5).
* By item 5 of the imports, `k[G_1] -> Ore(D_(kK) * [G_1/K])` is a Linnell embedding.
* Since `G_1` is locally indicable (Step 3), item 3 makes it Hughes-free.

So `D_(k G_1)` exists for every division ring `k`.

**Relabelling.** The map `a -> c, b -> d, c -> a` carries `G_1` isomorphically onto `G_2`, and cyclic relabellings
give `G_3`, `G_4` ([[higman-group-splits-as-amalgams-over-free-subgroups]]). QED

**Checks.**
* Steps 1–3 and 5 are elementary.
* Step 2 uses only the Bass--Serre structure theorem for actions with trivial edge stabilizers and the Kurosh
  property that free factors are retracts.
* No step uses a characteristic.
* The characteristic-zero input of the source (Strong Atiyah for locally indicable groups) is replaced by Steps 4
  and 6.
* Not independently re-derived by a second lane.
