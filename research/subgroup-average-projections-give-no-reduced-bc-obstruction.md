---
rg: 2
id: subgroup-average-projections-give-no-reduced-bc-obstruction
kind: claim
title: Subgroup averaging projections and compression relations give no obstruction to reduced Baum--Connes
invalidates:
  - bc-counterexample-via-kazhdan-projection
  - bc-counterexample-via-leavitt-compression-classes
distinct_from:
  kazhdan-projections-vanish-in-regular-group-algebra: that says the Kazhdan projection of an infinite subgroup is zero in the group von Neumann algebra and is not a group-ring element; this consumes it for K-theory, adds the finite-subgroup and finite-trace parts, and concludes that none of these projections reaches outside the reduced assembly image.
  kazhdan-projection-is-norm-limit-of-finite-averages: that approximates the Kazhdan projection by probability averages in the maximal group algebra; this is about where its class goes under the regular representation and the assembly map.
---

**ESTABLISHED.** Let `G` be a countable discrete group. Write
`lambda : C*_max G -> C*_r G` for the regular quotient and `mu_r` for the
reduced assembly map.

1. **Infinite Kazhdan subgroups.** Let `Lambda <= G` be infinite with property
   (T), with Kazhdan projection `p_Lambda` in
   `C*_max(Lambda) <= C*_max(G)`. Then `lambda(p_Lambda) = 0`, so
   `[p_Lambda]` lies in `ker(lambda_* : K_0(C*_max G) -> K_0(C*_r G))`.
2. **Finite subgroups.** Let `H <= G` be finite and
   `p_H = |H|^-1 sum_(h in H) u_h`. Then `[p_H]` is `mu_r` of the orbit `G/H`
   carrying the trivial `H`-representation, so it lies in the image of `mu_r`.
   So do its conjugates `u_g p_H u_g^* = p_(gHg^-1)`.
3. **Compression relations.** `C*_r G` has the faithful tracial state
   `tau(x) = <x delta_e, delta_e>`, so every `M_n(C*_r G)` is finite: if
   `v^*v = p` and `v v^* <= p`, then `v v^* = p`.
   - A strict compression `t Gamma t^-1 < Gamma` gives
     `p_Gamma <= u_t p_Gamma u_t^*` in `C*_max G`.
   - For infinite Kazhdan `Gamma`, both sides vanish in `C*_r G` by part 1.
   - A finite `Gamma` admits no strict compression.

Consequently no class of `K_0(C*_r G)` outside the image of `mu_r` is
represented by a subgroup averaging projection, a conjugate of one, or a
compression relation between them. In particular this covers `L^x` and the
Kun--Thom Theorem E groups.

**Remark: maximal assembly.** Let `G` be an infinite Kazhdan group whose
`mu_r` is rationally injective. Then `[p_G]` is not in the image of the
maximal assembly map `mu_max`:
- if `[p_G] = mu_max(x)`, then `mu_r(x) = lambda_*[p_G] = 0`, so `x` is torsion;
- hence `[p_G]` is torsion;
- but the trivial representation sends `[p_G]` to `1`, a non-torsion integer.

Kazhdan projections therefore test only the maximal version, which is why the
conjecture is stated with `C*_r`.
