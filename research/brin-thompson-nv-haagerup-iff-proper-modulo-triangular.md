---
rg: 2
id: brin-thompson-nv-haagerup-iff-proper-modulo-triangular
kind: claim
title: "For n >= 2, nV has the Haagerup property iff some cnd function is proper modulo the triangular subgroup T_n, iff some cnd function is proper modulo V^n; the fibre half R2 is implied by R1"
distinct_from:
  haagerup-splits-as-coset-plus-subgroup-properness: that splits Haagerup into a transversal and a fibre half for any subgroup; this shows that for H = T_n in nV the fibre half is redundant
  brin-thompson-nv-haagerup-iff-cocycle-and-kernel-domination: that splits along the kernel K of the exponent cocycle, whose finite automorphic intersections are infinite (they contain small-support kernel elements), so all three prerequisites are kept; this splits along T_n and keeps one
  brin-thompson-nv-cnd-proper-modulo-triangular-subgroup: that is the open transversal statement R1; this proves R1 is equivalent to the whole goal
---

**ESTABLISHED** by `brin-thompson-nv-haagerup-iff-proper-modulo-triangular-proof`.

**Statement.** Let `n ≥ 2`. The following are equivalent.

1. `nV` has the Haagerup property (`brin-thompson-groups-nv-are-a-t-menable` for this `n`).
2. Some cnd function on `nV` is proper modulo `T_n` (R1,
   `brin-thompson-nv-cnd-proper-modulo-triangular-subgroup`).
3. Some cnd function on `nV` is proper modulo `V^n`.
4. Some cnd function on `nV` is proper modulo `α(T_n)` or `α(V^n)` for one automorphism `α`
   (for example a conjugate or a coordinate permutation).

Moreover, from `ψ` as in (2) an explicit proper cnd function is
`Σ_{t,σ} ψ ∘ α_σ^{-1} ∘ Ad(t)` over the permutations `σ` and the finitely many shears `t` (and `t = 1`)
of `brin-thompson-nv-product-subgroup-has-finite-shear-core`.

**Consequences.**
- *R2 is redundant.* (2) ⇒ (1) ⇒ `brin-thompson-nv-cnd-proper-on-triangular-subgroup` (R2). So the
  route `brin-thompson-nv-a-t-menable-via-triangular-split` has only one independent hole, R1. Every
  obstruction to R2 is an obstruction to R1: in particular R1 implies Brothier's Problem B for
  `Γ = Z` and `Γ = V`, since `C(C,Z) ⋊ V` and `C(C,V) ⋊ V` embed in `T_n`.
- *Distortion stays in R1.* By `brin-thompson-nv-no-cubical-action-proper-mod-triangular`, no
  commensurating action satisfies (2) or (3) (`V^n ≤ T_n` is undistorted). This is consistent: the
  cubical obstruction to the fibre half (`brin-thompson-nv-fibre-elements-are-cubically-elliptic`)
  is now absorbed by the transversal half.
- *What a proof of R1 must do.* The fibre content is no longer an independent input. The
  transversal function, averaged over finitely many shears and permutations, already controls
  `V^n`, the fibre elements and the central direction `1_C` of Problem B.
- *Where the trick does not apply (remark, not load-bearing).* For `K = ker c` or the diagonal
  subgroup `{g : c(g) ∈ Z·(1,...,1)}`, conjugation by any finite set of elements of `nV` keeps
  every element supported in a small enough cube inside the subgroup, so finite automorphic
  intersections of inner conjugates stay infinite. `T_n` also contains small-support fibre
  elements, which is why the intersection first passes through `V^n` by permutations.
