---
rg: 2
id: kazhdan-relations-coamenable-subrelations-locally-kazhdan-proof
kind: route
title: Invariant section maximizers, reductions, choice functions and induced cnd functions, then the (T)/(H) exclusion
target: kazhdan-relations-coamenable-subrelations-locally-kazhdan
requires:
  - kazhdan-groupoid-cnd-criterion-and-t-h-exclusion
artifacts:
  - research/artifacts/kazhdan-relation-coamenability-collapse-2026-09-17.md
---

Complete proofs are in artifact Sections 3--5. The only imports are those of
`kazhdan-groupoid-cnd-criterion-and-t-h-exclusion`, plus Feldman--Moore generation.

1. **Local finite index (Theorem A).**
   - Property (T) turns almost invariant unit sections of `lambda_(R/S)` into an invariant unit section `xi`, which
     is constant on `R`-classes.
   - The classes where `|xi(x)(.)|` attains its maximum form a finite set of constant size `m`, by ergodicity.
     `Y = {x : [x]_S is maximizing}` is `S`-invariant and positive, and `R|_Y` has exact index `m` over `S|_Y`.
   - Among positive `S`-invariant subsets `A` of `Y`, the per-class count `k_A` is a constant. A minimizer makes
     `S|_A` ergodic with index `k_A`.
2. **Reductions keep (T) (Lemma R).**
   - Extend a cnd `psi_Y` on `R|_Y` to `R` through `p(x) = g_(k(x)) x`, the first Feldman--Moore translate into `Y`.
     It stays cnd by merging coefficients.
   - (T) of `R` bounds it on some `R|_E`. On the piece where `k(x)` is constant, translating by `g_k` bounds `psi_Y`
     on a positive piece of `Y`.
   - Theorem 5.22 (ii)=>(i).
3. **Choice functions (Lemma C).**
   - `S` is ergodic of exact index `k` in the ergodic `T`. The skew relation on `Y x {1..k}`, "same `S`-class
     label", is p.m.p. and ergodic, and `Y x {1}` meets every class.
   - The equal-measure exhaustion (Lemma E) gives `phi_i in [T]` with `[x]_T = ⊔ [phi_i x]_S`.
   - Section 6.2 shows that ergodicity of `S` is needed.
4. **Induced cnd (Lemma I).** `psi_T(x,y) = sum_i psi_S(phi_i x, phi_(tau(i)) y)` is cnd on `T`: class by class it
   is a sum of `k` cnd kernels. It dominates `psi_S` on `S`.
5. **Locally Kazhdan (Theorem A').** `R|_A` has (T) by Lemma R. So `psi_T` is bounded on some `R|_E`, hence
   `psi_S <= psi_T` is bounded on `S|_E`. Theorem 5.22 (ii)=>(i) applies to the ergodic `S|_A`.
6. **Exclusion (Theorem B).**
   - A proper cnd on `S` restricts to one on the `S`-invariant `A`, so `S|_A` has (H) (Thm 6.5).
   - `S|_A` is ergodic, diffuse and has (T), contradicting Thm 9.2.
   - Treeable subrelations are covered by Ueda's Thm 8.4.
7. **Kazhdan groups (Corollary K).** `X ⋊ G` has (T) (AD11 Cor 9.4 proof) and Thm 5.18 passes it to `R_G`. A free
   action of an infinite group is diffuse.
