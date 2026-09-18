---
rg: 2
id: euclidean-artin-toric-commensurability-proof
kind: route
title: Divide the affine Weyl arrangement complement by the coroot lattice, then by W and by the larger lattice, and move B_A across finite-index inclusions
target: euclidean-artin-toric-commensurability
requires:
  - boone-higman-type-a-class-closed-under-finite-extensions
  - fiber-type-toric-arrangement-groups-lie-in-the-pbh-class
---

Notation as in the target.

1. **The Artin group.** `W̃` acts freely and properly discontinuously on the
   connected complex manifold `M`, and `π_1(M/W̃) ≅ A(X̃_n)`.
   - This is van der Lek's theorem for Coxeter groups acting on their Tits cone, in
     Nguyễn Viết Dũng's form for affine Weyl groups (Topology 22 (1983) 425–435). Both
     are cited, not re-read.
   - The same import is used, for type B̃_n, in
     `b-tilde-artin-complement-fibres-over-configuration-space` (via Li--Roushon).
   - Freeness is the Steinberg argument of `b-tilde-artin-pbh-via-free-fibre-kernel-proof`,
     step 1. It works verbatim for any affine Weyl group: a fixed point of
     `w ≠ 1` lies on some `{α = k}`.
2. **Lattice quotients.** `L` acts on `M` by translations, freely.
   - Because `α(L) ⊆ Z`, the family `{α = k}_(k ∈ Z)` is `L`-invariant. The
     exponential `V_C -> T_L`, `u ↦ [u]`, sends `∪_k {α = k}` onto `{t^α = 1}`, where
     `t^α = e^(2πi α(u))` is a well-defined character of `T_L`, since `α ∈ L*`.
   - The preimage of `{t^α = 1}` is exactly `∪_k {α = k}`. So `M/L ≅ M_L`.
3. **Indices.** The coverings `M/Q^∨ -> M/W̃` and `M/Q^∨ -> M/L` have degrees
   `|W̃ / Q^∨| = |W|` and `[L : Q^∨]`. All three spaces are connected, so
   `π_1(M/Q^∨)` has those indices in `A(X̃_n)` and in `π_1(M_L)`.
4. **B_A.** `B_A` is closed under subgroups and finite-index overgroups
   (`boone-higman-type-a-class-closed-under-finite-extensions`, parts 1–2). So each of
   `A(X̃_n)`, `π_1(M/Q^∨)` and `π_1(M_L)` lies in `B_A` if and only if the others do.
5. **C̃_n.**
   - The roots of C_n are `±2e_i` and `±e_i ± e_j`. Their coroots `±e_i` and
     `±e_i ± e_j` span `Q^∨ = Z^n`.
   - With `L = Z^n` and `v = e^(2πiu)`, `M_L = {v_i^2 ≠ 1, v_i ≠ v_j^(±1)}`. This is
     fiber-type, by the C_n example in
     `fiber-type-toric-arrangement-groups-lie-in-the-pbh-class-proof`. So
     `A(C̃_n) ∈ B_A`.
   - (For `n = 1`, `M_L = C^× − {±1}` and `A(C̃_1)` is free of rank 2.) ∎
