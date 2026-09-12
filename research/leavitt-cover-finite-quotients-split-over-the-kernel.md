---
rg: 2
id: leavitt-cover-finite-quotients-split-over-the-kernel
kind: claim
title: Finite quotients of the hyperbolic Leavitt cover split as the kernel image times the Leavitt unit group
distinct_from:
  hyperbolic-kazhdan-cover-of-leavitt-unit-group: that constructs the cover and records that every finite image of G is the image of N; this determines the finite quotients exactly, embeds the Leavitt unit group into Out(N), and identifies the profinite completion of G with a completion of N.
  kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient: that is the sofic-approximation statement that G preserves the expander blocks of N; this is the exact algebraic statement for finite quotients.
  rips-kernel-without-finite-quotients: that asks for a Rips kernel with no finite quotients; this describes all finite quotients of one Rips extension with Kazhdan kernel over a simple acyclic quotient.
artifacts:
  - research/artifacts/hyperbolic-leavitt-cover-relative-defect-2026-09-12.md
---

**ESTABLISHED.** Let `1 -> N -> G -> R^x -> 1` be the hyperbolic Kazhdan cover
of `hyperbolic-kazhdan-cover-of-leavitt-unit-group`, with `G` torsion-free.

1. **Outer action.**
   - `C_G(N) = 1`, so conjugation embeds `G` into `Aut(N)` and `R^x` into
     `Out(N)`.
   - In particular `Out(N)` is not residually finite.
2. **Splitting.** Let `L <= N` be normal in `G` and of finite index in `N`.
   Then

   ```text
   G/L  =  N/L  x  K_L,     K_L ~= R^x,
   ```

   an internal direct product, and the complement `K_L` is unique.
3. **All finite quotients.**
   - `K -> K cap N` is a bijection from normal subgroups of finite index in `G`
     to the subgroups `L` of item 2, with `G/K ~= N/L`.
   - Hence the profinite completion of `G` is the completion `N^_G` of `N` with
     respect to these `L`.
   - Every normal subgroup of finite index in `N` is `G`-invariant (observed by
     lane `hyperbolic-rf`). So `N^_G` is the full profinite completion `N^`,
     and `G^ ~= N^`.
   - `G` is residually finite exactly when the homomorphism `G -> N^_G`, sending
     `g` to its `N/L`-coordinates, is injective.

Derivation: `leavitt-cover-finite-quotients-split-proof`.

**What it says about the hyperbolic questions.** Every element of `G \ N`
acts on `N` as an outer automorphism, which becomes inner, and canonically
split, on every finite quotient of `N` that `G` preserves. So residual
finiteness of `G` means every such element is detected by the canonical inner
realizer of its action on some finite quotient of `N`.

In every finite model, the relative defect of
`hyperbolic-kazhdan-group-has-infranormal-kazhdan-subgroup` collapses into the
image of `N`, since `K_L` centralizes `N/L`. So a proof of
`sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels` for this host would
make `G` non-residually-finite. The finite-quotient side cannot refute that
criterion unless it separates `G`.
