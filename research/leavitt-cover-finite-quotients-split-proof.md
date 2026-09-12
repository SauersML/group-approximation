---
rg: 2
id: leavitt-cover-finite-quotients-split-proof
kind: route
title: Kill the outer action by simplicity and the central extension by acyclicity
target: leavitt-cover-finite-quotients-split-over-the-kernel
requires:
  - hyperbolic-kazhdan-cover-of-leavitt-unit-group
  - hyperbolic-nonelementary-centralizer-finite
  - binary-leavitt-unit-group-is-simple
  - binary-leavitt-unit-group-integrally-acyclic
artifacts:
  - research/artifacts/hyperbolic-leavitt-cover-relative-defect-2026-09-12.md
---

Write `Q = R^x`. By the cover claim, `G` is torsion-free and hyperbolic, `N` is
infinite Kazhdan, and every finite image of `G` equals the image of `N`.

**Item 1.**
- `N` is infinite Kazhdan, hence not virtually cyclic, hence non-elementary.
  So `C_G(N)` is finite (`hyperbolic-nonelementary-centralizer-finite`), and
  therefore trivial because `G` is torsion-free.
- If `g` acts on `N` as conjugation by `n in N`, then `n^-1 g in C_G(N) = 1`,
  so `g in N`. Hence `Q` embeds in `Out(N)`.
- `Q` is infinite and simple, so it is not residually finite. Subgroups of
  residually finite groups are residually finite, so `Out(N)` is not.

**Item 2.** Put `F = N/L`, a finite normal subgroup of `G/L`.
1. **Outer action is trivial.** Conjugation gives `Q = (G/L)/F -> Out(F)`. Its
   kernel has finite index in the infinite simple group `Q`, so it is all of
   `Q`.
2. **Centralizer.** Let `C = C_(G/L)(F)`, which is normal. Every element acts
   on `F` as an inner automorphism, so `F C = G/L`. Also `C cap F = Z(F)`, and
   `C / Z(F) ~= (G/L)/F = Q`. So `C` is a central extension of `Q` by `Z(F)`.
3. **Splitting.** By `binary-leavitt-unit-group-integrally-acyclic`,
   `H^2(Q; Z(F)) = 0`, so `C ~= Z(F) x Q`.
4. **Complement.** Put `K_L = [C, C]`. It is `1 x Q` because `Q` is perfect, and
   it is characteristic in `C`, hence normal in `G/L`.
   - `K_L cap F <= K_L cap Z(F) = 1`.
   - `F K_L` contains `Z(F) K_L = C`, so `F K_L = G/L`.
   - Two normal subgroups with trivial intersection that generate give an
     internal direct product.
5. **Uniqueness.** Any normal complement to `F` centralizes `F`, so it lies in
   `C`. It is isomorphic to the perfect group `Q`, so it lies in `[C, C] = K_L`.
   Both map isomorphically onto `Q`, so they are equal.

**Item 3.**
- Let `K` be normal of finite index in `G`. Since `G = N K`, put
  `L = K cap N`. Then `G/L = N/L x K/L`. By uniqueness `K/L = K_L`, and
  `G/K ~= N/L`.
- Conversely, `L` gives the kernel `K` = preimage of `K_L`, with `K cap N = L`.
  These maps are inverse to each other.
- Finite quotients of `G` are therefore the groups `N/L` with the projections
  `G -> N/L`. The inverse limit is `N^_G`, and injectivity of
  `G -> N^_G` is residual finiteness by definition.
- **Every finite-index normal `L` of `N` qualifies.** `N` is finitely
  generated, so for each `k` it has finitely many normal subgroups of index `k`.
  `G` permutes them by conjugation, and `N` acts trivially, so the action
  factors through `Q`. A permutation action of `Q` on a finite set is trivial,
  because `Q` has no nontrivial finite quotient. So `N^_G = N^`. ∎
