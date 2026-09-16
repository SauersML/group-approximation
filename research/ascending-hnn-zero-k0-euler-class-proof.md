---
rg: 2
id: ascending-hnn-zero-k0-euler-class-proof
kind: route
title: "Mapping cone of a lift of the Bass--Serre boundary map: the induced resolution appears twice with opposite signs"
target: ascending-hnn-of-fp-group-has-zero-k0-euler-class
requires: [fp-type-fp-group-is-type-f-iff-wall-class-vanishes]
artifacts:
  - research/artifacts/zaremsky-1-21-fibering-and-retracts-2026-09-16.md
---

Textbook facts used:

- (S2), (S3), (S4) as listed in
  `g-times-z-type-f-iff-g-f-infinity-with-finite-cd-proof`;
- the Bass–Serre tree of an HNN extension (Serre, *Trees*);
- the comparison theorem for projective complexes.

Proof:

1. **The tree.** The Bass–Serre tree `T` of `G = B*_φ` has vertex set `G/B`
   and edge set `G/B`, and the edge `gB` joins `gB` to `gt⁻¹B`. This is well
   defined: for `b ∈ B`, `gbt⁻¹B = gt⁻¹φ(b)B = gt⁻¹B`. Since `T` is a tree,
   the cellular chain complex gives an exact sequence of `ZG`-modules

   ```text
   0 → Z[G/B] --∂--> Z[G/B] --ε--> Z → 0,   ∂(gB) = gt⁻¹B − gB.
   ```

2. **Induced resolution.** Let `P_* → Z` be a finite resolution of length
   `n = cd B` by f.g. projective `ZB`-modules. `ZG` is a free right
   `ZB`-module on coset representatives, so `ind = ZG ⊗_{ZB} −` is exact.
   Hence `ind P_*` is a finite resolution of `ind Z = Z[G/B]` by f.g.
   projective `ZG`-modules.
3. **Lift.** By the comparison theorem, `∂` lifts to a chain map
   `f: ind P_* → ind P_*`.
4. **Cone.** Let `C = Cone(f)`, with `C_k = ind P_{k−1} ⊕ ind P_k` and
   `d(x,y) = (−dx, f(x) + dy)`. The long exact sequence of
   `0 → ind P_* → C_* → ind P_{*−1} → 0` has connecting map `f_* = ∂` on
   `H_0`. Since `H_*(ind P) = Z[G/B]` in degree 0 and vanishes elsewhere:
   - `H_k(C) = 0` for `k ≥ 2`;
   - `H_1(C) = ker ∂ = 0`;
   - `H_0(C) = coker ∂ ≅ Z` via `ε`.

   So `C_* → Z` is a resolution of length `≤ n+1` by f.g. projective
   `ZG`-modules. Hence `G` is FP and `cd G ≤ cd B + 1`.
5. **Euler class.** In `K_0(ZG)`,
   `Σ_k (−1)^k [C_k] = Σ_k (−1)^k [ind P_{k−1}] + Σ_k (−1)^k [ind P_k] = 0`,
   since the first sum is minus the second. By the generalized Schanuel lemma
   this class is independent of the resolution. So `χ_G = 0`. Its images give
   `σ(G) = 0 ∈ K̃_0(ZG)` and `e(G) = ε_*(χ_G) = 0`.
6. **FL.** The class lies in `Z·[ZG]`, so (S3) turns `C_*` into a finite free
   resolution, and `G` is of type FL.
7. **Type F.** If `G` is finitely presented, it is of type F by
   `fp-type-fp-group-is-type-f-iff-wall-class-vanishes`, since it is FP with
   `σ(G) = 0`. Conversely, type F implies finitely presented. If `B = ⟨X | R⟩`
   is finite, then `⟨X, t | R, t x t⁻¹ = φ(x) (x ∈ X)⟩` is a finite
   presentation of `G`.
8. **Corollary.** If `χ: G → Z` is onto with kernel `N` of type FP, pick
   `χ(t) = 1`. Then `G = ⟨N, t | t x t⁻¹ = α(x)⟩ = N*_α` with `α` conjugation
   by `t`, an automorphism of `N`, and steps 1–7 apply. QED

The general sum formula for trees with FP stabilizers
(`χ_G = Σ_v ind χ_{G_v} − Σ_e ind χ_{G_e}`) and its sanity checks are in the
artifact, §1.
