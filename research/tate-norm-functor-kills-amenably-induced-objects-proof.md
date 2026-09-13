---
rg: 2
id: tate-norm-functor-kills-amenably-induced-objects-proof
kind: route
title: Induced objects reduce to amenable wreath products where weakly contractible objects vanish; K-amenability failure blocks generation
target: tate-norm-functor-kills-amenably-induced-objects
requires: [tate-norm-is-additive-exact-and-gamma-compatible, tate-diagonal-cone-is-weakly-contractible-wreath-object]
artifacts: [research/artifacts/uct-tate-diagonal-wreath-cone-2026-09-13-part3.md]
---

The full derivation is `research/artifacts/uct-tate-diagonal-wreath-cone-2026-09-13-part3.md` §10.

- **Item 1.**
  - Item 5 of the Tate-norm claim gives
    `cone(ε) ⊗ T(Ind_K^Γ B) ≅ Ind_(K≀G)^W(Res_(K≀G) Y ⊗ B^(⊗p))`.
  - Green imprimitivity reduces `Ψ` to `(K≀G) ⋉_r (Res Y ⊗ B^(⊗p))`.
  - `Res_(K≀G) Y` is weakly contractible, since finite subgroups of `K ≀ G` are finite subgroups
    of `W`.
  - `K ≀ G` is amenable, so the object vanishes by Meyer–Nest Thm. 8.5 (arXiv:math/0312292v3).
  - `Ψ` is exact and commutes with countable direct sums, so its kernel is localizing.
- **Item 2.**
  - `λ` is a natural transformation between triangulated, direct-sum preserving functors, so the
    class where it is invertible is localizing.
  - It contains `Ind_K^Γ B` for amenable `K`, where maximal and reduced crossed products agree.
  - If `C` belonged to that class, `λ : C*_max Γ → C*_r Γ` would be a KK-equivalence.
  - For infinite Kazhdan `Γ`, the Kazhdan projection `p` is nonzero in `K_0(C*_max Γ)`, since
    `[triv]_*[p] = 1`, while `λ(p) = 0` (Cuntz's K-amenability argument, recalled).
