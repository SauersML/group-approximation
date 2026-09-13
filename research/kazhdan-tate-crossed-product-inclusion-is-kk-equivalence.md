---
rg: 2
id: kazhdan-tate-crossed-product-inclusion-is-kk-equivalence
kind: claim
title: For torsion-free Kazhdan hyperbolic Γ, the inclusion 1_T ⋊_r (ΔΓ × Z/p) → 1_T ⋊_r (Γ ≀ Z/p) is a KK-equivalence
distinct_from:
  kazhdan-group-algebra-tate-diagonal-is-kkg-equivalence: that asks for a KK^G-equivalence of the Tate diagonal; this is its non-equivariant half, the crossed-product statement, which together with phantom-freeness is equivalent to it.
  tate-diagonal-cone-is-weakly-contractible-wreath-object: that proves the reformulation W ⋉_r Y and K-invisibility; this asks for KK-vanishing of W ⋉_r Y.
---

**OPEN.**
- **Setting.** `p` is prime, `G = Z/p`, and `Γ` is a torsion-free infinite hyperbolic group with
  property (T), for instance a torsion-free uniform lattice in `Sp(n,1)` with `n ≥ 2`.
  - `W = Γ ≀ G` and `H = ΔΓ × <σ>`.
  - `1_T` is the Tate object, with `W` and `H` acting through `G`.
- **Question.** Is the subgroup inclusion `1_T ⋊_r H → 1_T ⋊_r W` a KK-equivalence, with no
  equivariance required?
- **Equivalent form.** `W ⋉_r Y ≃_KK 0` for
  `Y = cone([ℓ²(W/H)]) ⊗ q^*1_T` (`tate-diagonal-cone-is-weakly-contractible-wreath-object`).
- **What is known.**
  - The inclusion is an isomorphism on K-theory with every coefficient algebra, by Baum–Connes with
    coefficients for `W`.
  - `Y` vanishes on every finite, amenable, `Γ^p`-contained and `H`-conjugate-contained subgroup
    (`wreath-tate-cone-vanishes-on-centralizer-and-amenables`).

## Attempts

- **K-theory with coefficients (passes, dies as a proof).** K-invisibility is proved. Promoting it
  to KK-vanishing fails on the `(1 − γ_W)`-part, which is where `Y` lives entirely.
- **Generation (dies at (T)).** It would suffice that `q^*1_T` is built from cells induced from the
  subgroups on which `Y` vanishes. `W` has property (FA), so tree resolutions degenerate, and no other
  resolution is known.
- **Maximal crossed products (dies).** The Kazhdan projection splits off `1_T ⋊ G`, and the rest is
  the `J`-part of `C*_max Γ`, with no integer invariant.
  See `research/artifacts/uct-tate-diagonal-wreath-cone-2026-09-13-part2.md` §7(f1).
- **Banach KK (dies).** Lafforgue's `γ = 1` in Banach KK controls only K-theory of the crossed
  product.
