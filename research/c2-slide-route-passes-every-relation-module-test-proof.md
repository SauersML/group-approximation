---
rg: 2
id: c2-slide-route-passes-every-relation-module-test-proof
kind: route
title: The relation-module matrix of every slide group is unitriangular over ZG, Z[H\G] = H(g-2)ZG by an explicit witness, and the w12 coset invariant extends through the transition class in H^2(G;ZG)
target: c2-slide-route-passes-every-relation-module-test
requires:
  - admissible-ab-nonzero-two-cell-base-exists
  - c2-one-relator-lift-presentations-are-obstructed
  - rank-five-degree-one-two-cell-configuration-is-a-core
artifacts:
  - experiments/c2-slide-screen-2026-09-18/pair_invariant.py
  - experiments/c2-slide-screen-2026-09-18/screen.py
---

# Proof

Notation is that of the target. `F_3 = F(x,y,t)`, `K = ⟨⟨w, t⟩⟩ ≤ F_3` is the kernel of
`F_3 → G` (`x, y ↦ x, y`, `t ↦ 1`), and `Φ : ZG → Z[H\G]`, `λ ↦ Hλ`. `Φ` is right
`ZG`-linear, and `Φ(kλ) = ε(k)Φ(λ)` for `k ∈ ZH`. All modules of classes are left modules;
maps between free modules are right multiplications.

## Step 0. τ = 1 (S0)

If `f(z) = z` in `G` under `t ↦ τ ∈ G`, choose a word `τ̂ ∈ F(x,y)` for `τ`, and let `α` be the
automorphism of `F_3` fixing `x, y` with `α(t) = t τ̂`. Then `α^{-1}∘f` is a lift for `t ↦ 1`, and
`α` induces an isomorphism of the two slide groups that fixes `x, y` and carries `t τ̂^{-1}` to
`t`. So `t = τ` in the first slide group iff `t = 1` in the second.

## Step 1. The relation module (S1)

`⟨x,y,t | w, t⟩` is aspherical, since it is the presentation complex of `G` with a free edge and
a cancelling cell. By Lyndon, `K_ab` is free on `[w], [t]`. A slide datum `f` has
`f(z) = Π_z^{-1} φ_0(z)` in `F_3` with `Π_z ∈ ⟨⟨t⟩⟩`, so `[Π_z] = m_z [t]` with `m_z ∈ ZG`.
Write `ω_z = f(z)φ_0(z)^{-1} = Π_z^{-1}`, so `[ω_z] = −m_z[t]`. The Fox chain rule for relation
modules (w12 Step 1) gives

`[f(u_i)] = [φ_0(u_i)] + Σ_z (∂_z u_i) [ω_z]`.

Here `[φ_0(u_0)] = [w]` and `[φ_0(u_1)] = [g w g^{-1}] = g[w]`. So, in the basis `[w], [t]`,

`κ = ( (1, −Σ_z ∂_z u_0 m_z) ; (g, −Σ_z ∂_z u_1 m_z) )`.

With `Q = ((1, 0); (g, −1))`, which satisfies `Q^2 = 1`, the second row of `Qκ` is
`(0, Σ_z (∂_z u_1 − g ∂_z u_0) m_z) = (0, −c·m)`, where `c_z = g ∂_z u_0 − ∂_z u_1` is the
certificate row of `admissible-ab-nonzero-two-cell-base-exists`. So `Qκ` is upper triangular with
diagonal `(1, −c·m)`.

- If `c·m` is a unit `±h`, then `κ` is invertible and `[f(u_0)], [f(u_1)]` is a basis of `K_ab`.
- Conversely, if they form a basis then `c·m` has a two-sided inverse in `ZG`. `G` is locally
  indicable (a one-relator torsion-free group, or directly `F_4 ⋊ Z`), so its units are trivial
  (Higman). Hence `c·m = ±h`.

The words chosen for `Π_z`, the order of its factors, and any insertion of elements of
`⟨⟨w⟩⟩` into `f(z)` that keeps `m_z` fixed do not change `κ`. The certificate `m = d` of
`verify_unimodular.py` has `c·d = 1`.

**Consequences.**
- For `c·m = ±h`, `Γ'' = F_3/⟨⟨f(u_0), f(u_1)⟩⟩` has the relation module of `G`. So
  `Γ'' → G` is an isomorphism iff the kernel `Λ = ⟨⟨t⟩⟩_{Γ''}` is trivial.
- `Λ = K/⟨⟨f(u_0), f(u_1)⟩⟩` is perfect: `Λ/[Λ,Λ] = K_ab/⟨[f(u_0)], [f(u_1)]⟩ = 0`. So no
  homomorphism from `Γ''` to a solvable group has `t ≠ 1`.
- The Magnus-type step of w12 (O4), comparing the relator class with the class of a single
  conjugate, has no analogue here: every relation-module test is passed.

## Step 2. The Φ-test is vacuous as well (S1, remark)

The `|T| = 3` analogue of w12's (O3) asks whether `H ∈ H(g−2)ZG`, i.e. whether
`I_H ZG + (g−2)ZG = ZG`. It holds.

Let `M = ZG / (I_H ZG + (g−2)ZG)` and `v = [1]`. Then `vh = v` for `h ∈ H`, and `vg = 2v`.
- Since `y = d ∈ H`, `vY = v`. So `vX = (vXy)Y = (vg)Y = 2vY = 2v`, and `v = vXx = 2vx`.
- Since `a = XyxYx ∈ H`, `v = va`. Step by step: `vX = 2v`, then `·y` gives `2v`, then `·x`
  gives `2vx = v`, then `·Y` gives `v`, then `·x` gives `vx`. So `v = vx`.
- Hence `v = 2vx = 2v`, so `v = 0` and `M = 0`.

Explicitly, `s = Y(2yxYx − 2xYx − x)` satisfies `H(g − 2)s = H` in `Z[H\G]`. The `X`-part
contributes `2Ha − 2Hx − H = H − 2Hx`, and the `−2Y`-part contributes
`−2(2HxYx − 2HxYx − Hx) = 2Hx`. Only `a, y ∈ H` are used.

So `Z[H\G] = H(g−2)ZG`, and the `Z[H\G]` image cannot distinguish a slide datum from a
realization.

## Step 3. t occurs at least three times in f(u_0) (S2)

Augmenting the `[t]`-column of `κ` gives the `t`-exponent sums. Since
`e_z(u_1) = 2e_z(u_0)` and `ε(g) = 1`, `ε(c·m) = −Σ_z e_z(u_0)ε(m_z) = ±1`. So
`exp_t f(u_0) = ε(c·m) = ±1` and `exp_t f(u_1) = ±2`.

Suppose `t` occurs exactly once in `f(u_0)`, and `Γ'' ≅ G` through `t ↦ 1`. Solving that relator,
`t = T_0` for a word `T_0 ∈ F(x,y)`, and `T_0 = 1` in `G`. Put `f'(z) = f(z)[t := T_0]`. Then `f'` is
a lift over `(x,y)`, `f'(u_0) = 1` in `F(x,y)`, and `G = ⟨x,y | f'(u_1)⟩`.
- By Magnus, `f'(u_1) ∼ w^{±1}`, so `Φ[f'(u_1)] = ±Hh` for some `h`.
- But the chain rule of Step 1, applied over `F(x,y)`, gives
  `[f'(u_1)] − 2[f'(u_0)] = (g − 2) + Σ_z (∂_z u_1 − 2∂_z u_0)[ω'_z]`. Each coefficient lies in
  `ZH` with augmentation `e_z(u_1) − 2e_z(u_0) = 0`, so `Φ[f'(u_1)] − 2Φ[f'(u_0)] = Hg − 2H`.
- Since `[f'(u_0)] = 0`, this gives `Φ[f'(u_1)] = Hg − 2H`, which is not `±Hh` because `g ∉ H`.

This is a contradiction. The same substitution with `f(u_1)` is excluded by parity, since its
`t`-exponent sum is even. So `t` occurs an odd number of times, at least 3, in `f(u_0)`, and an
even number of times, at least 2, in `f(u_1)`.

## Step 4. The w12 invariant for an arbitrary generating pair (S3)

Let `X` be the presentation complex of `⟨x,y | w⟩`, with cellular chains
`ZG →∂_2 ZG^2 → ZG`, `∂_2(1) = (∂_x w, ∂_y w)`. Put `J = ∂_x w·ZG + ∂_y w·ZG`, a right ideal.

**(P1) `H(g−2)J = 0`.** Fox's chain rule applied to `φ_0(u_0) = w` and `φ_0(u_1) = gwg^{-1}` gives,
in `ZG`, `∂_v w = Σ_z (∂_z u_0)∂_v(φ_0 z)` and `g∂_v w = Σ_z (∂_z u_1)∂_v(φ_0 z)`, for `v = x, y`.
(The terms `(1 − gwg^{-1})∂_v g` vanish in `ZG`.) So
`(g−2)∂_v w = Σ_z (∂_z u_1 − 2∂_z u_0)∂_v(φ_0 z)`. Each coefficient lies in `ZH` with augmentation
`e_z(u_1) − 2e_z(u_0) = 0`. So `H(g−2)∂_v w = 0`, and right-linearity gives `H(g−2)J = 0`.
`pair_invariant.py` checks both identities exactly in the normal form of `F_4 ⋊ Z`.

**(P2) The transition class.** Let `(x', y')` be a generating pair of `G` with a one-relator
presentation `G = ⟨x',y' | r'⟩`, and let `X'` be its complex, with ideal `J'`. Both complexes are
aspherical, so there are augmentation-preserving chain maps `X → X' → X`. Let `μ, ν` be their
degree-2 entries.
- A chain homotopy changes `μ` by `∂_x w h_x + ∂_y w h_y ∈ J`. So `μ̄ ∈ ZG/J` is well defined.
- The composite `X → X' → X` is homotopic to the identity, so `1 − μν ∈ J`.
- By (P1), `I(x',y') := H(g−2)μ̄ ∈ Z[H\G]` is well defined.

**(P3) The obstruction for the pair.** Suppose `G = ⟨H, x', y' | z = f(z) (z ∈ Z)⟩` for a
one-relator presentation `⟨Z | r⟩` of `H`. Tietze moves give `G = ⟨x', y' | f(r)⟩`, so we may take
`r' = f(r)`, with `[f(r)] = 1` in `ZG ≅ N'_ab`.
- Consider the two chain maps from `ZG ⊗_H C_*(⟨Z | r⟩)` to `C_*(X̃')` over `H ≤ G`. One is given
  by `f`. The other is a lift `f_0` over `(x,y)` followed by `X → X'`. They are homotopic.
- Their degree-2 entries are `[f(r)] = 1` and `βμ`, where `β = [f_0(r)]`. A homotopy changes a
  degree-2 entry by `Σ_z (∂_z r)h_z`. Each `∂_z r ∈ ZH` has augmentation `0`, because
  `r ∈ [F(Z), F(Z)]` (w12 (O1)). So `Φ` does not see the change.
- Hence `H = Φ(βμ) = Φ(β)μ = ±H(g−2)μ̄`, using w12 (O2) for `Φ(β) = ±H(g − 2)`.

So a relative presentation of shape (O4) over `(x', y')` needs `I(x', y') = ±H` (or `±Hh`, after
conjugating `r'`).
- For a pair Nielsen-equivalent to `(x, y)`, the chain maps come from an automorphism of the free
  group, and `μ̄ = ±h` is a unit. Then `I = ±(Hgh − 2Hh) ≠ ±H`, which recovers w12 (O4).
- For a pair outside that Nielsen class, `μ̄` is some generator of the cyclic right module
  `ZG/J ≅ H^2(G; ZG)` (from `1 − μν ∈ J`).
- Step 2 shows that `H` does lie in the image `H(g−2)ZG`. So (P3) excludes such a pair only
  through the arithmetic of `μ̄` in `H^2(G; ZG)`, not through `Φ` alone.

This reduces the non-Nielsen `|T| = 2` case to one question. Is there a generating pair of `G`
whose transition class `μ̄ ∈ H^2(G;ZG)` satisfies `H(g−2)μ̄ = ±Hh`?

## Step 5. Relators mixing H and T

By `relative-realization-is-relative-efficiency` and the admissibility of (C2)
(`admissible-ab-nonzero-two-cell-base-exists`), the relative chain complex of some shape with
`|R| − |T| = 2` exists at the module level. So no stable-module invariant excludes every
`|T| = 2` shape with mixed relators. As in Step 1, the question there is a relation-gap question,
not a module question. This step only records the reduction; it proves no new statement.
