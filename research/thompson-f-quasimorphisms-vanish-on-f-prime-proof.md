---
rg: 2
id: thompson-f-quasimorphisms-vanish-on-f-prime-proof
kind: route
title: Pushing a commutator product along disjoint translates bounds n times its quasimorphism value
target: thompson-f-quasimorphisms-vanish-on-f-prime
requires:
  - thompson-f-has-no-free-subgroups
artifacts:
  - research/artifacts/thompson-f-qi-h2-busemann-reduction-2026-09-16.md
---

The full argument is Part 1 of the artifact. It is summarised here with every step named.

Imported facts.
- (S) Dudko–Medynets, *Finite factor representations of Higman–Thompson groups*,
  arXiv:1212.1230v2, p. 10. The PDF was re-fetched and its text extracted on 2026-09-16. Verbatim,
  up to extraction spacing: "Observe that the commutator subgroup of F_(n,r) is a simple group and
  the abelianization of F_(n,r) is isomorphic to Z^n [1, Section 4]." Here `F = F_(2,1)`, and their
  [1] is K. Brown, *Finiteness properties of groups*, J. Pure Appl. Algebra 44 (1987).
- (NF) `thompson-f-has-no-free-subgroups`: `F` is not elementary amenable.

Let `D` be the defect of a homogeneous quasimorphism `β: F → R`.

**Step 0: `F'` is perfect.** If `F'` were abelian, `F` would be metabelian, hence elementary
amenable, contradicting (NF). By (S), the normal subgroup `[F',F']` of `F'` is `1` or `F'`. It is not
`1`, so `[F',F'] = F'`.

**Step 1: elements of `F'` have compact support in `(0,1)`.** Near `0` each `f ∈ F` is `t ↦ 2^{a_f} t`,
and near `1` it is `t ↦ 1 − 2^{c_f}(1 − t)`. The map `f ↦ (a_f, c_f)` is a homomorphism to `Z^2`, so
it kills `F'`.

**Step 2: a pushing element.** `h(t) = 2t` on `[0,1/4]`, `t + 1/4` on `[1/4,1/2]`, `t/2 + 1/2` on
`[1/2,1]` lies in `F` and has `h(t) > t` on `(0,1)`. So `h^n(s) → 1` for every `s ∈ (0,1)`: the
increasing bounded sequence converges to a fixed point `≥ s`, and the only such fixed point is `1`.

**Step 3: quasimorphism facts.**
- (Q1) `β(f g f^{-1}) = β(g)`. The difference is at most `2D`; apply this to `g^n` and divide by `n`.
- (Q2) If `ab = ba`, then `β(ab) = β(a) + β(b)`. Apply the defect bound to `(ab)^n = a^n b^n`.
- (Q3) `|β([a,b])| ≤ D`, since `β(a b a^{-1}) + β(b^{-1}) = 0` by (Q1).
- (Q4) `|β(c_1 ⋯ c_m)| ≤ Σ|β(c_i)| + (m − 1)D`.

**Step 4: the swindle.**
- Let `g ∈ F'`. By Step 0, `g = Π_{i=1}^m [x_i, y_i]` with `x_i, y_i ∈ F'`. By Step 1, all their
  supports lie in some `U = [u_0, u_1] ⊂ (0,1)`. Put `Γ = {f ∈ F : supp f ⊆ U}`, which contains `g`.
- Choose `M` with `h^M(u_0) > u_1`. The intervals `U_k = h^{Mk}(U)` are pairwise disjoint: for
  `k < k'`, `min U_{k'} = h^{Mk}(h^{M(k'−k)}(u_0)) > h^{Mk}(u_1) = max U_k`. The inequality holds
  because `h^{M(k'−k)}(u_0) ≥ h^M(u_0) > u_1`, since `h(t) ≥ t`, and `h^{Mk}` is increasing.
- `τ_k(f) = h^{Mk} f h^{−Mk}` has support in `U_k` when `f ∈ Γ`.
- Homeomorphisms with disjoint supports commute. If `t ∈ supp f`, then `f(t) ∈ supp f`, so the other
  map fixes both `t` and `f(t)`.
- Hence `Φ_n(f_0, …, f_{n−1}) = τ_0(f_0) ⋯ τ_{n−1}(f_{n−1})` is a homomorphism `Γ^n → F`.
- Applying `Φ_n` to the diagonal identity `(g, …, g) = Π_i [(x_i, …, x_i), (y_i, …, y_i)]` shows that
  `P_n := τ_0(g) ⋯ τ_{n−1}(g)` is a product of `m` commutators.
- The factors of `P_n` commute pairwise, and each has value `β(g)` by (Q1). So (Q2) gives
  `β(P_n) = nβ(g)`.
- (Q3) and (Q4) give `|β(P_n)| ≤ (2m − 1)D`.
- So `n|β(g)| ≤ (2m − 1)D` for all `n ≥ 1`, and `β(g) = 0`. ∎

Consequence.
- `β` factors through `F/F'`. For `g ∈ F` and `k ∈ F'` we have `(gk)^n ∈ g^n F'`, so
  `n|β(gk) − β(g)| = |β((gk)^n) − β(g^n)| ≤ D + |β(k')| = D`, where `k' = g^{-n}(gk)^n ∈ F'`.
- The induced function on the abelian group `F/F'` is additive by (Q2), so `β` is a homomorphism.
