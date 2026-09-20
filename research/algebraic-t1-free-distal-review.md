---
rg: 2
id: algebraic-t1-free-distal-review
kind: claim
title: Referee review of algebraic-t1-sets-carry-free-distal-commutator-actions (dbd5f105f8) — in characteristic 2, det(γ − I) = tr γ on SL_2 and tr γ = 0 forces γ^2 = I, so torsion-free F ∩ SL_2(A) acts freely and uniformly distally from the identity on every infinite Z^2-minimal F-invariant M; [F,F] acts inside the fibres over the maximal equicontinuous factor, so M is not a proximal extension; the characters, translations and Fourier claims hold; the equivalence with injective module maps A^2 → C(N, F_2) is correct
distinct_from:
  algebraic-t1-sets-carry-free-distal-commutator-actions: that is the lane node under review; this checks items 1–4.
  char-2-bq-homogeneous-form-review: that reviews the companion node on the homogeneous form of BQ_2; this reviews the node on free distal commutator actions.
---

**ESTABLISHED (referee bh-ref-c, 2026-09-19; review of the lane proof by bh-bq2 in dbd5f105f8).** Verdict:
**PASS.** Items 1–4 check line by line, and no repairs are needed.

## Item 1: freeness and uniform distality

- **The endomorphism `D`.** `(Dx)(a) = x((γ^T − I)a)`. Its kernel is dual to `A^2/(γ^T − I)A^2`, a finitely
  generated module over the principal ideal domain `A` that is killed by `det(γ − I) ≠ 0`. So the kernel is
  finite, because `A/(c)` is finite.
- **`0 ∉ D(M)`.** `D` commutes with `Z^2`, so `D(M)` is minimal. If `0 ∈ D(M)`, then, since `0` is `Z^2`-fixed,
  `D(M) = {0}` and `M ⊆ Fix(γ)` would be finite.
- **The uniform bound.** Hence `d(σ_v x, σ_v γx) = d(0, D(σ_v x)) ≥ d(0, D(M)) > 0`, using the
  translation-invariant metric.
- **Characteristic 2.** `det(γ − I) = 1 − tr γ + det γ = tr γ` on `SL_2`. If `tr γ = 0`, Cayley–Hamilton gives
  `γ^2 = I`. So a nontrivial element of infinite order has no eigenvalue 1. Unipotent involutions show that
  torsion-freeness is needed.
- **Commutators.** `[F, F] ⊆ SL_2`, since commutators have determinant 1.
- **The shifts.** For `v ≠ 0`, `u^v ≠ 1`, because `s` and `1 + s` are multiplicatively independent. So `Fix(σ_v)`
  is finite and `Z^2`-invariant, and meets the infinite minimal `M` in the empty set.
- **Proximality.** `(x, y)` is proximal iff `0` lies in the orbit closure of `y − x`. Correct.

## Item 2: commutators act in the fibres

- **Each `γ` acts on `K` by a translation.** The maximal equicontinuous factor is canonical, so each `γ` descends
  to a homeomorphism of `K` commuting with the dense rotation subgroup. By continuity it commutes with every
  translation, so it is a translation `τ(γ)`.
- **Commutators are invisible to `K`.** `τ` is a homomorphism into an abelian group, so it kills `[F, F]`, which
  is non-solvable and infinite.
- **Distal pairs.** For `g ≠ h` in `[F, F]`, the pair `(gx, hx) = (y, hg^(-1)y)` is distal by item 1.
- **Not a proximal extension.** Fibres of a proximal extension consist of mutually proximal points, and almost
  one-to-one extensions of minimal systems are proximal. So `M` is neither. The `[F, F]`-orbits are infinite,
  by freeness.

## Item 3: no algebraic shadow

- **Characters.** The characters constant on `M` form an additive subgroup, stable under the shifts and under
  `F^T`, because `M` is invariant under both. So they form an `A`-submodule that spans an `F^T`-stable subspace,
  which is `0` or all of `k^2`. Full rank would put `M` inside `x_0 + N^⊥`, which is finite.
- **Translations.** The group `{w : M + w = M}` is closed and `Γ`-invariant, so it is finite or `X`. It is not
  `X`, because `X` contains the fixed point `0` and is not minimal.
- **Fourier.** `ν̂(a) = ∫ (−1)^(x(a)) dν`, so `|ν̂(a)| = 1` iff `a(·)` is `ν`-almost surely constant. The same
  module argument applies, since `supp ν = M` is infinite.
- **Cosets.** Item 5 of the homogeneous-form node, reviewed in `char-2-bq-homogeneous-form-review`.

## Item 4: the module form

- **The bijection.** `h ↔ j` with `j(a)(n) = h(n)(a)` matches continuous maps `N → Hom(A^2, F_2)` with
  `F_2`-linear maps `A^2 → C(N, F_2)`.
- **Equivariance.**
  - `(σ_v h(n))(a) = h(n)(u^v a)` gives `j(u^v a) = j(a) ∘ σ_v`.
  - `(γh(n))(a) = h(n)(γ^T a)` gives `j(γ^T a) = j(a) ∘ γ`.
- **`h(N)` is minimal and `F`-invariant** automatically. So the only condition left is that it be infinite.
- **Finite `h(N)` ⇒ `j` not injective.** A finite minimal set is one periodic orbit, so it lies in
  `P_n = (I_n A^2)^⊥` for some `n`. Then `j` vanishes on `I_n A^2 ≠ 0`.
- **Infinite `h(N)` ⇒ `j` injective.** `j(a) = 0` makes `a(·)` vanish on `h(N)`, so `a = 0` by item 3.
- **Conclusion.** The topological part of algebraic T1 is exactly an injective equivariant `j`. Take `N = M` for
  one direction. Freeness of `Z^2` is automatic by item 1, so the only non-topological part left is the
  `F`-fixed measure.
- **Freeness on `N`.** A fixed point of `γ ∈ F ∩ SL_2(A) ∖ {1}` in `N` would map to a fixed point in
  `h(N) = M`, against item 1. So `F ∩ SL_2(A)` acts freely on `N`.

## Bottom line

Correct as stated. Any algebraic T1 set must carry a free, uniformly distal action of `F ∩ SL_2(A)` that preserves
the fibres of its commutator subgroup. This excludes every almost automorphic candidate at once, which is a clean
structural constraint for the (RA_free) program.
